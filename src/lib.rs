#![no_std]

use core::cmp::{Ord, Ordering, PartialOrd};
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;

mod group;
pub use group::{array_group, group, ArrayFieldGroup, FieldGroup};

// This is a hack! It's not meant to be used by users, and may be removed without warning if a
// better method to do this appears!
// It has to be public to be used by the macros. Theoretically it could be embedded in the macros,
// but I don't want to create a trait and a type for every macro invocation, I want it to be as
// cheap as possible for better compile times.
#[doc(hidden)]
pub trait AmbiguousIfDeferIsImpl<A> {
    fn some_item(&self) {}
}

impl<T: ?Sized> AmbiguousIfDeferIsImpl<()> for *const T {}
impl<T: ?Sized + core::ops::Deref> AmbiguousIfDeferIsImpl<u8> for *const T {}

/// This creates a [`Field`] to a field of a type. The type cannot implement [`Deref`](core::ops::Deref), because deref can run arbitrary
/// code, which would mean that the method this library uses to reference fields isn't guaranteed to be correct.
///
/// It also supports fields of fields.
///
/// # Examples
/// ```
/// use field_ref::field;
///
/// struct Struct(u32, u32);
///
/// let a = field!(Struct=>0);
/// let b = field!(Struct=>1);
/// assert_ne!(a, b);
///
/// let mut s = Struct(1, 2);
///
/// a.set(&mut s, 4);
/// assert_eq!(s.0, 4);
/// ```
#[macro_export]
macro_rules! field {
    ($on:ty => $field:tt $(.$fields:tt)*) => {{
        let temp = core::mem::MaybeUninit::<$on>::uninit();
        let ptr = temp.as_ptr();
        <_ as $crate::AmbiguousIfDeferIsImpl<_>>::some_item(&ptr); // Your type probably implements 'Defer'. It's not allowed to

        unsafe {
            let addr = core::ptr::addr_of!((*temp.as_ptr()).$field);
            $(
                <_ as $crate::AmbiguousIfDeferIsImpl<_>>::some_item(&addr); // Your type probably implements 'Defer'. It's not allowed to
                let addr = core::ptr::addr_of!((*addr).$fields);
            )*
            // Because none of the types in the chain implements deref this is safe to do!
            $crate::Field::from_pointers(ptr, addr)
        }
    }};
}

/// A very lightweight reference to a struct field.
///
/// It's guaranteed to be the exact same representation as a [`usize`]
#[repr(C)]
pub struct Field<On, To> {
    // Invariants:
    // * This has to be a valid offset from the start of an 'On' struct that produces the
    // field. It's in bytes.
    // * Fields cannot overlap. This means we can't do tricks like [T; 3] having fields with type [T; 2], even though that's
    // theoretically possible, as I think it's more useful to be able to partially borrow the
    // types.
    offset: usize,
    _phantom: PhantomData<(On, To)>,
}

impl<On, To> Field<On, To> {
    /// Creates a [`Field`] from two pointers. Have a look at the [`field`] macro if you
    /// want a safe way to create this struct.
    ///
    /// # Panics
    /// * If the field and on pointers are not aligned
    ///
    /// # Safety
    /// * The offset between field and on has to be valid to pass to `from_offset`
    pub unsafe fn from_pointers(on: *const On, field: *const To) -> Self {
        assert_eq!(
            (field as usize - on as usize) % core::mem::align_of::<To>(),
            0,
            "Cannot create a 'Field' to an unaligned field"
        );
        Self::from_offset(field as usize - on as usize)
    }

    /// Creates a [`Field`] from just an offset. Have a look at the [`field`] macro if you
    /// want a safe way to create this struct.
    ///
    /// # Safety
    /// * When having any reference to a `&On`, the offset added to that pointer has to be a valid `&Field`, including valid alignment.
    pub unsafe fn from_offset(offset: usize) -> Self {
        Self {
            offset,
            _phantom: PhantomData,
        }
    }

    /// Offsets a raw pointer to the field.
    ///
    /// # Safety
    /// * There has to be an allocated object at least the size of the `On` type.
    pub unsafe fn offset_ptr(self, raw: *const On) -> *const To {
        raw.cast::<u8>().add(self.offset).cast::<To>()
    }

    /// Offsets a mutable raw pointer to the field.
    ///
    /// # Safety
    /// * There has to be an allocated object at least the size of the `On` type.
    pub unsafe fn offset_mut_ptr(self, raw: *mut On) -> *mut To {
        raw.cast::<u8>().add(self.offset).cast::<To>()
    }

    /// Reads a field from a type.
    pub fn get(self, on: &On) -> &To {
        // Safety
        // * This is safe because of the invariant
        unsafe { &*(on as *const On).cast::<u8>().add(self.offset).cast::<To>() }
    }

    /// Reads a field from a type mutably.
    pub fn get_mut(self, on: &mut On) -> &mut To {
        // Safety
        // * This is safe because of the invariant
        unsafe { &mut *(on as *mut On).cast::<u8>().add(self.offset).cast::<To>() }
    }

    /// Sets the value of a field
    pub fn set(self, on: &mut On, new: To) {
        *self.get_mut(on) = new;
    }

    /// Replaces the value of a field, and returns the old value
    pub fn replace(self, on: &mut On, new: To) -> To {
        core::mem::replace(self.get_mut(on), new)
    }

    /// Reintreprets this field as another type. More controlled than transmuting the
    /// entire [`Field`] struct, because it only changes one generic parameter.
    ///
    /// # Safety
    /// * If there is a valid `To` instance, the memory layout has to guarantee that there is
    /// also a valid `T` instance at that same location. Note that this still allows for `T` to
    /// be a smaller value than `To`, for example, casting from `u64` to `u32` would be fine.
    pub unsafe fn cast<T>(self) -> Field<On, T> {
        Field {
            offset: self.offset,
            _phantom: PhantomData,
        }
    }

    /// Takes a field of a field
    ///
    /// # Examples
    /// ```
    /// use field_ref::field;
    ///
    /// struct BStruct(u32);
    /// struct AStruct(BStruct);
    ///
    /// let field = field!(AStruct=>0).join(field!(BStruct=>0));
    /// assert_eq!(field.get(&AStruct(BStruct(42))), &42);
    /// ```
    pub fn join<T>(self, next: Field<To, T>) -> Field<On, T> {
        // Safety:
        // We know 'On' contains a field 'Field' at the offset. We also know that
        // nexts offset creates a valid 'T' from a 'Field'. So, we should always get a valid
        // 'T' from an 'On' by putting them together.
        unsafe { Field::from_offset(self.offset + next.offset) }
    }
}

/// The field that this returns will just give back the same instance. Might be useful for generic
/// code.
impl<T> Default for Field<T, T> {
    fn default() -> Self {
        unsafe { Self::from_offset(0) }
    }
}

impl<On, To> PartialOrd for Field<On, To> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.offset.partial_cmp(&other.offset)
    }
}

impl<On, To> Ord for Field<On, To> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.offset.cmp(&other.offset)
    }
}

impl<On, To> PartialEq for Field<On, To> {
    fn eq(&self, other: &Self) -> bool {
        self.offset == other.offset
    }
}

impl<On, To> Eq for Field<On, To> {}

impl<On, To> Hash for Field<On, To> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.offset.hash(state);
    }
}

impl<On, To> Clone for Field<On, To> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<On, To> Copy for Field<On, To> {}

impl<On, To> fmt::Debug for Field<On, To> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "Field({})", self.offset)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Testing {
        a: u32,
        d: u64,
        b: u32,
        c: u64,
    }

    #[test]
    #[should_panic]
    fn create_fields_unaligned() {
        #[repr(packed)]
        struct MyStruct {
            a: u8,
            b: u32,
        }

        let a_field = field!(MyStruct=>a);
        let b_field = field!(MyStruct=>b);

        let s = MyStruct { a: 1, b: 2 };

        assert_eq!(*a_field.get(&s), 1);
        assert_eq!(*b_field.get(&s), 2);
    }

    #[test]
    fn create_fields() {
        let a_field = field!(Testing=>a);
        let b_field = field!(Testing=>b);

        let s = Testing {
            a: 1,
            b: 2,
            c: 99,
            d: 249,
        };

        assert_eq!(*a_field.get(&s), 1);
        assert_eq!(*b_field.get(&s), 2);
    }

    #[test]
    fn use_groups() {
        let mut testing = Testing {
            a: 0,
            b: 1,
            c: 2,
            d: 3,
        };

        let field_group = field_group!(Testing=>a, b);

        let [a, b] = field_group.get_mut(&mut testing);
        *a = 42;
        *b = 30;

        assert_eq!(testing.a, 42);
        assert_eq!(testing.b, 30);

        for element in field_group.iter_mut(&mut testing) {
            *element = 2;
        }

        assert_eq!(testing.a, 2);
        assert_eq!(testing.b, 2);

        assert!(array_group([field!(Testing=>c), field!(Testing=>c),]).is_none());
        assert!(group(&[field!(Testing=>c), field!(Testing=>c),]).is_none());
    }
}
