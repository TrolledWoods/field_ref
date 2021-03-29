#![no_std]

use core::cmp::{Ord, Ordering, PartialOrd};
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem::MaybeUninit;

/// This creates a [`FieldRef`] to a field of a type. The type cannot implement [`Deref`](core::ops::Deref), because deref can run arbitrary
/// code, which would mean that the method this library uses to reference fields isn't guaranteed to be correct.
///
/// # Examples
/// ```
/// use field_ref::field_ref;
///
/// struct Struct(u32, u32);
///
/// let a = field_ref!(Struct, 0);
/// let b = field_ref!(Struct, 1);
/// assert_ne!(a, b);
///
/// let mut s = Struct(1, 2);
///
/// a.set(&mut s, 4);
/// assert_eq!(s.0, 4);
/// ```
#[macro_export]
macro_rules! field_ref {
    ($on:ty, $field:tt) => {{
        // @Speed: This will probably ruin compiletimes a bit
        const _: fn() -> () = || {
            struct Check<T: ?Sized>(T);
            trait AmbiguousIfImpl<A> { fn some_item() { } }

            impl<T: ?Sized> AmbiguousIfImpl<()> for Check<T> { }
            impl<T: ?Sized + core::ops::Deref> AmbiguousIfImpl<u8> for Check<T> { }

            <Check::<$on> as AmbiguousIfImpl<_>>::some_item() // Your type probably implements 'Defer'. It's not allowed to
        };

        // Because the type does not implement Deref this is safe to do!
        let temp = core::mem::MaybeUninit::<$on>::uninit();
        unsafe { $crate::FieldRef::from_pointers(temp.as_ptr(), core::ptr::addr_of!((*temp.as_ptr()).$field)) }
    }};
}

/// A group of non-overlapping fields. Created with the [`group`] function.
pub struct FieldGroup<On, Field, const N: usize> {
    // Invariants:
    // * The fields cannot overlap
    fields: [FieldRef<On, Field>; N],
}

impl<On, Field, const N: usize> FieldGroup<On, Field, N> {
    /// Iterates over all the fields in order.
    pub fn iter<'a>(&'a self, on: &'a On) -> impl Iterator<Item = &'a Field> {
        let on_ptr = on as *const On;
        self.fields.iter().enumerate().map(move |(i, field)| {
            // Safety: The invariants of the field ensure this is safe, as well as the invariant
            // that the fields cannot overlap.
            unsafe { &*on_ptr.cast::<u8>().add(field.offset).cast::<Field>() }
        })
    }

    /// Iterates over all the fields in order.
    pub fn iter_mut<'a>(&'a self, on: &'a mut On) -> impl Iterator<Item = &'a mut Field> {
        let on_ptr = on as *mut On;
        self.fields.iter().enumerate().map(move |(i, field)| {
            // Safety: The invariants of the field ensure this is safe, as well as the invariant
            // that the fields cannot overlap.
            unsafe { &mut *on_ptr.cast::<u8>().add(field.offset).cast::<Field>() }
        })
    }

    /// Reads all the fields in the group from a value. The returned fields are in the same order
    /// as given to the [`group`] function.
    pub fn get<'a>(&self, on: &'a On) -> [&'a Field; N] {
        let mut temp = MaybeUninit::<[&Field; N]>::uninit();

        let on_ptr = on as *const On;
        let field_ptr = temp.as_mut_ptr().cast::<&Field>();
        for (i, field) in self.fields.iter().enumerate() {
            // Safety: The invariants of the field ensure this is safe
            unsafe {
                field_ptr
                    .add(i)
                    .write(&*on_ptr.cast::<u8>().add(field.offset).cast::<Field>());
            }
        }

        // Safety: We wrote to all the indices in the array in the loop
        unsafe { temp.assume_init() }
    }

    /// Reads all the fields in the group from a value. The returned fields are in the same order
    /// as given to the [`group`] function.
    pub fn get_mut<'a>(&self, on: &'a mut On) -> [&'a mut Field; N] {
        let mut temp = MaybeUninit::<[&mut Field; N]>::uninit();

        let on_ptr = on as *mut On;
        let field_ptr = temp.as_mut_ptr().cast::<&mut Field>();
        for (i, field) in self.fields.iter().enumerate() {
            // Safety: The invariants of the field ensure this is safe, as well as the invariant
            // that the fields cannot overlap.
            unsafe {
                field_ptr
                    .add(i)
                    .write(&mut *on_ptr.cast::<u8>().add(field.offset).cast::<Field>());
            }
        }

        // Safety: We wrote to all the indices in the array in the loop
        unsafe { temp.assume_init() }
    }
}

/// Tries to create a [`FieldGroup`] with all the given fields. Returns [`None`] if there are overlapping
/// fields.
///
/// # Examples
/// ```
/// use field_ref::{field_ref, group};
///
/// struct Testing {
///     a: u32,
///     b: u32,
///     c: u32,
/// }
///
/// let mut test = Testing {
///     a: 0,
///     b: 0,
///     c: 0,
/// };
///
/// let fields = group([
///     field_ref!(Testing, a),
///     field_ref!(Testing, b),
///     field_ref!(Testing, c),
/// ]).unwrap();
///
/// let [a, b, c] = fields.get_mut(&mut test);
/// *a = 42;
/// *b = 30;
/// *c = 10;
///
/// assert_eq!(test.a, 42);
/// assert_eq!(test.b, 30);
/// assert_eq!(test.c, 10);
/// ```
pub fn group<On, Field, const N: usize>(
    fields: [FieldRef<On, Field>; N],
) -> Option<FieldGroup<On, Field, N>> {
    // Check for overlap
    for i in 0..fields.len() {
        for j in i + 1..fields.len() {
            if fields[i] == fields[j] {
                return None;
            }
        }
    }

    // Since there was no overlap, the invariant is fulfilled
    Some(FieldGroup { fields })
}

/// A very lightweight reference to a struct field.
///
/// It's guaranteed to be the exact same representation as a [`usize`]
#[repr(C)]
pub struct FieldRef<On, Field> {
    // Invariants:
    // * This has to be a valid offset from the start of an 'On' struct that produces the
    // field. It's in bytes.
    // * Fields cannot overlap. This means we can't do tricks like [T; 3] having fields with type [T; 2], even though that's
    // theoretically possible, as I think it's more useful to be able to partially borrow the
    // types.
    offset: usize,
    _phantom: PhantomData<(On, Field)>,
}

impl<On, Field> FieldRef<On, Field> {
    /// Creates a [`FieldRef`] from two pointers. Have a look at the [`field_ref`] macro if you
    /// want a safe way to create this struct.
    ///
    /// # Panics
    /// * If the field and on pointers are not aligned
    ///
    /// # Safety
    /// * The offset between field and on has to be valid to pass to `from_offset`
    pub unsafe fn from_pointers(on: *const On, field: *const Field) -> Self {
        assert_eq!(
            (field as usize - on as usize) % core::mem::align_of::<Field>(),
            0,
            "Cannot create a 'FieldRef' to an unaligned field"
        );
        Self::from_offset(field as usize - on as usize)
    }

    /// Creates a [`FieldRef`] from just an offset. Have a look at the [`field_ref`] macro if you
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
    pub unsafe fn offset_ptr(self, raw: *const On) -> *const Field {
        raw.cast::<u8>().add(self.offset).cast::<Field>()
    }

    /// Offsets a mutable raw pointer to the field.
    ///
    /// # Safety
    /// * There has to be an allocated object at least the size of the `On` type.
    pub unsafe fn offset_mut_ptr(self, raw: *mut On) -> *mut Field {
        raw.cast::<u8>().add(self.offset).cast::<Field>()
    }

    /// Reads a field from a type.
    pub fn get(self, on: &On) -> &Field {
        // Safety
        // * This is safe because of the invariant
        unsafe {
            &*(on as *const On)
                .cast::<u8>()
                .add(self.offset)
                .cast::<Field>()
        }
    }

    /// Reads a field from a type mutably.
    pub fn get_mut(self, on: &mut On) -> &mut Field {
        // Safety
        // * This is safe because of the invariant
        unsafe {
            &mut *(on as *mut On)
                .cast::<u8>()
                .add(self.offset)
                .cast::<Field>()
        }
    }

    /// Sets the value of a field
    pub fn set(self, on: &mut On, new: Field) {
        *self.get_mut(on) = new;
    }

    /// Replaces the value of a field, and returns the old value
    pub fn replace(self, on: &mut On, new: Field) -> Field {
        core::mem::replace(self.get_mut(on), new)
    }

    /// Joins fields, i.e. takes a field of a field.
    ///
    /// # Examples
    /// ```
    /// use field_ref::field_ref;
    ///
    /// struct BStruct(u32);
    /// struct AStruct(BStruct);
    ///
    /// let field = field_ref!(AStruct, 0).join(field_ref!(BStruct, 0));
    /// assert_eq!(field.get(&AStruct(BStruct(42))), &42);
    /// ```
    pub fn join<T>(self, next: FieldRef<Field, T>) -> FieldRef<On, T> {
        // Safety:
        // We know 'On' contains a field 'Field' at the offset. We also know that
        // nexts offset creates a valid 'T' from a 'Field'. So, we should always get a valid
        // 'T' from an 'On' by putting them together.
        unsafe { FieldRef::from_offset(self.offset + next.offset) }
    }
}

/// The field that this returns will just give back the same instance. Might be useful for generic
/// code.
impl<T> Default for FieldRef<T, T> {
    fn default() -> Self {
        unsafe { Self::from_offset(0) }
    }
}

impl<On, Field> PartialOrd for FieldRef<On, Field> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.offset.partial_cmp(&other.offset)
    }
}

impl<On, Field> Ord for FieldRef<On, Field> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.offset.cmp(&other.offset)
    }
}

impl<On, Field> PartialEq for FieldRef<On, Field> {
    fn eq(&self, other: &Self) -> bool {
        self.offset == other.offset
    }
}

impl<On, Field> Eq for FieldRef<On, Field> {}

impl<On, Field> Hash for FieldRef<On, Field> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.offset.hash(state);
    }
}

impl<On, Field> Clone for FieldRef<On, Field> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<On, Field> Copy for FieldRef<On, Field> {}

impl<On, Field> fmt::Debug for FieldRef<On, Field> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "FieldRef({})", self.offset)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn create_fields_unaligned() {
        #[repr(packed)]
        struct MyStruct {
            a: u8,
            b: u32,
        }

        let a_field = field_ref!(MyStruct, a);
        let b_field = field_ref!(MyStruct, b);

        let s = MyStruct { a: 1, b: 2 };

        assert_eq!(*a_field.get(&s), 1);
        assert_eq!(*b_field.get(&s), 2);
    }

    #[test]
    fn create_fields() {
        struct MyStruct {
            a: u8,
            b: u32,
        }

        let a_field = field_ref!(MyStruct, a);
        let b_field = field_ref!(MyStruct, b);

        let s = MyStruct { a: 1, b: 2 };

        assert_eq!(*a_field.get(&s), 1);
        assert_eq!(*b_field.get(&s), 2);
    }
}
