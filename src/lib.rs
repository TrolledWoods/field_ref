use std::marker::PhantomData;

/// This creates a [`FieldRef`] to a field of a type. The type cannot implement [`Deref`](core::ops::Deref).
#[macro_export]
macro_rules! field_ref {
    ($on:ty, $field:ident) => {{
        // @Speed: This will probably ruin compiletimes a bit
        const _: fn() -> () = || {
            struct Check<T: ?Sized>(T);
            trait AmbiguousIfImpl<A> { fn some_item() { } }

            impl<T: ?Sized> AmbiguousIfImpl<()> for Check<T> { }
            impl<T: ?Sized + std::ops::Deref> AmbiguousIfImpl<u8> for Check<T> { }

            <Check::<$on> as AmbiguousIfImpl<_>>::some_item() // Your type probably implements 'Defer'. It's not allowed to
        };

        // Because the type does not implement Deref this is safe to do!
        let temp = std::mem::MaybeUninit::<$on>::uninit();
        unsafe { $crate::FieldRef::from_pointers(temp.as_ptr(), std::ptr::addr_of!((*temp.as_ptr()).$field)) }
    }};
}

/// A very lightweight reference to a struct field.
///
/// It's lightweight because it is represented just by an offset of bytes.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FieldRef<On, Field> {
    // Invariant: This has to be a valid offset from the start of an 'On' struct that produces the
    // field. It's in bytes.
    offset: usize,

    // @Cleanup: This might be bad, since this will get variances from the generic parameters.
    _on: PhantomData<On>,
    _field: PhantomData<Field>,
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
    unsafe fn from_pointers(on: *const On, field: *const Field) -> Self {
        assert_eq!(
            (field as usize - on as usize) % std::mem::align_of::<Field>(),
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
            _on: PhantomData,
            _field: PhantomData,
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

    /// Joins fields, i.e. takes a field of a field
    pub fn join<T>(self, next: FieldRef<Field, T>) -> FieldRef<On, T> {
        // Safety:
        // We know 'On' contains a field 'Field' at the offset. We also know that
        // nexts offset creates a valid 'T' from a 'Field'. So, we should always get a valid
        // 'T' from an 'On' by putting them together.
        unsafe { FieldRef::from_offset(self.offset + next.offset) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_fields() {
        struct MyStruct {
            a: u8,
            b: u32,
        }

        let a_field: FieldRef<MyStruct, u8> = field_ref!(MyStruct, a);
        let b_field: FieldRef<MyStruct, u32> = field_ref!(MyStruct, b);

        let s = MyStruct { a: 1, b: 2 };

        assert_eq!(*a_field.get(&s), 1);
        assert_eq!(*b_field.get(&s), 2);
    }
}
