use crate::FieldRef;
use core::mem::MaybeUninit;
use core::ops::Deref;

/// Creates a group of fields. The group will be in the same order as the fields given into the
/// macro.
///
/// # Examples
/// ```
/// use field_ref::field_group;
///
/// struct Hi(u32, u32, u32);
///
/// let mut hi = Hi(3, 2, 1);
///
/// let group = field_group!(Hi, 0, 1, 2);
/// let [a, b, c] = group.get_mut(&mut hi);
/// assert_eq!(*a, 3);
/// *a = 5;
/// *b = 3;
/// *c = 2;
///
/// assert_eq!(hi.0, 5);
/// assert_eq!(hi.1, 3);
/// assert_eq!(hi.2, 2);
/// ```
#[macro_export]
macro_rules! field_group {
    ($type:ty, $($field:tt),+) => {{
        $crate::array_group([
            $(
                $crate::field_ref!($type, $field)
            ),+
        ]).expect("Field group has the same field more than once")
    }}
}

/// Tries to create a [`FieldGroup`] with all the given fields. Returns [`None`] if there are overlapping
/// fields. This is mostly to give users a safe way to get mutable references to separate fields at
/// the same time. If you know how many fields you have, you can use the [`array_group`] instead,
/// which gives you more power.
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
/// let fields = &[
///     field_ref!(Testing, a),
///     field_ref!(Testing, b),
///     field_ref!(Testing, c),
/// ];
///
/// for field in group(fields).unwrap().iter_mut(&mut test) {
///     *field = 42;
/// }
///
/// assert_eq!(test.a, 42);
/// assert_eq!(test.b, 42);
/// assert_eq!(test.c, 42);
/// ```
pub fn group<On, Field>(fields: &[FieldRef<On, Field>]) -> Option<&FieldGroup<On, Field>> {
    // Check for overlap
    for i in 0..fields.len() {
        for j in i + 1..fields.len() {
            if fields[i] == fields[j] {
                return None;
            }
        }
    }

    // Since there was no overlap, the invariant is fulfilled
    unsafe { Some(FieldGroup::from_slice(fields)) }
}

/// Creates a group of fields. The group will be in the same order as the fields given into the
/// function. If the same field appears more than once, None will be returned. If you know the
/// fields ahead of time, the [`field_group`] macro is more convenient to use.
///
/// # Examples
/// ```
/// use field_ref::{field_ref, array_group};
///
/// struct Hi(u32, u32, u32);
///
/// let mut hi = Hi(3, 2, 1);
///
/// let group = array_group([
///     field_ref!(Hi, 0),
///     field_ref!(Hi, 1),
///     field_ref!(Hi, 2)
/// ]).unwrap();
///
/// let [a, b, c] = group.get_mut(&mut hi);
/// assert_eq!(*a, 3);
/// *a = 5;
/// *b = 3;
/// *c = 2;
///
/// assert_eq!(hi.0, 5);
/// assert_eq!(hi.1, 3);
/// assert_eq!(hi.2, 2);
///
/// assert!(array_group([
///     field_ref!(Hi, 0),
///     field_ref!(Hi, 0),
/// ]).is_none());
/// ```
pub fn array_group<On, Field, const N: usize>(
    fields: [FieldRef<On, Field>; N],
) -> Option<ArrayFieldGroup<On, Field, N>> {
    // Check for overlap
    for i in 0..fields.len() {
        for j in i + 1..fields.len() {
            if fields[i] == fields[j] {
                return None;
            }
        }
    }

    // Since there was no overlap, the invariant is fulfilled
    Some(ArrayFieldGroup { fields })
}

/// A group of non-overlapping fields. Created with the [`array_group`] function.
pub struct ArrayFieldGroup<On, Field, const N: usize> {
    // Invariants:
    // * The fields cannot overlap
    fields: [FieldRef<On, Field>; N],
}

impl<On, Field, const N: usize> ArrayFieldGroup<On, Field, N> {
    pub fn get<'a>(&self, on: &'a On) -> [&'a Field; N] {
        let mut temp = MaybeUninit::<[&Field; N]>::uninit();

        let on_ptr = on as *const On;
        let mut ptr = temp.as_mut_ptr().cast::<&Field>();
        for field in &self.fields {
            unsafe {
                ptr.write(&*on_ptr.cast::<u8>().add(field.offset).cast::<Field>());
                ptr = ptr.add(1);
            }
        }

        unsafe { temp.assume_init() }
    }

    pub fn get_mut<'a>(&self, on: &'a mut On) -> [&'a mut Field; N] {
        let mut temp = MaybeUninit::<[&mut Field; N]>::uninit();

        let on_ptr = on as *mut On;
        let mut ptr = temp.as_mut_ptr().cast::<&mut Field>();
        for field in &self.fields {
            unsafe {
                ptr.write(&mut *on_ptr.cast::<u8>().add(field.offset).cast::<Field>());
                ptr = ptr.add(1);
            }
        }

        unsafe { temp.assume_init() }
    }
}

impl<On, Field, const N: usize> Deref for ArrayFieldGroup<On, Field, N> {
    type Target = FieldGroup<On, Field>;

    fn deref(&self) -> &Self::Target {
        // Safety: We also have the same invariant
        unsafe { FieldGroup::from_slice(self.fields.as_ref()) }
    }
}

/// A group of non-overlapping fields. Created with the [`group`] function.
#[repr(transparent)]
pub struct FieldGroup<On, Field> {
    // Invariants:
    // * The fields cannot overlap
    fields: [FieldRef<On, Field>],
}

impl<On, Field> FieldGroup<On, Field> {
    /// Creates a new group from a slice.
    ///
    /// # Safety
    /// * The fields cannot overlap.
    pub unsafe fn from_slice(fields: &[FieldRef<On, Field>]) -> &Self {
        &*(fields as *const [FieldRef<On, Field>] as *const FieldGroup<On, Field>)
    }

    /// Iterates over all the fields in order.
    pub fn iter<'a>(&'a self, on: &'a On) -> impl Iterator<Item = &'a Field> {
        let on_ptr = on as *const On;
        self.fields.iter().map(move |field| {
            // Safety: The invariants of the field ensure this is safe, as well as the invariant
            // that the fields cannot overlap.
            unsafe { &*on_ptr.cast::<u8>().add(field.offset).cast::<Field>() }
        })
    }

    /// Iterates over all the fields in order.
    pub fn iter_mut<'a>(&'a self, on: &'a mut On) -> impl Iterator<Item = &'a mut Field> {
        let on_ptr = on as *mut On;
        self.fields.iter().map(move |field| {
            // Safety: The invariants of the field ensure this is safe, as well as the invariant
            // that the fields cannot overlap.
            unsafe { &mut *on_ptr.cast::<u8>().add(field.offset).cast::<Field>() }
        })
    }
}
