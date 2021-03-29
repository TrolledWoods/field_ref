use crate::Field;
use core::mem::MaybeUninit;
use core::ops::Deref;
use core::cmp::{Ord, Ordering, PartialOrd};
use core::hash::{Hash, Hasher};

/// Creates a group of fields. The group will be in the same order as the fields given into the
/// macro. You can go multiple fields deep if you need to.
///
/// # Examples
/// ```
/// use field_ref::field_group;
///
/// struct Hi(u32, u32, (u32,));
///
/// let mut hi = Hi(3, 2, (1,));
///
/// let group = field_group!(Hi=>0, 1, 2.0);
/// let [a, b, c] = group.get_mut(&mut hi);
/// assert_eq!(*a, 3);
/// *a = 5;
/// *b = 3;
/// *c = 2;
///
/// assert_eq!(hi.0, 5);
/// assert_eq!(hi.1, 3);
/// assert_eq!(hi.2.0, 2);
/// ```
#[macro_export]
macro_rules! field_group {
    ($type:ty=>$($field:tt $(.$more_fields:tt)*),+) => {{
        $crate::array_group([
            $(
                $crate::field!($type=>$field$(.$more_fields)*)
            ),+
        ]).expect("Field group has the same field more than once")
    }};
}

/// Tries to create a [`FieldGroup`] with all the given fields. Returns [`None`] if there are overlapping
/// fields. This is mostly to give users a safe way to get mutable references to separate fields at
/// the same time. If you know how many fields you have, you can use the [`array_group`] instead,
/// which gives you more power.
///
/// # Examples
/// ```
/// use field_ref::{field, group};
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
///     field!(Testing=>a),
///     field!(Testing=>b),
///     field!(Testing=>c),
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
#[must_use]
pub fn group<On, To>(fields: &[Field<On, To>]) -> Option<&FieldGroup<On, To>> {
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
/// use field_ref::{field, array_group};
///
/// struct Hi(u32, u32, u32);
///
/// let mut hi = Hi(3, 2, 1);
///
/// let group = array_group([
///     field!(Hi=>0),
///     field!(Hi=>1),
///     field!(Hi=>2)
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
///     field!(Hi=>0),
///     field!(Hi=>0),
/// ]).is_none());
/// ```
#[must_use]
pub fn array_group<On, To, const N: usize>(
    fields: [Field<On, To>; N],
) -> Option<ArrayFieldGroup<On, To, N>> {
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
pub struct ArrayFieldGroup<On, To, const N: usize> {
    // Invariants:
    // * The fields cannot overlap
    fields: [Field<On, To>; N],
}

impl<On, To, const N: usize> ArrayFieldGroup<On, To, N> {
    pub fn get<'a>(&self, on: &'a On) -> [&'a To; N] {
        let mut temp = MaybeUninit::<[&To; N]>::uninit();

        let on_ptr = on as *const On;
        let mut ptr = temp.as_mut_ptr().cast::<&To>();
        for field in &self.fields {
            unsafe {
                ptr.write(&*on_ptr.cast::<u8>().add(field.offset).cast::<To>());
                ptr = ptr.add(1);
            }
        }

        unsafe { temp.assume_init() }
    }

    pub fn get_mut<'a>(&self, on: &'a mut On) -> [&'a mut To; N] {
        let mut temp = MaybeUninit::<[&mut To; N]>::uninit();

        let on_ptr = on as *mut On;
        let mut ptr = temp.as_mut_ptr().cast::<&mut To>();
        for field in &self.fields {
            unsafe {
                ptr.write(&mut *on_ptr.cast::<u8>().add(field.offset).cast::<To>());
                ptr = ptr.add(1);
            }
        }

        unsafe { temp.assume_init() }
    }
}

impl<On, To, const N: usize> Deref for ArrayFieldGroup<On, To, N> {
    type Target = FieldGroup<On, To>;

    fn deref(&self) -> &Self::Target {
        // Safety: We also have the same invariant
        unsafe { FieldGroup::from_slice(self.fields.as_ref()) }
    }
}

impl<On, To, const N: usize> PartialOrd for ArrayFieldGroup<On, To, N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.fields.partial_cmp(&other.fields)
    }
}

impl<On, To, const N: usize> Ord for ArrayFieldGroup<On, To, N> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.fields.cmp(&other.fields)
    }
}

impl<On, To, const N: usize> PartialEq for ArrayFieldGroup<On, To, N> {
    fn eq(&self, other: &Self) -> bool {
        self.fields == other.fields
    }
}

impl<On, To, const N: usize> Eq for ArrayFieldGroup<On, To, N> {}

impl<On, To, const N: usize> Hash for ArrayFieldGroup<On, To, N> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.fields.hash(state);
    }
}

impl<On, To, const N: usize> Clone for ArrayFieldGroup<On, To, N> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<On, To, const N: usize> Copy for ArrayFieldGroup<On, To, N> {}


/// A group of non-overlapping fields. Created with the [`group`] function.
#[repr(transparent)]
pub struct FieldGroup<On, To> {
    // Invariants:
    // * The fields cannot overlap
    fields: [Field<On, To>],
}

impl<On, To> FieldGroup<On, To> {
    /// Creates a new group from a slice.
    ///
    /// # Safety
    /// * The fields cannot overlap.
    #[must_use]
    pub unsafe fn from_slice(fields: &[Field<On, To>]) -> &Self {
        &*(fields as *const [Field<On, To>] as *const FieldGroup<On, To>)
    }

    /// Iterates over all the fields in order.
    pub fn iter<'a>(
        &'a self,
        on: &'a On,
    ) -> impl Iterator<Item = &'a To>
           + core::iter::FusedIterator
           + core::iter::ExactSizeIterator
           + core::iter::DoubleEndedIterator {
        let on_ptr = on as *const On;
        self.fields.iter().map(move |field| {
            // Safety: The invariants of the field ensure this is safe, as well as the invariant
            // that the fields cannot overlap.
            unsafe { &*on_ptr.cast::<u8>().add(field.offset).cast::<To>() }
        })
    }

    /// Iterates over all the fields in order.
    pub fn iter_mut<'a>(
        &'a self,
        on: &'a mut On,
    ) -> impl Iterator<Item = &'a mut To>
           + core::iter::FusedIterator
           + core::iter::ExactSizeIterator
           + core::iter::DoubleEndedIterator {
        let on_ptr = on as *mut On;
        self.fields.iter().map(move |field| {
            // Safety: The invariants of the field ensure this is safe, as well as the invariant
            // that the fields cannot overlap.
            unsafe { &mut *on_ptr.cast::<u8>().add(field.offset).cast::<To>() }
        })
    }
}

impl<On, To> PartialOrd for FieldGroup<On, To> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.fields.partial_cmp(&other.fields)
    }
}

impl<On, To> Ord for FieldGroup<On, To> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.fields.cmp(&other.fields)
    }
}

impl<On, To> PartialEq for FieldGroup<On, To> {
    fn eq(&self, other: &Self) -> bool {
        self.fields == other.fields
    }
}

impl<On, To> Eq for FieldGroup<On, To> {}
