//! Id types, are types that have the size of a [`usize`], and so benefit from
//! a super lightweight [`Clone`] and are even [`Copy`], while being global. They
//! have the same advantages (and performance maybe) as a smart pointer like
//! `Arc<Mutex<T>>`.
//!
//! # How to
//!
//! ```
//! # use lunc_utils::idtype;
//! #
//! // we define the idtype like so:
//! idtype! {
//!     /// Hello i am the documentation
//!     pub type TestId(&'static str);
//!     //               ^ NOTE: the 'static lifetime is necessary for string
//!     //                 slices like that
//!
//!     /// Another type, they do not share the same database
//!     pub type AnotherOne(&'static str);
//!
//!     /// You can even not have a type.
//!     pub type NoTypeOne;
//! }
//!
//! let a = TestId::with_internal("A");
//!
//! // you can access the data stored
//! a.inspect(|this| {
//!     assert_eq!(this, &"A");
//! });
//!
//! let b = a.clone();
//!
//! // drop is implemented so the value behind a will be dropped if there is
//! // only one instance of it.
//! drop(a);
//!
//! {
//!     let db = TestId::database().lock();
//!
//!     // there is only one instance of the object remaining
//!     assert_eq!(db.alive(b.id()), Some(1));
//! }
//!
//! // we can mutate its value
//! b.inspect_mut(|this| {
//!     *this = "B";
//! });
//!
//! // we also drop b, now there is no more instance to "B", the value is
//! // dropped
//! let b_id = b.id();
//! drop(b);
//!
//! let database = TestId::database().lock();
//! // there is no more instance alive, because we dropped a and b
//! assert_eq!(database.alive(b_id), None);
//! ```

use std::{
    collections::HashMap,
    num::NonZeroUsize,
    sync::{LazyLock, RwLock, RwLockReadGuard, RwLockWriteGuard},
};

// TODO(URGENT): rewrite this macro as a procedural macro, declarative macros
// are not powerful enough here, we are doing too much hacks.
//
// Do it in the style of an attribute macro like so:
//
// #[idtype(derive = [Hash, PartialEq, Eq])]
// pub struct IdTypeTest {
//     #[set] // add the method `set_field_a(&mut Self, A)`
//     #[get] // add the method `field_a` that returns a clone of field_a
//     field_a: A,
// }

/// Macro used to define idtypes, see [`idtype`] documentation.
///
/// [`idtype`]: mod@crate::idtype
#[macro_export]
macro_rules! idtype {
    {} => {};

    {$(#[$attr:meta])* $vis:vis type $name:ident; $($rest:tt)*} => {
        $crate::idtype! {
            $( #[$attr] )*  $vis type $name(());
            $( $rest )*
        }
    };

    {$(#[$attr:meta])* $vis:vis type $name:ident ($T:ty); $($rest:tt)*} => {
        impl $crate::idtype::InternalType for $name {
            type Internal = $T;
        }

        $crate::internal_idtype!(
            attr = [ $( $attr , )* ],
            vis = $vis,
            name = $name,
            T = $T,
        );

        $crate::idtype! { $( $rest )* }
    };

    {impl clone_methods for $name:ident; $($rest:tt)*} => {
        impl $name {
            /// Tries to clones the value, note this calls [`clone`], and it
            /// may be slow.
            ///
            /// [`clone`]: Clone::clone
            pub fn try_clone_value(&self) -> Option<<Self as $crate::idtype::InternalType>::Internal> {
                self.try_inspect(|this| <<Self as $crate::idtype::InternalType>::Internal as Clone>::clone(this))
            }

            /// Clones the value, note this calls [`clone`], and it may be
            /// slow.
            ///
            /// # Panic
            ///
            /// This function panics if we cannot acquire a Read lock of the
            /// value, see [`read`].
            ///
            /// [`clone`]: Clone::clone
            /// [`read`]: std::sync::RwLock::read
            pub fn clone_val(&self) -> <Self as $crate::idtype::InternalType>::Internal {
                self.try_clone_value().unwrap()
            }
        }

        $crate::idtype! { $( $rest )* }
    };

    {impl Hash for $name:ident; $($rest:tt)*} => {
        impl std::hash::Hash for $name {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                // let db = Self::database().lock();

                // let entry = db.get_entry(self.0);

                // let guard = entry.value.read().unwrap();

                // <<Self as $crate::idtype::InternalType>::Internal as std::hash::Hash>::hash(&*guard, state);
                state.write_usize(self.0.get());
            }
        }

        $crate::idtype! { $( $rest )* }
    };

    {impl PartialEq for $name:ident; $($rest:tt)*} => {
        impl PartialEq for $name {
            #[doc = concat!("Equality of two [`", stringify!($name), "`].")]
            ///
            /// They are equal, only if their internal values are equal, even if
            /// they are not referring to the same object.
            ///
            /// If you want to know if two instances refer to the same object
            /// see
            #[doc = concat!("[`", stringify!($name), "::object_eq`]")]
            fn eq(&self, other: &Self) -> bool {
                // // NOTE: we cannot use the `object_eq` method here because we
                // // don't know if the internal value implements `Eq`
                // let db = Self::database().lock();

                // let self_entry = db.get_entry(self.0);

                // let self_guard = self_entry.value.read().unwrap();

                // let other_entry = db.get_entry(other.0);

                // let other_guard = other_entry.value.read().unwrap();

                // PartialEq::eq(&*self_guard, &*other_guard)

                self.object_eq(other)
            }
        }

        $crate::idtype! { $( $rest )* }
    };

    {impl Eq for $name:ident; $($rest:tt)*} => {
        impl Eq for $name {}

        $crate::idtype! { $( $rest )* }
    };

    {$(#[$attr:meta])* $vis:vis struct $name:ident $( [ $( $derive:path ),*  $(,)? ] )? { $( $(#[$field_attr:meta])* $field_vis:vis $field_name:ident : $field_ty:ty ),* $( , )? } $($rest:tt)*} => {
        $crate::idtype::concat_idents!(internal_name =  Internal, $name {
            /// Internal struct for [`
            #[doc = stringify!($name)]
            ///`].
            #[derive(Debug)]
            $(
                $( #[derive($derive)] )*
            )?
            pub struct internal_name {
                $( $( #[$field_attr] )* $field_vis $field_name : $field_ty , )*
            }

            impl $crate::idtype::InternalType for $name {
                type Internal = internal_name ;
            }


            $crate::internal_idtype!(
                attr = [
                    $( $attr , )*
                    doc = "# Fields documentation",
                    $(
                        doc = concat!("## `", stringify!($field_name), "`"),
                        $(
                            $field_attr,
                        )*
                        doc = "\n\n",
                    )*
                ],
                vis = $vis,
                name = $name,
                T = <$name as $crate::idtype::InternalType>::Internal,
            );
        });

        $crate::idtype! { $( $rest )* }
    };

    {impl FieldSet<$field_name:ident: $field_ty:ty> for $name:ident; $($rest:tt)*} => {
        impl $name {
            $crate::idtype::concat_idents!(set_method = set_, $field_name {
                /// Set the field `
                #[doc = stringify!($field_name)]
                ///` to the new value.
                ///
                /// # Panic
                ///
                /// This function may panic if it cannot acquire a write
                /// guard to the lock.
                pub fn set_method(&mut self, $field_name: impl Into<$field_ty>) {
                    let db = Self::database().lock();

                    let entry = db.get_entry(self.0);

                    let mut guard = entry.value.write().unwrap();

                    guard.$field_name = $field_name.into();
                }
            });
        }

        $crate::idtype! { $( $rest )* }
    };
    {impl FieldGet<$vis:vis $field_name:ident: $field_ty:ty> for $name:ident; $($rest:tt)*} => {
        impl $name {
            #[doc = concat!("Get the `", stringify!($field_name), "` of ", stringify!($name))]
            $vis fn $field_name(&self) -> $field_ty {
                let db = Self::database().lock();

                db.get(self.0).read().unwrap().$field_name.clone()
            }
        }

        $crate::idtype! { $( $rest )* }
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! internal_idtype {
    (attr = [ $( $attr:meta , )* ], vis = $vis:vis, name = $name:ident, T = $T:ty,) => {
        $crate::idtype::concat_idents!(database_name = DATABASE_, $name {
            $( #[$attr] )*
            #[repr(transparent)]
            $vis struct $name(std::num::NonZeroUsize);
            // NOTE: this maybe overkill because on a 64 bit machine you can
            // have up to 18_446_744_073_709_551_615 objects, and it can be more
            // than what we need, so it may be a good idea to change this to
            // use `NonZeroU32`.

            $crate::idtype::concat_idents!(test_name = test_idtype_, $name, _as_correct_sizes {
                #[allow(non_snake_case)]
                #[cfg(test)]
                #[test]
                fn test_name(){
                    assert_eq!(std::mem::size_of::<$name>(), std::mem::size_of::<Option<$name>>());
                    assert_eq!(std::mem::size_of::<$name>(), std::mem::size_of::<usize>());
                }
            });

            #[allow(non_upper_case_globals)]
            pub(crate) static database_name: $crate::idtype::DatabaseLock<$T> = $crate::idtype::DatabaseLock::new();

            impl $name {
                /// Creates a new [`
                #[doc = stringify!($name)]
                ///`] with the internal value.
                ///
                /// # Example
                ///
                /// ```
                /// # use lunc_utils::idtype;
                /// idtype! {
                ///     type TestId(usize);
                /// }
                ///
                /// let a = TestId::with_internal(12);
                ///
                /// a.inspect(|id| {
                ///     assert_eq!(*id, 12);
                /// });
                /// ```
                pub fn with_internal(value: $T) -> Self {
                    let mut db = database_name.lock_mut();
                    let id = db.register(value);

                    Self(id)
                }

                /// Creates a new [`
                #[doc = stringify!($name)]
                ///`] from the id.
                ///
                ///
                /// # Safety
                ///
                /// This is not safe, because using an object that is not
                /// instantiated can lead to panics, or if the id's object is
                /// initialized, it can lead to use of an object that will die
                /// before this typeid. **TLDR: use it if you know what you
                /// do.**
                pub const unsafe fn from_raw(id: std::num::NonZeroUsize) -> Self {
                    Self(id)
                }

                /// Returns a reference to the database for this idtype.
                pub const fn database() -> &'static $crate::idtype::DatabaseLock<$T> {
                    &database_name
                }

                /// Mutable failable inspection of the value of [`
                #[doc = stringify!($name)]
                ///`].
                ///
                #[doc = concat!("See [`", stringify!($name), "::inspect_mut`] for more details.")]
                pub fn try_inspect_mut<R>(&self, mut f: impl FnMut(&mut $T) -> R) -> Option<R> {
                    let db = database_name.lock();

                    let entry = db.get_entry(self.0);

                    let mut guard = entry.value.write().ok()?;

                    Some(f(&mut *guard))
                }

                /// Mutable inspection of the value of [`
                #[doc = stringify!($name)]
                ///`].
                ///
                /// # Example
                ///
                /// ```
                /// # use lunc_utils::idtype;
                /// idtype! {
                ///     type TestId(usize);
                /// }
                ///
                /// let a = TestId::with_internal(12);
                ///
                /// a.inspect(|id| {
                ///     assert_eq!(*id, 12);
                /// });
                ///
                /// a.inspect_mut(|id| {
                ///     *id *= 2;
                /// });
                ///
                /// a.inspect(|id| {
                ///     assert_eq!(*id, 24);
                /// });
                /// ```
                ///
                /// # Panic
                ///
                /// This function will panic if we cannot acquire a write lock
                /// to the underlying data
                pub fn inspect_mut<R>(&self, f: impl FnMut(&mut $T) -> R) -> R {
                    self.try_inspect_mut(f).unwrap()
                }

                /// Mutable failable inspection of the value of [`
                #[doc = stringify!($name)]
                ///`] that captures all variables.
                ///
                #[doc = concat!("See [`", stringify!($name), "::inspect_once`] for more details.")]
                pub fn try_inspect_once<R>(&self, f: impl FnOnce(&mut $T) -> R) -> Option<R> {
                    let db = database_name.lock();

                    let entry = db.get_entry(self.0);

                    let mut guard = entry.value.write().ok()?;

                    Some(f(&mut *guard))
                }

                /// Mutable inspection of the value of [`
                #[doc = stringify!($name)]
                ///`] that moves every captured variable.
                ///
                /// # Panic
                ///
                /// This function will panic if we cannot acquire a write lock
                /// to the underlying data
                pub fn inspect_once<R>(&self, f: impl FnOnce(&mut $T) -> R) -> R {
                    self.try_inspect_once(f).unwrap()
                }

                /// Failable inspection of the value of [`
                #[doc = stringify!($name)]
                ///`].
                ///
                #[doc = concat!("See [`", stringify!($name), "::inspect`] for more details.")]
                pub fn try_inspect<R>(&self, mut f: impl FnMut(&$T) -> R) -> Option<R> {
                    let db = database_name.lock();

                    let entry = db.get_entry(self.0);

                    let guard = entry.value.read().ok()?;

                    Some(f(&*guard))
                }

                /// Inspect the value of [`
                #[doc = stringify!($name)]
                ///`].
                ///
                /// # Example
                ///
                /// ```
                /// # use lunc_utils::idtype;
                /// idtype! {
                ///     type TestId(usize);
                /// }
                ///
                /// let a = TestId::with_internal(12);
                ///
                /// a.inspect(|id| {
                ///     assert_eq!(*id, 12);
                /// });
                /// ```
                ///
                /// # Panic
                ///
                /// This function will panic if we cannot acquire a read lock to
                /// the underlying data
                pub fn inspect<R>(&self, f: impl FnMut(&$T) -> R) -> R {
                    self.try_inspect(f).unwrap()
                }

                /// Returns the id
                ///
                /// # Note
                ///
                /// You cannot rely on the `id` this function will return
                /// you, it's a bad idea to write a test that verifies if the
                /// `id` of an instance is equal to something. The `id` is not
                /// guaranteed to be persistent in any fashion, across versions,
                /// across runs, etc.. You can just rely on the `id` to be the
                /// same across to instances of the same object like in the
                /// following example.
                ///
                /// # Example
                ///
                /// ```
                /// # use lunc_utils::idtype;
                /// idtype! {
                ///     type TestId;
                /// }
                ///
                /// let a = TestId::with_internal(());
                ///
                /// // SAFETY: this is safe for the example but not for real
                /// // use cases, because we did not increment the count of
                /// // instances alive but whatever
                /// let b = unsafe { TestId::from_raw(a.id()) };
                ///
                /// assert!(a.object_eq(&b));
                /// ```
                ///
                /// # Design decision
                ///
                /// Note that the return type of this function is
                /// [`NonZeroUsize`], this permits Rust to optimize out
                #[doc = concat!("[`Option<", stringify!($name), ">`]")]
                /// to have have **the same size and alignment** as
                #[doc = concat!("[`", stringify!($name), "`].")]
                ///
                /// [`NonZeroUsize`]: std::num::NonZeroUsize
                pub fn id(&self) -> std::num::NonZeroUsize {
                    self.0
                }

                /// Are these instances referring to the same object?
                ///
                /// # Example
                ///
                /// ```
                /// # use lunc_utils::idtype;
                /// idtype! {
                ///     type TestId;
                /// }
                ///
                /// let a = TestId::with_internal(());
                /// let b = a.clone();
                ///
                /// assert!(a.object_eq(&b));
                /// ```
                pub fn object_eq(&self, other: &Self) -> bool {
                    self.0 == other.0
                }

                /// Returns the amount of instances alive, for that object.
                ///
                /// # Example
                ///
                /// ```
                /// # use lunc_utils::idtype;
                /// idtype! {
                ///     type TestId;
                /// }
                ///
                /// let a = TestId::with_internal(());
                /// let b = a.clone();
                ///
                /// assert_eq!(a.alive(), 2);
                /// ```
                pub fn alive(&self) -> usize {
                    let db = Self::database().lock();

                    db.alive(self.0).unwrap_or_default() as usize
                }
            }

            impl std::fmt::Debug for $name {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    let db = database_name.lock();

                    let mut format = f.debug_struct(stringify!($name));
                    format.field("id", &self.0);

                    struct Unknown;
                    impl std::fmt::Debug for Unknown {
                        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                            write!(f, "<unknown>")
                        }
                    }

                    let data_guard = db
                        .try_get(self.0)
                        .map(|lock| lock.read().ok())
                        .flatten();

                    let data = data_guard
                        .as_ref()
                        .map(|d| d as &dyn std::fmt::Debug)
                        .unwrap_or(&Unknown);

                    format
                        .field("data", data)
                        .field("alive", &db.alive(self.0).unwrap_or(0))
                        .finish()
                }
            }

            impl Clone for $name {
                fn clone(&self) -> Self {
                    let mut db = database_name.lock_mut();

                    unsafe {
                        // SAFETY: we are cloning the instance so this is fine.
                        db.increment_count(self.0);
                    }

                    Self(self.0)
                }
            }

            impl Drop for $name {
                fn drop(&mut self) {
                    let mut db = database_name.lock_mut();

                    db.drop_instance(self.0);
                }
            }

        });

    }
}

#[doc(hidden)]
pub use ::concat_idents::concat_idents;

#[doc(inline)]
pub use crate::idtype;

#[derive(Debug)]
pub struct Entry<T> {
    #[doc(hidden)]
    pub value: RwLock<T>,
    /// count of how many alive instances there is currently.
    // NOTE: just like NonZeroUsize is overkill for the id, because there is way too
    // much, i think u16 should be fine here but idk maybe u32 is fine
    pub count: u32,
}

/// Database of idtype, for type `T`.
#[derive(Debug)]
pub struct Database<T> {
    data: HashMap<NonZeroUsize, Entry<T>>,
    last_id: NonZeroUsize,
}

impl<T> Database<T> {
    /// Create a new empty database
    pub fn new() -> Database<T> {
        Database {
            data: HashMap::new(),
            last_id: NonZeroUsize::new(1).unwrap(),
        }
    }

    /// Register a new object of this type and returns it's id.
    pub fn register(&mut self, value: T) -> NonZeroUsize {
        let id = self.last_id;

        // SAFETY: we are adding to a usize, this is guaranteed to never return 0
        self.last_id = unsafe { NonZeroUsize::new_unchecked(self.last_id.get() + 1) };

        self.data.insert(
            id,
            Entry {
                value: RwLock::new(value),
                count: 1,
            },
        );

        id
    }

    /// Tries to get the underlying value
    pub fn try_get(&self, id: NonZeroUsize) -> Option<&RwLock<T>> {
        self.data.get(&id).map(|entry| &entry.value)
    }

    /// Gets the value at the given id
    ///
    /// # Panic
    ///
    /// It panics if the id is not valid
    #[track_caller]
    pub fn get(&self, id: NonZeroUsize) -> &RwLock<T> {
        self.try_get(id).expect("invalid id")
    }

    /// Gets the entry of the id
    ///
    /// # Panic
    ///
    /// It panics if the id is not valid
    #[track_caller]
    pub fn get_entry(&self, id: NonZeroUsize) -> &Entry<T> {
        self.data.get(&id).expect("invalid id")
    }

    /// Tries to increments the count of currently alive instance of the object
    /// with `id`, if the id is not valid it does not do anything.
    ///
    /// # Safety
    ///
    /// If you call this function but the typeid was not cloned, it can lead to the
    /// object not being dropped, if the database is static
    pub unsafe fn increment_count(&mut self, id: NonZeroUsize) {
        let Some(entry) = self.data.get_mut(&id) else {
            return;
        };

        entry.count = entry
            .count
            .checked_add(1)
            .expect("You cannot have more than 4_294_967_295 instances of an object");
    }

    /// Tries to decrements the count of currently alive instance of the object
    /// with `id`, if the id is not valid it does not do anything.
    ///
    /// # Safety
    ///
    /// If you call this function and there is still an instance of the object
    /// alive, the usage of the instance could lead to panics.
    pub unsafe fn decrement_count(&mut self, id: NonZeroUsize) {
        let Some(entry) = self.data.get_mut(&id) else {
            return;
        };

        entry.count -= 1;
    }

    /// Tries to return the count of how many instances are alive
    pub fn alive(&self, id: NonZeroUsize) -> Option<u32> {
        Some(self.data.get(&id)?.count)
    }

    /// Decrements the count and drop the value of the object if count reaches zero
    pub fn drop_instance(&mut self, id: NonZeroUsize) {
        // SAFETY: we are dropping one instance of the object so this is fine
        unsafe {
            self.decrement_count(id);
        }

        if let Some(data) = self.data.get(&id)
            && data.count == 0
        {
            self.data.remove(&id);
        }
    }

    /// Clears the database removing all the underlying values of the object.
    ///
    /// # Safety
    ///
    /// This is unsafe because if you call this function and there is still
    /// instances of objects alive, when they will try to access the memory
    /// after the clear they will panic because the underlying objects no longer
    /// exist but the handles do.
    pub unsafe fn clear(&mut self) {
        self.last_id = NonZeroUsize::new(1).unwrap();
        self.data.clear();
    }
}

impl<T> Default for Database<T> {
    fn default() -> Self {
        Database::new()
    }
}

/// Lock of [`Database`] used in [`idtype!`] macro, to be able to make it static
#[derive(Debug)]
pub struct DatabaseLock<T> {
    inner: LazyLock<RwLock<Database<T>>>,
}

impl<T> DatabaseLock<T> {
    /// Create a new locked database with an empty database.
    pub const fn new() -> DatabaseLock<T> {
        DatabaseLock::with_db(|| RwLock::new(Database::new()))
    }

    /// Create a new locked database
    pub const fn with_db(f: fn() -> RwLock<Database<T>>) -> DatabaseLock<T> {
        DatabaseLock {
            inner: LazyLock::new(f),
        }
    }

    /// Forces the evaluation of the lazy lock
    pub fn eval(&self) {
        LazyLock::force(&self.inner);
    }

    /// Lock for read only uses.
    pub fn lock(&self) -> RwLockReadGuard<'_, Database<T>> {
        self.inner.read().unwrap()
    }

    /// Lock for write and read uses.
    ///
    /// # Note
    ///
    /// If you only read, it is preferred to use [`lock`]
    ///
    /// [`lock`]: DatabaseLock<T>::lock
    pub fn lock_mut(&self) -> RwLockWriteGuard<'_, Database<T>> {
        self.inner.write().unwrap()
    }
}

impl<T> Default for DatabaseLock<T> {
    fn default() -> Self {
        DatabaseLock::new()
    }
}

/// Trait to be able to have the struct syntax, it should not be implemented manually
pub trait InternalType {
    type Internal;
}

#[cfg(test)]
pub mod tests {
    // NOTE: this module is marked as public so that the functions we do not use
    // do no emit the `dead_code` lint

    use std::{error::Error, panic::catch_unwind, ptr, sync::Mutex};

    use super::*;

    idtype! {
        /// A simple test ID with a string.
        pub type TestId(&'static str);

        impl clone_methods for TestId;

        impl PartialEq for TestId;

        impl Eq for TestId;

        impl Hash for TestId;

        /// A second ID type, should not share the database with `TestId`.
        pub type AnotherId(&'static str);

        /// A no-type ID.
        pub type UnitId;
    }

    /// This functions is used to clear the database of `TestId`. To make each
    /// test independent.
    fn clear_test_id_db() {
        // SAFETY: it should be fine because every handle should be dropped at
        // the end of each test.
        unsafe {
            TestId::database().lock_mut().clear();
        }
    }

    /// see docs of `clear_test_id_db`
    fn clear_another_id_db() {
        // SAFETY: it should be fine because every handle should be dropped at
        // the end of each test.
        unsafe {
            AnotherId::database().lock_mut().clear();
        }
    }

    /// see docs of `clear_test_id_db`
    fn clear_unit_id_db() {
        // SAFETY: it should be fine because every handle should be dropped at
        // the end of each test.
        unsafe {
            UnitId::database().lock_mut().clear();
        }
    }

    /// We are using a lock in the tests of idtype because it makes those test
    /// "single-threaded", by default test are run in parallel in Rust and
    /// idtype does not support being used across multiple tests, and even
    /// if they do, those tests must run independently so we use a lock to
    /// ensure that the tests run sequantially, (we don't know the order but
    /// whatever..).
    static LOCK: LazyLock<Mutex<()>> = LazyLock::new(|| Mutex::new(()));

    type TestRes = Result<(), Box<dyn Error>>;

    #[test]
    fn test_basic_creation_and_inspect() -> TestRes {
        let _lock = LOCK.lock()?;
        clear_test_id_db();

        let a = TestId::with_internal("hello");
        assert_eq!(a.alive(), 1);

        a.inspect(|v| {
            assert_eq!(&v, &&"hello");
        });

        assert_eq!(a.alive(), 1);

        Ok(())
    }

    #[test]
    fn test_clone_and_alive_count() -> TestRes {
        let _lock = LOCK.lock()?;
        clear_test_id_db();

        let a = TestId::with_internal("value");
        let b = a.clone();

        assert!(a.object_eq(&b));
        assert_eq!(a.alive(), 2);

        drop(a);
        assert_eq!(b.alive(), 1);

        Ok(())
    }

    #[test]
    fn test_drop_and_alive_cleanup() -> TestRes {
        let _lock = LOCK.lock()?;
        clear_test_id_db();

        let a = TestId::with_internal("temp");
        let id = a.id();
        drop(a);

        let db = TestId::database().lock();
        assert_eq!(db.alive(id), None);

        Ok(())
    }

    #[test]
    fn test_mutation() -> TestRes {
        let _lock = LOCK.lock()?;
        clear_test_id_db();

        let a = TestId::with_internal("hello");

        a.inspect_mut(|v| {
            *v = "world";
        });

        a.inspect(|v| {
            assert_eq!(v, &"world");
        });

        Ok(())
    }

    #[test]
    fn test_try_clone_value_and_clone_val() -> TestRes {
        let _lock = LOCK.lock()?;
        clear_test_id_db();

        let a = TestId::with_internal("abc");

        assert_eq!(a.try_clone_value(), Some("abc"));
        assert_eq!(a.clone_val(), "abc");

        Ok(())
    }

    #[test]
    fn test_multiple_id_types_independence() -> TestRes {
        let _lock = LOCK.lock()?;
        clear_test_id_db();
        clear_another_id_db();

        let a = TestId::with_internal("a");
        let b = AnotherId::with_internal("b");

        assert!(!ptr::eq(TestId::database(), AnotherId::database()));

        a.inspect(|v| assert_eq!(v, &"a"));
        b.inspect(|v| assert_eq!(v, &"b"));

        Ok(())
    }

    #[test]
    fn test_unit_idtype_creation() -> TestRes {
        let _lock = LOCK.lock()?;
        clear_unit_id_db();

        let a = UnitId::with_internal(());

        assert_eq!(a.alive(), 1);

        let b = a.clone();
        assert_eq!(a.alive(), 2);

        assert!(a.object_eq(&b));

        Ok(())
    }

    #[test]
    fn debug_output_contains_fields() -> TestRes {
        let _lock = LOCK.lock()?;
        clear_test_id_db();

        let x = TestId::with_internal("dbg");
        let s = format!("{x:?}");
        assert!(s.contains("TestId"));
        assert!(s.contains("dbg"));
        assert!(s.contains("alive: 1"));

        Ok(())
    }

    #[test]
    fn unsafe_from_raw_does_not_increment_count_but_drop_decrements() -> TestRes {
        let _lock = LOCK.lock()?;
        clear_test_id_db();

        let a = TestId::with_internal("raw");
        let id = a.id();
        let before = a.alive();
        // from_raw doesn’t bump the count
        let b = unsafe { TestId::from_raw(id) };

        assert!(a.object_eq(&b));
        assert_eq!(b.alive(), before);

        // dropping b decrements the count
        drop(b);
        assert_eq!(a.alive(), before.saturating_sub(1));

        Ok(())
    }

    #[test]
    fn unit_id_clone_and_drop_sequence() -> TestRes {
        let _lock = LOCK.lock()?;
        clear_unit_id_db();

        let u1 = UnitId::with_internal(());
        assert_eq!(u1.alive(), 1);

        let u2 = u1.clone();
        let u3 = u2.clone();
        assert_eq!(u1.alive(), 3);

        drop(u2);
        assert_eq!(u1.alive(), 2);

        drop(u3);
        let u1_id = u1.id();
        drop(u1);

        // After all drops, the object should be removed from the DB
        let db = UnitId::database().lock();
        assert_eq!(db.alive(u1_id), None);

        Ok(())
    }

    // NOTE: we don't need the lock here because we are not using any of the
    // global databases the we can run these tests in parallel

    #[test]
    fn database_direct_api_register_and_drop() {
        let mut db: Database<u32> = Database::new();
        assert!(db.data.is_empty());

        let id1 = db.register(10);
        assert_eq!(id1, NonZeroUsize::new(1).unwrap());
        assert_eq!(*db.get(id1).read().unwrap(), 10);
        assert_eq!(db.alive(id1), Some(1));

        // Unsafe increment and decrement
        unsafe { db.increment_count(id1) };
        assert_eq!(db.alive(id1), Some(2));
        unsafe { db.decrement_count(id1) };
        assert_eq!(db.alive(id1), Some(1));

        // drop_instance removes it when count hits zero
        db.drop_instance(id1);
        assert_eq!(db.alive(id1), None);
    }

    #[test]
    fn try_get_and_get_entry_panics_on_invalid_id() {
        let mut db: Database<i32> = Database::new();
        let id = db.register(5);

        // try_get should return Some
        assert!(db.try_get(id).is_some());

        // get_entry with a bad id panics
        let bad_id = NonZeroUsize::new(id.get() + 100).unwrap();
        let result = catch_unwind(|| {
            let _ = db.get_entry(bad_id);
        });
        assert!(result.is_err());
    }
}
