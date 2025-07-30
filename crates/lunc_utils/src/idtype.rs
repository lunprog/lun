//! Id types, are types that have the size of a [`usize`], and so benefit from
//! a super lightwight [`Clone`] and are even [`Copy`], while being global. They
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
//! let a = TestId::new("A");
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
                let db = Self::database().lock();

                let entry = db.get_entry(self.0);

                let guard = entry.value.read().unwrap();

                <<Self as $crate::idtype::InternalType>::Internal as std::hash::Hash>::hash(&*guard, state);
            }
        }

        $crate::idtype! { $( $rest )* }
    };

    {impl PartialEq for $name:ident; $($rest:tt)*} => {
        impl PartialEq for $name {
            #[doc = concat!("Equality of two [`", stringify!($name), "`].")]
            ///
            /// They are equal, only if their internal values are equal, even if
            /// they are not refering to the same object.
            ///
            /// If you want to know if two instances refer to the same object
            /// see
            #[doc = concat!("[`", stringify!($name), "::object_eq`]")]
            fn eq(&self, other: &Self) -> bool {
                // NOTE: we cannot use the `object_eq` method here because we
                // don't know if the internal value implements `Eq`
                let db = Self::database().lock();

                let self_entry = db.get_entry(self.0);

                let self_guard = self_entry.value.read().unwrap();

                let other_entry = db.get_entry(other.0);

                let other_guard = other_entry.value.read().unwrap();

                PartialEq::eq(&*self_guard, &*other_guard)
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

            impl $name {
                $(

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

                )*
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
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! internal_idtype {
    (attr = [ $( $attr:meta , )* ], vis = $vis:vis, name = $name:ident, T = $T:ty,) => {
        $crate::idtype::concat_idents!(database_name = DATABASE_, $name {
            $( #[$attr] )*
            $vis struct $name(usize);
            // TODO(URGENT): change from `usize` to `NonZeroUsize`, so that `Option<Idtype>` is still the size of `usize`

            #[allow(non_upper_case_globals)]
            pub(crate) static database_name: $crate::idtype::DatabaseLock<$T> = $crate::idtype::DatabaseLock::new();

            impl $name {
                /// Creates a new [`
                #[doc = stringify!($name)]
                ///`] with the value.
                ///
                /// # Example
                ///
                /// ```
                /// # use lunc_utils::idtype;
                /// idtype! {
                ///     type TestId(usize);
                /// }
                ///
                /// let a = TestId::new(12);
                ///
                /// a.inspect(|id| {
                ///     assert_eq!(*id, 12);
                /// });
                /// ```
                pub fn new(value: $T) -> Self {
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
                /// instanciated can lead to panics, or if the id's object is
                /// initialized, it can lead to use of an object that will die
                /// before this typeid. **TLDR: use it if you know what you
                /// do.**
                pub const unsafe fn from_raw(id: usize) -> Self {
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
                /// let a = TestId::new(12);
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
                /// let a = TestId::new(12);
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
                /// `id` of an instance is equal to something. The `id` is
                /// not guaranteed to be persistent in any fashion, accross
                /// versions, accross runs, etc.. You can just rely on the `id`
                /// to be the same accross to instances of the same object like
                /// in the following example.
                ///
                /// # Example
                ///
                /// ```
                /// # use lunc_utils::idtype;
                /// idtype! {
                ///     type TestId;
                /// }
                ///
                /// let a = TestId::new(());
                ///
                /// // SAFETY: this is safe for the example but not for real
                /// // use cases, because we did not increment the count of
                /// // instances alive but whatever
                /// let b = unsafe { TestId::from_raw(a.id()) };
                ///
                /// assert!(a.object_eq(&b));
                /// ```
                pub fn id(&self) -> usize {
                    self.0
                }

                /// Are these instances refering to the same object?
                ///
                /// # Example
                ///
                /// ```
                /// # use lunc_utils::idtype;
                /// idtype! {
                ///     type TestId;
                /// }
                ///
                /// let a = TestId::new(());
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
                /// let a = TestId::new(());
                /// let b = a.clone();
                ///
                /// assert_eq!(a.alive(), 2);
                /// ```
                pub fn alive(&self) -> usize {
                    let db = Self::database().lock();

                    db.alive(self.0).unwrap() as usize
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
    // TODO: it is maybe possible to use NonZeroU32 here.
    pub count: u32,
}

/// Database of idtype, for type `T`.
#[derive(Debug)]
pub struct Database<T> {
    data: HashMap<usize, Entry<T>>,
    last_id: usize,
}

impl<T> Database<T> {
    /// Create a new empty database
    pub fn new() -> Database<T> {
        Database {
            data: HashMap::new(),
            last_id: 0,
        }
    }

    /// Register a new object of this type and returns it's id.
    pub fn register(&mut self, value: T) -> usize {
        let id = self.last_id;
        self.last_id += 1;

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
    pub fn try_get(&self, id: usize) -> Option<&RwLock<T>> {
        self.data.get(&id).map(|entry| &entry.value)
    }

    /// Gets the value at the given id
    ///
    /// # Panic
    ///
    /// It panics if the id is not valid
    pub fn get(&self, id: usize) -> &RwLock<T> {
        self.try_get(id).expect("invalid id")
    }

    /// Gets the entry of the id
    ///
    /// # Panic
    ///
    /// It panics if the id is not valid
    pub fn get_entry(&self, id: usize) -> &Entry<T> {
        self.data.get(&id).expect("invalid id")
    }

    /// Tries to increments the count of currently alive instance of the object
    /// with `id`, if the id is not valid it does not do anything.
    ///
    /// # Safety
    ///
    /// If you call this function but the typeid was not cloned, it can lead to the
    /// object not being dropped, if the database is static
    pub unsafe fn increment_count(&mut self, id: usize) {
        let Some(entry) = self.data.get_mut(&id) else {
            return;
        };

        entry.count += 1;
    }

    /// Tries to decrements the count of currently alive instance of the object
    /// with `id`, if the id is not valid it does not do anything.
    ///
    /// # Safety
    ///
    /// If you call this function and there is still an instance of the object
    /// alive, the usage of the instance could lead to panics.
    pub unsafe fn decrement_count(&mut self, id: usize) {
        let Some(entry) = self.data.get_mut(&id) else {
            return;
        };

        entry.count -= 1;
    }

    /// Tries to return the count of how many instances are alive
    pub fn alive(&self, id: usize) -> Option<u32> {
        Some(self.data.get(&id)?.count)
    }

    /// Decrements the count and drop the value of the object if count reaches zero
    pub fn drop_instance(&mut self, id: usize) {
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
    /// If you only read, it is preffered to use [`lock`]
    ///
    /// [`lock`]: DatabaseLock<T>::lock
    pub fn lock_mut(&self) -> RwLockWriteGuard<'_, Database<T>> {
        self.inner.write().unwrap()
    }
}

/// Trait to be able to have the struct syntax, it should not be implemented manually
pub trait InternalType {
    type Internal;
}
