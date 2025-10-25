//! Entities -- strongly-typed, lightweight integer identifiers used
//! throughout the compiler.
//!
//! This module implements a small, local replacement to the old
//! globally-tracked `idtype`-like identifiers. An [`Entity`] is a `Copy`
//! wrapper around an integer (by default `u32`) and carries an associated
//! `Data` type. The important properties of [`Entity`] are:
//!
//! - **Local lifetime**: entities and their data live inside an
//!   [`EntityDb<E>`]. There is no global registry and no reference-count-like
//!   tracking of live handles. Dropping the database drops all associated data.
//! - **Efficient representation**: entities are small (same size as the
//!   primitive) and [`Opt<E>`] provides a same-sized representation for
//!   optional entities by reserving one sentinel value.
//! - **Two map flavours**: use [`SparseMap`] for sparse, non-contiguous ids and
//!   [`TightMap`] for dense, mostly-contiguous ids (backed by a [`Vec`]).
//!
//! The APIs are intentionally small and predictable — this makes them easy
//! to use inside compiler data structures such as control-flow graphs, symbol
//! tables or intermediate representations.
//!
//! # Quick example
//!
//! ```rust
//! # use std::fmt::Debug;
//! # use std::hash::Hash;
//! # use std::marker::PhantomData;
//! # use std::collections::HashMap;
//! use lunc_entity::{entity, EntityDb};
//!
//! // Define a new entity type and its data
//! #[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
//! pub struct MyEntity(u32);
//!
//! // Implement the entity using the helper macro in this crate. In real code
//! // this macro is exported by the crate and you call it from user code.
//! entity!(MyEntity, String);
//!
//! // Create a small database, insert one entity and read its data.
//! let mut db = EntityDb::<MyEntity>::new();
//! let e = db.create("hello".to_string());
//! assert_eq!(db.get(e), &"hello".to_string());
//! ```

use std::{collections::HashMap, fmt::Debug, hash::Hash, marker::PhantomData, mem};

/// An entity is a tiny, `Copy` identifier used across the compiler.
///
/// Think of an `Entity` as a type-safe wrapper around a primitive integer
/// (commonly `u32`). Each `Entity` implementation must declare the associated
/// `Data` type, that is the type stored inside an `EntityDb<E>` for that entity
/// — and provide a `RESERVED` value which is used as a sentinel for `Opt<E>`.
///
/// Implementations are typically generated with the `entity!` macro.
///
/// # Example
///
/// ```rust
/// # use std::fmt::Debug;
/// # use std::hash::Hash;
///
/// use lunc_entity::{entity, Entity};
///
/// #[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
/// pub struct Foo(u32);
///
/// entity!(Foo, ());
///
/// let x = Foo::new(0);
/// assert_eq!(x.index(), 0);
/// ```
pub trait Entity: Debug + Copy + PartialEq + Eq + Hash {
    /// The data associated with this entity. [`EntityDb<E>`] stores values of
    /// this type.
    type Data: Sized;

    /// A reserved value that is illegal for normal entities. This sentinel is
    /// used by [`Opt<E>`] to represent [`None`] without increasing size.
    ///
    /// The [`entity!`] macro defaults this to `Self(u32::MAX)` for wrapper
    /// structs around `u32`.
    ///
    /// [`None`]: Opt::None
    const RESERVED: Self;

    /// Create a new `Entity` with the provided `id`.
    ///
    /// # Panics
    ///
    /// Panics if `id` does not fit the underlying representation or if it
    /// would equal [`Entity::RESERVED`].
    fn new(id: usize) -> Self;

    /// Returns the underlying zero-based index of this [`Entity`].
    fn index(self) -> usize;

    /// Is this the reserved sentinel value?
    #[inline(always)]
    fn is_reserved(self) -> bool {
        self == Entity::RESERVED
    }
}

/// Convenience macro to implement an [`Entity`] for a simple wrapper type (like
/// `struct MyE(u32);`).
///
/// It fills in `Entity::Data`, `RESERVED` and the `new`/`index` helpers.
///
/// # Example
///
/// ```rust
/// use lunc_entity::entity;
///
/// #[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
/// pub struct MyEntity(u32);
/// entity!(MyEntity, i32);
/// ```
#[macro_export]
macro_rules! entity {
    ($entity:ty, $entity_data:ty) => {
        impl $crate::Entity for $entity {
            type Data = $entity_data;

            const RESERVED: Self = Self(u32::MAX);

            #[track_caller]
            fn new(id: usize) -> Self {
                let id: u32 = id.try_into().unwrap();

                let entity = Self(id);

                if $crate::Entity::is_reserved(entity) {
                    panic!("invalid id");
                }

                entity
            }

            fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

/// [`EntityDb<E>`] stores the primary data associated with an entity type `E`,
/// [`Entity::Data`].
///
/// Internally it is just a `Vec<E::Data>` and entities are the indices into
/// that vector. Use [`EntityDb::create`] to allocate a new entity and push its
/// associated data. Data is dropped only when the [`EntityDb`] itself is dropped.
///
/// # Example
///
/// ```rust
/// use lunc_entity::{entity, EntityDb};
///
/// #[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
/// pub struct Id(u32);
/// entity!(Id, String);
///
/// let mut db = EntityDb::<Id>::new();
/// let id = db.create("value".to_string());
/// assert!(db.is_valid(id));
/// assert_eq!(db.get(id), &"value".to_string());
/// ```
#[derive(Debug, Clone)]
pub struct EntityDb<E: Entity> {
    /// the data being stored
    elems: Vec<E::Data>,
    /// last id given to an entity
    last_id: usize,
    _e: PhantomData<fn(E) -> E::Data>,
}

impl<E: Entity> EntityDb<E> {
    /// Create a new, empty [`EntityDb`].
    pub fn new() -> EntityDb<E> {
        EntityDb {
            elems: Vec::new(),
            last_id: 0,
            _e: PhantomData,
        }
    }

    /// Create a new [`EntityDb`] with capacity reserved for `cap` elements.
    pub fn with_capacity(cap: usize) -> EntityDb<E> {
        EntityDb {
            elems: Vec::with_capacity(cap),
            ..EntityDb::new()
        }
    }

    /// Allocate a new entity and store `data` for it. The returned value is a
    /// fresh `E` whose index corresponds to the pushed slot.
    pub fn create(&mut self, data: E::Data) -> E {
        let entity = E::new(self.last_id);
        self.last_id += 1;

        self.elems.push(data);

        entity
    }

    /// Checks whether `entity` refers to a slot inside this database.
    pub fn is_valid(&self, entity: E) -> bool {
        entity.index() < self.elems.len()
    }

    /// Try to get a reference to the data for `entity`.
    pub fn try_get(&self, entity: E) -> Option<&E::Data> {
        self.elems.get(entity.index())
    }

    /// Mutable version of `try_get`.
    pub fn try_get_mut(&mut self, entity: E) -> Option<&mut E::Data> {
        self.elems.get_mut(entity.index())
    }

    /// Get the data for `entity` and panic if it is invalid.
    ///
    /// This is a convenience wrapper around `try_get`.
    #[inline(always)]
    pub fn get(&self, entity: E) -> &E::Data {
        self.try_get(entity).unwrap()
    }

    /// Mutable `get`.
    #[inline(always)]
    pub fn get_mut(&mut self, entity: E) -> &mut E::Data {
        self.try_get_mut(entity).unwrap()
    }

    /// Number of entities allocated in this database.
    #[inline(always)]
    pub fn count(&self) -> usize {
        self.elems.len()
    }

    /// Is the database empty?
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.count() == 0
    }
}

impl<E: Entity> Default for EntityDb<E> {
    fn default() -> Self {
        EntityDb::new()
    }
}

/// A [`SparseMap`] associates arbitrary values to [`Entity`]. Internally backed
/// by an hash map and suitable for sparse, non-contiguous entity id sets.
///
/// Prefer `SparseMap` when entity ids will have many gaps or when allocations
/// are occasional.
///
/// # Example
///
/// ```rust
/// use lunc_entity::{entity, SparseMap, Entity};
///
/// #[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
/// pub struct Node(u32);
/// entity!(Node, ());
///
/// let mut map = SparseMap::<Node, i32>::new();
/// let n = Node::new(10);
/// map.insert(n, 42);
/// assert_eq!(map.get(n), Some(&42));
/// assert!(map.contains_entity(n));
/// ```
#[derive(Debug, Clone)]
pub struct SparseMap<E: Entity, V> {
    elems: HashMap<usize, V>,
    _e: PhantomData<fn(E) -> V>,
}

impl<E: Entity, V> SparseMap<E, V> {
    /// Create a new empty [`SparseMap`].
    pub fn new() -> SparseMap<E, V> {
        SparseMap {
            elems: HashMap::new(),
            _e: PhantomData,
        }
    }

    /// Insert a value for `entity`, replacing any previous value.
    pub fn insert(&mut self, entity: E, value: V) {
        self.elems.insert(entity.index(), value);
    }

    /// Get the value associated with `entity`.
    pub fn get(&self, entity: E) -> Option<&V> {
        self.elems.get(&entity.index())
    }

    /// Mutable `get`.
    pub fn get_mut(&mut self, entity: E) -> Option<&mut V> {
        self.elems.get_mut(&entity.index())
    }

    /// Clear the map.
    pub fn clear(&mut self) {
        self.elems.clear();
    }

    /// Does this map contain a value for `entity`?
    pub fn contains_entity(&self, entity: E) -> bool {
        self.get(entity).is_some()
    }
}

impl<E: Entity, V> Default for SparseMap<E, V> {
    fn default() -> Self {
        SparseMap::new()
    }
}

/// [`TightMap`] associates additional data to entities using a contiguous
/// `Vec`.
///
/// Use this map when the set of keys is dense or mostly contiguous. On
/// insertions [`TightMap`] will extend its internal `Vec` and fill holes with a
/// cloned `default` value.
///
/// # Note
///
/// `V` must implement [`Clone`] because the default value is cloned to fill new
/// slots. When `remove` is called, the slot is reset back to the default value
/// and the previous value is returned.
///
/// # Example
///
/// ```rust
/// use lunc_entity::{entity, TightMap, Entity};
///
/// #[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
/// pub struct Reg(u32);
/// entity!(Reg, ());
///
/// // default value is 0
/// let mut tm = TightMap::<Reg, i32>::new();
/// let r = Reg::new(2);
/// tm.insert(r, 7);
/// assert_eq!(tm.get(r), Some(&7));
/// ```
#[derive(Debug, Clone)]
pub struct TightMap<E: Entity, V: Clone> {
    _e: PhantomData<fn(E) -> V>,
    /// the stored elements
    elems: Vec<V>,
    /// default value used to fill holes
    default: V,
    /// occupancy bitmap, used for Debug checks
    #[cfg(debug_assertions)]
    occupied: Vec<bool>,
}

impl<E: Entity, V: Clone> TightMap<E, V> {
    /// Create a new [`TightMap`] using [`V::default()`] as the default.
    ///
    /// [`V::default()`]: Default::default
    pub fn new() -> TightMap<E, V>
    where
        V: Default,
    {
        TightMap::with_default(Default::default())
    }

    /// Create a new [`TightMap`] with the provided `default` value.
    pub fn with_default(default: V) -> TightMap<E, V> {
        TightMap {
            _e: PhantomData,
            elems: Vec::new(),
            default,
            #[cfg(debug_assertions)]
            occupied: Vec::new(),
        }
    }

    /// Ensure the internal vectors are at least `index + 1` long.
    fn ensure_index(&mut self, index: usize) {
        if index >= self.elems.len() {
            let to_add = index + 1 - self.elems.len();
            self.elems
                .extend(std::iter::repeat_with(|| self.default.clone()).take(to_add));

            #[cfg(debug_assertions)]
            {
                self.occupied.extend(std::iter::repeat_n(false, to_add));
            }
        }
    }

    /// Insert a value for `entity`, expanding the underlying `Vec` if
    /// necessary. This overwrites any previous value.
    pub fn insert(&mut self, entity: E, value: V) {
        self.ensure_index(entity.index());

        // put value into slot, mark occupied
        self.elems[entity.index()] = value;

        #[cfg(debug_assertions)]
        {
            self.occupied[entity.index()] = true;
        };
    }

    /// Remove the value for `entity`. Returns the previous value (which may be
    /// the default), or [`None`] if the index is out of range.
    pub fn remove(&mut self, entity: E) -> Option<V> {
        let idx = entity.index();

        if idx < self.elems.len() {
            #[cfg(debug_assertions)]
            {
                self.occupied[idx] = false;
            };

            let prev = mem::replace(&mut self.elems[idx], self.default.clone());

            Some(prev)
        } else {
            None
        }
    }

    /// Get the value for `entity`.
    pub fn get(&self, entity: E) -> Option<&V> {
        self.elems.get(entity.index())
    }

    /// Mutable `get`.
    pub fn get_mut(&mut self, entity: E) -> Option<&mut V> {
        self.elems.get_mut(entity.index())
    }

    /// Clear the map contents.
    pub fn clear(&mut self) {
        self.elems.clear();
    }
}

impl<E: Entity, V: Clone + Default> Default for TightMap<E, V> {
    fn default() -> Self {
        TightMap::new()
    }
}

/// [`Opt<E>`] is an optimized [`Option<E>`]: it stores an [`Entity`] but reuses
/// the [`Entity::RESERVED`] sentinel to represent `None`. This ensures `Opt<E>`
/// is the same size as `E`.
///
/// # Note
///
/// Constructing [`Opt::Some`] with the reserved value will trigger a panic in
/// debug mode (in release mod it's just an Undefined Behavior).
///
/// # Example
///
/// ```rust
/// use lunc_entity::{entity, Opt, Entity};
///
/// #[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
/// pub struct Slot(u32);
/// entity!(Slot, ());
///
/// // None variant:
/// let mut o: Opt<Slot> = Opt::None();
/// assert!(o.is_none());
///
/// // Some variant:
/// let some = Opt::Some(Slot::new(1));
/// assert!(some.is_some());
/// assert_eq!(some.unwrap().index(), 1);
/// ```
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Opt<E: Entity>(E);

impl<E: Entity> Opt<E> {
    /// Construct a [`Some(entity)`]. Panics (in debug mode) if `entity` is the
    /// reserved Entity.
    #[allow(non_snake_case)]
    pub fn Some(entity: E) -> Opt<E> {
        debug_assert_ne!(
            entity,
            E::RESERVED,
            "Cannot make an Opt<E> from the reserved value."
        );

        Opt(entity)
    }

    /// Construct a `None` option.
    #[allow(non_snake_case)]
    pub const fn None() -> Opt<E> {
        Opt(E::RESERVED)
    }

    /// Is this `None`?
    pub fn is_none(&self) -> bool {
        self.0.is_reserved()
    }

    /// Is this `Some`?
    pub fn is_some(&self) -> bool {
        !self.0.is_reserved()
    }

    /// Convert to a standard `Option<E>`.
    pub fn expand(self) -> Option<E> {
        if self.is_none() { None } else { Some(self.0) }
    }

    /// Map an `Opt<E>` to `Option<U>` using the provided function.
    pub fn map<U>(self, f: impl FnOnce(E) -> U) -> Option<U> {
        self.expand().map(f)
    }

    /// Unwrap the contained `Entity` or panic if `None`.
    #[track_caller]
    pub fn unwrap(self) -> E {
        self.expand().unwrap()
    }

    /// Take the stored entity, leaving a `None` in its place.
    pub fn take(&mut self) -> Opt<E> {
        mem::replace(self, Self::None())
    }
}
