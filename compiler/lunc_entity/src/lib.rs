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

use std::{
    fmt::{self, Debug, Display},
    hash::{Hash, Hasher},
    io,
    marker::PhantomData,
    mem,
};

use indexmap::{IndexMap, IndexSet};
use lunc_utils::{
    impl_pdump,
    pretty::{PrettyCtxt, PrettyDump},
};

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

    /// Converts this entity to an [`AnyId`].
    fn to_any(self) -> AnyId {
        AnyId(self.index() as u32)
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
#[derive(Debug, Clone, Hash)]
pub struct EntityDb<E: Entity> {
    /// the data being stored
    elems: Vec<E::Data>,
    /// phantom data so that E is actually used
    _e: PhantomData<fn(E) -> E::Data>,
}

impl<E: Entity> EntityDb<E> {
    /// Create a new, empty [`EntityDb`].
    pub fn new() -> EntityDb<E> {
        EntityDb {
            elems: Vec::new(),
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
        let entity = E::new(self.elems.len());

        self.elems.push(data);

        entity
    }

    /// Create a new entity with data the default value of `E::Data`.
    pub fn create_default(&mut self) -> E
    where
        E::Data: Default,
    {
        self.create(E::Data::default())
    }

    /// Create a new entity with `ctor` that takes the id as argument, and
    /// returns the data to associate with the entity. This method returns the
    /// entity created.
    pub fn create_with(&mut self, ctor: impl FnOnce(E) -> E::Data) -> E {
        let entity = E::new(self.elems.len());
        self.create(ctor(entity));

        entity
    }

    /// Creates `count` new entities with the data returned by `ctor`, returns a
    /// Vector containing all created entities.
    ///
    /// `ctor` takes to arguments:
    /// - the entity being created as the first param
    /// - the index, e.g: when `ctor` is called for the first entity, the
    ///   `index == 0`, for the second entity created `index == 1` etc..
    pub fn create_many(
        &mut self,
        mut ctor: impl FnMut(E, usize) -> E::Data,
        count: usize,
    ) -> Vec<E> {
        self.elems.reserve(count);
        let mut entities = Vec::with_capacity(count);

        for i in 0..count {
            let entity = E::new(self.elems.len());
            entities.push(entity);
            let data = ctor(entity, i);
            let res = self.create(data);

            debug_assert_eq!(entity, res);
        }

        entities
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

    /// Returns an iterator on the data of the entities.
    ///
    /// The iterator yields all the data in the order they were created.
    pub fn data_iter(&self) -> impl Iterator<Item = &E::Data> {
        self.elems.iter()
    }

    /// Returns an iterator over the stored entities handles.
    ///
    /// The iterator yields all the data in the order they were created.
    pub fn entity_iter(&self) -> impl ExactSizeIterator<Item = E> + use<E> {
        (0..self.elems.len()).map(|i| E::new(i))
    }

    /// Returns an iterator on the entity and its associated data.
    ///
    /// The iterator yields all the data in the order they were created.
    pub fn full_iter(&self) -> impl Iterator<Item = (E, &E::Data)> {
        self.elems
            .iter()
            .enumerate()
            .map(|(id, data)| (E::new(id), data))
    }

    /// Get the last entity we created
    pub fn last(&self) -> E {
        E::new(self.elems.len() - 1)
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
    elems: IndexMap<usize, V>,
    _e: PhantomData<fn(E) -> V>,
}

impl<E: Entity, V> SparseMap<E, V> {
    /// Create a new empty [`SparseMap`].
    pub fn new() -> SparseMap<E, V> {
        SparseMap {
            elems: IndexMap::new(),
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

    /// Is this map empty?
    pub fn is_empty(&self) -> bool {
        self.elems.is_empty()
    }

    /// Returns an iterator on the entity and its associated data.
    pub fn iter(&self) -> impl Iterator<Item = (E, &V)> {
        self.elems.iter().map(|(id, data)| (E::new(*id), data))
    }
}

impl<E: Entity, V> Default for SparseMap<E, V> {
    fn default() -> Self {
        SparseMap::new()
    }
}

impl<E: Entity, V: Hash> Hash for SparseMap<E, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.elems.len().hash(state);

        for pair in self.iter() {
            pair.hash(state);
        }
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

/// A set of entities, used to store only one copy of an entity. It should be
/// used instead of a `Vec<Entity>` when you know that you want only one entry by entity.
#[derive(Debug, Clone)]
pub struct EntitySet<E: Entity> {
    elems: IndexSet<E>,
}

impl<E: Entity> EntitySet<E> {
    /// Create a new empty entity set.
    pub fn new() -> EntitySet<E> {
        EntitySet {
            elems: IndexSet::new(),
        }
    }

    /// Insert a new entity in the set.
    #[inline]
    pub fn insert(&mut self, entity: E) {
        self.elems.insert(entity);
    }

    /// Returns `true` if the entity is in the set.
    #[inline]
    pub fn exists(&self, entity: E) -> bool {
        self.elems.contains(&entity)
    }

    /// Clear the set
    #[inline]
    pub fn clear(&mut self) {
        self.elems.clear();
    }

    /// Count of how many entities are stored in the set.
    #[inline]
    pub fn len(&mut self) -> usize {
        self.elems.len()
    }

    /// Returns `true` if the set is empty.
    #[inline]
    pub fn is_empty(&mut self) -> bool {
        self.len() == 0
    }

    /// Get an iterator over the entries of the set, it is ensured to be in the
    /// order of insertion.
    pub fn iter(&self) -> impl Iterator<Item = &E> {
        self.elems.iter()
    }
}

impl<E: Entity> Default for EntitySet<E> {
    fn default() -> Self {
        EntitySet::new()
    }
}

impl<Ex: Clone, E: Entity + PrettyDump<Ex>> PrettyDump<Ex> for EntitySet<E> {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &Ex) -> io::Result<()> {
        ctx.pretty_list(None, extra)
            .disable_nl()
            .items(self.iter())
            .finish()
    }
}

impl<E: Entity> Hash for EntitySet<E> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for entity in self.iter() {
            entity.hash(state);
        }
    }
}

/// Any entity, can be downcast to anything that implements [`Entity`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AnyId(u32);

impl AnyId {
    /// Create a new any id from the entity, ensured to be a valid any id.
    pub fn upcast<E: Entity>(entity: E) -> AnyId {
        entity.to_any()
    }

    /// Downcast this any id to `E`.
    ///
    /// # Safety
    ///
    /// You should only downcast when you are 100% that it will be a valid entity.
    pub fn downcast<E: Entity>(self) -> E {
        E::new(self.0 as usize)
    }
}

impl Display for AnyId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AnyId({})", self.0)
    }
}

impl_pdump! {
    AnyId,
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
/// let mut o: Opt<Slot> = Opt::None;
/// assert!(o.is_none());
///
/// // Some variant:
/// let some = Opt::Some(Slot::new(1));
/// assert!(some.is_some());
/// assert_eq!(some.unwrap().index(), 1);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Opt<E: Entity>(E);

impl<E: Entity> Opt<E> {
    /// Construct a `Some(entity)`. Panics (in debug mode) if `entity` is the
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
    #[allow(non_upper_case_globals)]
    pub const None: Opt<E> = Opt(E::RESERVED);

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
        mem::replace(self, Self::None)
    }
}

impl<E: Entity> Debug for Opt<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_some() {
            f.debug_tuple("Some").field(&self.0).finish()
        } else {
            f.debug_struct("None").finish()
        }
    }
}

impl<E: Entity + Display> Display for Opt<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_some() {
            Display::fmt(&self.0, f)
        } else {
            write!(f, "None")
        }
    }
}

impl<E: PrettyDump<Ex> + Entity, Ex> PrettyDump<Ex> for Opt<E> {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &Ex) -> io::Result<()> {
        self.expand().try_dump(ctx, extra)
    }
}

impl<E: Entity> From<Option<E>> for Opt<E> {
    fn from(value: Option<E>) -> Self {
        match value {
            Some(e) => Opt::Some(e),
            None => Opt::None,
        }
    }
}

pub mod private {
    pub trait Sealed {}

    impl<E> Sealed for Option<E> {}
}

pub trait OptionExt<E: Entity>: private::Sealed {
    /// Reduces the `Option<E>` to an `Opt<E>`, where `E` is an [Entity].
    fn shorten(self) -> Opt<E>;
}

impl<E: Entity> OptionExt<E> for Option<E> {
    fn shorten(self) -> Opt<E> {
        Opt::from(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Create simple test entities with different associated Data types.
    #[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
    pub struct TestEntityA(u32);
    entity!(TestEntityA, String);

    #[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
    pub struct TestEntityB(u32);
    entity!(TestEntityB, i32);

    #[test]
    fn entity_new_and_index() {
        let e0 = TestEntityA::new(0);
        assert_eq!(e0.index(), 0);

        let e7 = TestEntityA::new(7);
        assert_eq!(e7.index(), 7);
        assert!(e0 != e7);
    }

    #[test]
    #[should_panic]
    fn entity_new_reserved_panics() {
        // The macro sets RESERVED = Self(u32::MAX) so creating with that id panics.
        let _ = TestEntityA::new(u32::MAX as usize);
    }

    #[test]
    fn entity_db_create_get_is_valid_count() {
        let mut db = EntityDb::<TestEntityA>::new();
        assert!(db.is_empty());
        assert_eq!(db.count(), 0);

        let a = db.create("first".to_string());
        // The library intends each create to produce a distinct index.
        // If implementation forgot to increment a last_id counter this assertion
        // will catch it.
        assert!(db.is_valid(a));
        assert_eq!(db.count(), 1);
        assert_eq!(db.get(a), "first");

        let b = db.create("second".to_string());
        assert!(db.is_valid(b));
        assert_eq!(db.count(), 2);
        // ensure values are stored and retrievable independently
        assert_eq!(db.get(a), "first");
        assert_eq!(db.get(b), "second");

        // try_get on out-of-range entity returns None
        let out_of_range = TestEntityA::new(1000);
        assert_eq!(db.try_get(out_of_range), None);
    }

    #[test]
    fn entity_db_get_mut() {
        let mut db = EntityDb::<TestEntityA>::new();
        let e = db.create("one".to_string());
        {
            let s = db.get_mut(e);
            s.push_str(":mutated");
        }
        assert_eq!(db.get(e), "one:mutated");
    }

    #[test]
    fn sparse_map_basic_ops() {
        let mut m = SparseMap::<TestEntityA, usize>::new();
        let e1 = TestEntityA::new(10);
        assert!(!m.contains_entity(e1));
        m.insert(e1, 123);
        assert!(m.contains_entity(e1));
        assert_eq!(m.get(e1), Some(&123));

        // mutable access
        if let Some(v) = m.get_mut(e1) {
            *v += 7;
        }
        assert_eq!(m.get(e1), Some(&130));

        m.clear();
        assert!(!m.contains_entity(e1));
        assert_eq!(m.get(e1), None);
    }

    #[test]
    fn tight_map_insert_get_remove() {
        // use i32 default value of 0
        let mut tm = TightMap::<TestEntityB, i32>::with_default(0);

        let e2 = TestEntityB::new(2);
        // Initially out of range
        assert_eq!(tm.get(e2), None);

        tm.insert(e2, 55);
        assert_eq!(tm.get(e2), Some(&55));

        // insert at a higher index fills holes with default clone
        let e5 = TestEntityB::new(5);
        tm.insert(e5, 99);
        assert_eq!(tm.get(e5), Some(&99));
        // earlier indices that were never assigned should equal default (0)
        assert_eq!(tm.get(TestEntityB::new(0)), Some(&0));

        // remove returns previous value and resets slot to default
        let prev = tm.remove(e5);
        assert_eq!(prev, Some(99));
        assert_eq!(tm.get(e5), Some(&0));

        // removing an index that was never allocated returns None
        let not_alloc = TestEntityB::new(1000);
        assert_eq!(tm.remove(not_alloc), None);
    }

    #[test]
    fn tight_map_get_mut_and_clear() {
        let mut tm = TightMap::<TestEntityB, i32>::with_default(-1);
        let e3 = TestEntityB::new(3);
        tm.insert(e3, 7);

        if let Some(v) = tm.get_mut(e3) {
            *v = 42;
        }
        assert_eq!(tm.get(e3), Some(&42));

        tm.clear();
        assert_eq!(tm.get(e3), None);
    }

    #[test]
    fn tight_map_default_new_works() {
        // requires V: Default
        let mut tm = TightMap::<TestEntityB, i32>::new();
        // default is i32::default() == 0
        let e1 = TestEntityB::new(1);
        tm.insert(e1, 11);
        assert_eq!(tm.get(e1), Some(&11));
    }

    #[test]
    fn opt_some_none_and_expand() {
        // None
        let none_opt: Opt<TestEntityA> = Opt::None;
        assert!(none_opt.is_none());
        assert!(!none_opt.is_some());
        assert_eq!(none_opt.expand(), None);

        // Some
        let some = Opt::Some(TestEntityA::new(3));
        assert!(some.is_some());
        assert!(!some.is_none());
        assert_eq!(some.expand().unwrap().index(), 3);

        // unwrap for Some
        assert_eq!(Opt::Some(TestEntityA::new(4)).unwrap().index(), 4);

        // map
        let mapped = Opt::Some(TestEntityA::new(5)).map(|e| e.index() * 2);
        assert_eq!(mapped, Some(10));

        // take
        let mut xx = Opt::Some(TestEntityA::new(6));
        let taken = xx.take();
        assert!(taken.is_some());
        assert!(xx.is_none());
    }

    // debug-only test: creating Opt::Some with the reserved value triggers a debug assertion.
    // Only run this test when debug assertions are enabled.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn opt_some_with_reserved_panics_in_debug() {
        let reserved = TestEntityA::RESERVED;
        let _ = Opt::Some(reserved);
    }

    // debug-only test: ensure we can create the RESERVED sentinel via Opt::None
    #[test]
    fn opt_none_is_reserved_under_the_hood() {
        let none: Opt<TestEntityA> = Opt::None;
        assert!(none.is_none());
        // expanding should yield None
        assert_eq!(none.expand(), None);
    }
}
