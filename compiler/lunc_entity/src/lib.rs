//! Entities, described in [#56].
//!
//! [#56]: https://github.com/lunprog/lun/issues/56
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use std::{collections::HashMap, fmt::Debug, hash::Hash, marker::PhantomData, mem};

/// An entity is a type that is a wrapper around an integer primitive and
/// cost-less clone/copy, used across the compiler.
pub trait Entity: Debug + Copy + PartialEq + Eq + Hash {
    /// The data that the entity stores.
    type Data: Sized;

    /// A reserved value, an id that is illegal for the entity to take, by
    /// default it should always be `u32::MAX`.
    const RESERVED: Self;

    /// Create a new [`Entity`] with the given `id`.
    ///
    /// # Panic
    ///
    /// This function will panic if the id is not representable: outside of the
    /// range of the underlying type or if it is the [`Entity::RESERVED`].
    fn new(id: usize) -> Self;

    /// Returns the underlying id of the [`Entity`], starts always at zero.
    fn index(self) -> usize;

    /// Is this entity using the reserved id?
    #[inline(always)]
    fn is_reserved(self) -> bool {
        self == Entity::RESERVED
    }
}

/// Implement the [`Entity`] trait for `$entity` with `$entity_data` as the data
/// type.
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

/// [`Entity`] database, this is where the associated data of an entity is
/// stored.
#[derive(Debug, Clone)]
pub struct EntityDb<E: Entity> {
    /// the data being stored
    elems: Vec<E::Data>,
    /// last id given to an entity
    last_id: usize,
    _e: PhantomData<fn(E) -> E::Data>,
}

impl<E: Entity> EntityDb<E> {
    /// Create a new [`EntityDb`].
    pub fn new() -> EntityDb<E> {
        EntityDb {
            elems: Vec::new(),
            last_id: 0,
            _e: PhantomData,
        }
    }

    /// Create a new [`EntityDb`] with at least `cap`, pre-allocated.
    pub fn with_capacity(cap: usize) -> EntityDb<E> {
        EntityDb {
            elems: Vec::with_capacity(cap),
            ..EntityDb::new()
        }
    }

    /// Create a new entity with the given `data`.
    pub fn create(&mut self, data: E::Data) -> E {
        let entity = E::new(self.last_id);

        self.elems.push(data);

        entity
    }

    /// Checks if `entity` is valid in this database.
    pub fn is_valid(&self, entity: E) -> bool {
        entity.index() < self.elems.len()
    }

    /// Tries to get the data associated with `entity`.
    pub fn try_get(&self, entity: E) -> Option<&E::Data> {
        self.elems.get(entity.index())
    }

    /// Tries to get the data associated with `entity`, but mutable version.
    pub fn try_get_mut(&mut self, entity: E) -> Option<&mut E::Data> {
        self.elems.get_mut(entity.index())
    }

    /// Get the data associated with `entity`.
    ///
    /// # Panic
    ///
    /// This function may panic if `entity` is not valid.
    #[inline(always)]
    pub fn get(&self, entity: E) -> &E::Data {
        self.try_get(entity).unwrap()
    }

    /// Get the data associated with `entity`, but mutable version.
    ///
    /// # Panic
    ///
    /// This function may panic if `entity` is not valid.
    #[inline(always)]
    pub fn get_mut(&mut self, entity: E) -> &E::Data {
        self.try_get_mut(entity).unwrap()
    }

    /// Count of how many entities were created.
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

/// A map to associate other data than [`Entity::Data`] to an [`Entity`].
/// Designed for sparse ID sets: use when entities are assigned non-contiguous
/// IDs with frequent holes.
///
/// See also [`TightMap`].
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

    /// Insert a new `value` for `entity`, over-writing the previous one if any.
    pub fn insert(&mut self, entity: E, value: V) {
        self.elems.insert(entity.index(), value);
    }

    /// Get the value associated with `entity`.
    pub fn get(&self, entity: E) -> Option<&V> {
        self.elems.get(&entity.index())
    }

    /// Get the value associated with `entity`, but mutable version.
    pub fn get_mut(&mut self, entity: E) -> Option<&mut V> {
        self.elems.get_mut(&entity.index())
    }

    /// Clear the hole map.
    pub fn clear(&mut self) {
        self.elems.clear();
    }

    /// Does this map contains the `entity`?
    pub fn contains_entity(&self, entity: E) -> bool {
        self.get(entity).is_some()
    }
}

impl<E: Entity, V> Default for SparseMap<E, V> {
    fn default() -> Self {
        SparseMap::new()
    }
}

/// A map to associate other data than [`Entity::Data`] to an [`Entity`].
/// Optimized for densely-numbered entities: choose this collection when entity
/// IDs are large and form a mostly contiguous range (rarely or never missing).
/// If you cannot ensure that please use [`SparseMap`].
///
/// With this collection, the "holes" will be filled with a default value.
///
/// See also [`SparseMap`].
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
    /// Create a new empty [`TightMap`] with the default value of `V` being
    /// [`Default::default`].
    pub fn new() -> TightMap<E, V>
    where
        V: Default,
    {
        TightMap::with_default(Default::default())
    }

    /// Create a new empty [`TightMap`] with the default value of `V` being
    /// `default`.
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
                self.occupied.extend(std::iter::repeat(false).take(to_add));
            }
        }
    }

    /// Insert a new `value` for `entity`, over-writing the previous one if any.
    pub fn insert(&mut self, entity: E, value: V) {
        self.ensure_index(entity.index());

        // put value into slot, mark occupied
        self.elems[entity.index()] = value;

        #[cfg(debug_assertions)]
        {
            self.occupied[entity.index()] = true;
        };
    }

    /// Remove the `entity` from this map, return the value stored before,
    /// please note that the value before may be the default value of this map,
    /// if this function return `Some(..)` it does not guarantee that there was
    /// ever a matching `TightMap::insert` call.
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

    /// Get the value associated with `entity`.
    pub fn get(&self, entity: E) -> Option<&V> {
        self.elems.get(entity.index())
    }

    /// Get the value associated with `entity`, but mutable version.
    pub fn get_mut(&mut self, entity: E) -> Option<&mut V> {
        self.elems.get_mut(entity.index())
    }

    /// Clear the hole map.
    pub fn clear(&mut self) {
        self.elems.clear();
    }
}

impl<E: Entity, V: Clone + Default> Default for TightMap<E, V> {
    fn default() -> Self {
        TightMap::new()
    }
}
