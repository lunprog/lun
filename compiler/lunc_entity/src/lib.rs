//! Entities, described in [#56].
//!
//! [#56]: https://github.com/lunprog/lun/issues/56
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use std::{fmt::Debug, hash::Hash, marker::PhantomData};

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
