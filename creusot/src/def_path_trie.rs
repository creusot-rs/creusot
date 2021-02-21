use rustc_hir::definitions::DefPathData;
use rustc_hir::definitions::DisambiguatedDefPathData;
use sequence_trie::*;

use crate::util::ModulePath;

#[derive(Debug)]
pub struct DefPathTrie<K> {
    inner: SequenceTrie<FakeDisambiguatedDefPathData, K>,
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
struct FakeDisambiguatedDefPathData {
    data: DefPathData,
    disambiguator: u32,
}

impl From<DisambiguatedDefPathData> for FakeDisambiguatedDefPathData {
    fn from(dpd: DisambiguatedDefPathData) -> Self {
        // SAFETY: I do not believe that rustc guarantees that the layout
        // of identical structs will be identical, which makes this unsafe.
        // I am leaving this in for now, a more correct version would do an actual
        // translation between identical structs, or would use safe transmute (when that arrives)
        unsafe { std::mem::transmute(dpd) }
    }
}

impl Into<DisambiguatedDefPathData> for FakeDisambiguatedDefPathData {
    fn into(self) -> DisambiguatedDefPathData {
        unsafe { std::mem::transmute(self) }
    }
}

impl<V> DefPathTrie<V> {
    pub fn new() -> Self {
        Self { inner: SequenceTrie::new() }
    }

    pub fn insert(&mut self, key: ModulePath, value: V) -> Option<V> {
        self.inner.insert_owned(key.0.data.into_iter().map(|dpd| dpd.into()), value)
    }

    pub fn get_mut(&mut self, key: ModulePath) -> Option<&mut V> {
        self.inner.get_mut(
            unsafe {
                std::mem::transmute::<
                    Vec<DisambiguatedDefPathData>,
                    Vec<FakeDisambiguatedDefPathData>,
                >(key.0.data)
            }
            .iter(),
        )
    }

    pub fn get(&self, key: ModulePath) -> Option<&V> {
        self.inner.get(
            unsafe {
                std::mem::transmute::<
                    Vec<DisambiguatedDefPathData>,
                    Vec<FakeDisambiguatedDefPathData>,
                >(key.0.data)
            }
            .iter(),
        )
    }

    pub fn get_mut_with_default(&mut self, key: ModulePath) -> &mut V
    where
        V: Default,
    {
        if self.get(key.clone()).is_none() {
            self.insert(key.clone(), V::default());
        }
        self.get_mut(key).unwrap()
    }

    pub fn value(&self) -> Option<&V> {
        self.inner.value()
    }

    // pub fn key
    pub fn children_with_keys(&self) -> Vec<(&DisambiguatedDefPathData, &Self)> {
        self.inner
            .children_with_keys()
            .into_iter()
            .map(|kv| {
                // SAFETY: YOLO. REMOVE AS SOON AS CONFIRMED WORKING
                unsafe { std::mem::transmute(kv) }
            })
            .collect()
    }
}
