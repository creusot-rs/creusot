use crate::{
    logic::FMap,
    std::iter::{FromIterator, Iterator},
    *,
};
use ::std::{
    collections::hash_map::*,
    default::Default,
    hash::{BuildHasher, Hash},
};

impl<K: DeepModel, V, S> View for HashMap<K, V, S> {
    type ViewTy = FMap<K::DeepModelTy, V>;

    #[logic(open)]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

extern_spec! {
    mod std {
        mod collections {
            mod hash_map {
                impl<K: DeepModel, V, S> HashMap<K, V, S> {
                    #[ensures(self@ == result@)]
                    fn iter(&self) -> Iter<'_, K, V>;

                    #[ensures(forall<k: K::DeepModelTy> (*self)@.contains(k) == (^self)@.contains(k))]
                    #[ensures(forall<k: K::DeepModelTy> (*self)@.contains(k) == result@.contains(k))]
                    #[ensures(forall<k: K::DeepModelTy> (*self)@.contains(k) ==> (*self)@[k] == *result@[k] && (^self)@[k] == ^result@[k])]
                    fn iter_mut(&mut self) -> IterMut<'_, K, V>;
                }
            }
        }
    }

    impl<K: DeepModel, V, S> IntoIterator for HashMap<K, V, S> {
        #[ensures(self@ == result@)]
        fn into_iter(self) -> IntoIter<K, V>;
    }

    impl<'a, K: DeepModel, V, S> IntoIterator for &'a HashMap<K, V, S> {
        #[ensures(self@ == result@)]
        fn into_iter(self) -> Iter<'a, K, V>;
    }

    impl<'a, K: DeepModel, V, S> IntoIterator for &'a mut HashMap<K, V, S> {
        #[ensures(forall<k: K::DeepModelTy> (*self)@.contains(k) == (^self)@.contains(k))]
        #[ensures(forall<k: K::DeepModelTy> (*self)@.contains(k) == result@.contains(k))]
        #[ensures(forall<k: K::DeepModelTy> (*self)@.contains(k) ==> (*self)@[k] == *result@[k] && (^self)@[k] == ^result@[k])]
        fn into_iter(self) -> IterMut<'a, K, V>;
    }
}

impl<K: DeepModel, V> View for IntoIter<K, V> {
    type ViewTy = FMap<K::DeepModelTy, V>;

    #[logic(open)]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<K: DeepModel, V> Iterator for IntoIter<K, V> {
    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        // self@ equals the union of visited (viewed as a fmap) and o@
        pearlite! {
            self@.len() == visited.len() + o@.len()
            && (forall<k: K, v: V> visited.contains((k, v))
                ==> self@.get(k.deep_model()) == Some(v) && o@.get(k.deep_model()) == None)
            && (forall<k: K::DeepModelTy, v: V> o@.get(k) == Some(v)
                ==> self@.get(k) == Some(v) && !exists<k2: K, v2: V> k2.deep_model() == k && visited.contains((k2, v2)))
            && (forall<k: K::DeepModelTy, v: V> self@.get(k) == Some(v)
                ==> (exists<k1: K> k1.deep_model() == k && visited.contains((k1, v))) || o@.get(k) == Some(v))
            && (forall<i1, i2>
                0 <= i1 && i1 < visited.len() && 0 <= i2 && i2 < visited.len()
                && visited[i1].0.deep_model() == visited[i2].0.deep_model()
                ==> i1 == i2)
        }
    }

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && self@.is_empty() }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        proof_assert! { forall<i> 0 <= i && i < bc.len() ==> bc[i] == ab.concat(bc)[ab.len() + i] }
    }
}

impl<'a, K: DeepModel, V> View for Iter<'a, K, V> {
    type ViewTy = FMap<K::DeepModelTy, V>;

    #[logic(open)]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<'a, K: DeepModel, V> Iterator for Iter<'a, K, V> {
    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        // `self@` equals the union of `visited` (viewed as a finite map) and `o@`
        pearlite! {
            self@.len() == visited.len() + o@.len()
            && (forall<k: &K, v: &V> visited.contains((k, v))
                ==> self@.get(k.deep_model()) == Some(*v) && o@.get(k.deep_model()) == None)
            && (forall<k: K::DeepModelTy, v: V> o@.get(k) == Some(v)
                ==> self@.get(k) == Some(v) && !exists<k2: &K, v2: &V> k2.deep_model() == k && visited.contains((k2, v2)))
            && (forall<k: K::DeepModelTy, v: V> self@.get(k) == Some(v)
                ==> (exists<k2: &K> k2.deep_model() == k && visited.contains((k2, &v))) || o@.get(k) == Some(v))
            && (forall<i1, i2>
                0 <= i1 && i1 < visited.len() && 0 <= i2 && i2 < visited.len()
                && visited[i1].0.deep_model() == visited[i2].0.deep_model()
                ==> i1 == i2)
        }
    }

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && self@.is_empty() }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        proof_assert! { forall<i> 0 <= i && i < bc.len() ==> bc[i] == ab.concat(bc)[ab.len() + i] }
    }
}

impl<'a, K: DeepModel, V> View for IterMut<'a, K, V> {
    type ViewTy = FMap<K::DeepModelTy, &'a mut V>;

    #[logic(open)]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<'a, K: DeepModel, V> Iterator for IterMut<'a, K, V> {
    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        // self@ equals the union of visited (viewed as a fmap) and o@
        pearlite! {
            self@.len() == visited.len() + o@.len()
            && (forall<k: K, v: &mut V> visited.contains((&k, v))
                ==> self@.get(k.deep_model()) == Some(v) && o@.get(k.deep_model()) == None)
            && (forall<k: K::DeepModelTy, v: &mut V> o@.get(k) == Some(v)
                ==> self@.get(k) == Some(v) && !exists<k2: &K, v2: &mut V> k2.deep_model() == k && visited.contains((k2, v2)))
            && (forall<k: K::DeepModelTy, v: &mut V> self@.get(k) == Some(v)
                ==> (exists<k1: &K> k1.deep_model() == k && visited.contains((k1, v))) || o@.get(k) == Some(v))
            && (forall<i1, i2>
                0 <= i1 && i1 < visited.len() && 0 <= i2 && i2 < visited.len()
                && visited[i1].0.deep_model() == visited[i2].0.deep_model()
                ==> i1 == i2)
        }
    }

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && self@.is_empty() }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        proof_assert! { forall<i> 0 <= i && i < bc.len() ==> bc[i] == ab.concat(bc)[ab.len() + i] }
    }
}

impl<K: Eq + Hash + DeepModel, V, S: Default + BuildHasher> FromIterator<(K, V)>
    for HashMap<K, V, S>
{
    #[logic(open)]
    fn from_iter_post(prod: Seq<(K, V)>, res: Self) -> bool {
        pearlite! { forall<k: K::DeepModelTy, v: V> (res@.get(k) == Some(v))
        == (exists<i, k1: K> 0 <= i && i < prod.len() && k1.deep_model() == k && prod[i] == (k1, v)
            && forall<j> i < j && j < prod.len() ==> prod[j].0.deep_model() != k) }
    }
}
