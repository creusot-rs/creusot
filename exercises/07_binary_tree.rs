extern crate creusot_contracts;
use creusot_contracts::*;

enum BinaryTree<T> {
	Leaf(T),
	Node(Box<BinaryTree<T>>, T, Box<BinaryTree<T>>)
}

impl<T : Model> BinaryTree<T> {
	#[logic]
	fn model_acc(self, map: <Self as Model>::ModelTy) -> <Self as Model>::ModelTy {
		match self {
			BinaryTree::Leaf(k) => map.set(k.model(), true),
			BinaryTree::Node(l, k, r) => l.model_acc(r.model_acc(map)).set(k.model(), true)
		}
	}

	#[logic]
	fn has(self, k: T) -> bool {
		match self {
			BinaryTree::Leaf(l) => pearlite! { @l == @k },
			BinaryTree::Node(l, k2, r) => l.has(k) || pearlite! { @k2 == @k } || r.has(k)
		}
	}
}

impl<K : Model> Model for BinaryTree<K> {
	type ModelTy = Mapping<K::ModelTy, bool>;

	#[logic]
	fn model(self) -> Self::ModelTy {
		self.model_acc(Mapping::cst(false))
	}
}


impl<T : Ord + Model> BinaryTree<T>
where T::ModelTy: OrdLogic {
	#[predicate]
	fn invariant(self) -> bool {
		self.unique_keys() && self.ordered_keys()
	}

	#[predicate]
	fn unique_keys(self) -> bool {
		match self {
			BinaryTree::Leaf(_) => true,
			BinaryTree::Node(l, k, r) => 
				l.unique_keys() && r.unique_keys() && 
				pearlite! { !(@l).get(@k) && !(@r).get(@k) }
		}
	}

	#[predicate]
	fn ordered_keys(self) -> bool {
		match self {
			BinaryTree::Leaf(_) => true,
			BinaryTree::Node(l, k, r) => 
				l.ordered_keys() && r.ordered_keys() &&
				pearlite! {
					forall<k2 : T> (@l).get(@k2) ==> @k2 < @k 
				} && 
				pearlite! { forall<k2 : T> (@r).get(@k2) ==> @k < @k2 }
		}
	}

	#[logic]
	#[requires(self.invariant())]
	#[ensures(self.has(k) ==> (@self).get(@k))]
	fn model_accu(self, accu: <Self as Model>::ModelTy, k: T) {
		match self {
			BinaryTree::Leaf(_) => (),
			BinaryTree::Node(l, k2, r) => {
				r.model_accu(accu, k);
				l.model_accu(r.model_acc(accu), k);
				if pearlite! { @k == @k2 } {
					()
				} else {
					()
				}
			},
		}
	}

	// #[logic]
	// #[requires(BinaryTree::Node(l, k, r).invariant())]
	// #[requires((@l).get(@k2))]
	// #[ensures((@BinaryTree::Node(l, k, r)).get(@k2))]
	// fn model_left(l: Box<Self>, k: T, r: Box<Self>, k2: T) {}

	#[requires(self.invariant())]
	#[ensures(result == (@self).get(@k))]
	fn contains(&self, k: &T) -> bool {
		match self {
			BinaryTree::Leaf(k2) => k == k2,
			BinaryTree::Node(l, k2, r) => match k.cmp(k2) {
				Ordering::Less => l.contains(k),
				Ordering::Equal => true,
				Ordering::Greater => r.contains(k),
			} 
		}
	}
}