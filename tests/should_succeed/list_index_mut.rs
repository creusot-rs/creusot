extern crate creusot_contracts;
use creusot_contracts::{logic::Int, *};

pub struct List(u32, Option<Box<List>>);
impl List {
    #[logic]
    fn len(self: List) -> Int {
        {
            let List(_, ls) = self;
            1 + match ls {
                Some(ls) => ls.len(),
                None => 0,
            }
        }
    }

    #[logic]
    fn get(self: List, ix: Int) -> Option<u32> {
        {
            let List(i, ls) = self;
            match ix > 0 {
                false => Some(i),
                true => match ls {
                    Some(ls) => ls.get(ix - 1),
                    None => None,
                },
            }
        }
    }
}

#[requires(ix@ < l.len())]
#[ensures(Some(*result) == l.get(ix@))]
#[ensures(Some(^result) == (^l).get(ix@))]
#[ensures((^l).len() == (*l).len())]
#[ensures(forall<i> 0 <= i && i < l.len() && i != ix@ ==> l.get(i) == (^l).get(i))]
pub fn index_mut(mut l: &mut List, mut ix: usize) -> &mut u32 {
    let old_l = snapshot! { l };
    let old_ix = snapshot! { ix };
    #[invariant(0usize <= ix && ix@ < l.len())]
    #[invariant(l.get(ix@) == (**old_l).get(old_ix@))]
    #[invariant((^l).get(ix@) == (^*old_l).get(old_ix@))]
    #[invariant((^l).len() == l.len() ==> (^*old_l).len() == (**old_l).len())]
    #[invariant(
        (forall<i> 0 <= i && i < l.len() && i != ix@ ==> (^l).get(i) == l.get(i)) ==>
        forall<i> 0 <= i && i < old_l.len() && i != old_ix@ ==>
            (^*old_l).get(i) == (**old_l).get(i)
    )]
    while ix > 0 {
        l = l.1.as_mut().unwrap();

        ix -= 1;
    }

    &mut l.0
}

// Ensure that this performs a set on the list
#[requires(ix@ < l.len())]
#[ensures(Some(v) == (^l).get(ix@))]
#[ensures((^l).len() == l.len())]
#[ensures(forall<i> 0 <= i && i < l.len() && i != ix@ ==> l.get(i) == (^l).get(i))]
pub fn write(l: &mut List, ix: usize, v: u32) {
    *index_mut(l, ix) = v;
}

pub fn f() {
    let mut l = List(1, Some(Box::new(List(10, None))));
    write(&mut l, 0, 2);

    // assert!(get 0 l == 2 && get 1 l == 10);
}
