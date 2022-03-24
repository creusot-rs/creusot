extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;
use std::mem;

extern_spec! {
    #[ensures(match result {
        None => (@s).len() == 0 && ^s === * s && @*s === Seq::EMPTY,
        Some((first, tail)) => *first === (@*s)[0] && ^first === (@^s)[0]
            && (@*s).len() > 0 && (@^s).len() > 0
            && @*tail === (@*s).tail()
            && @^tail === (@^s).tail()
    })]
    fn <[T]>::split_first_mut<'a, T>(s: &'a mut [T]) -> Option<(&'a mut T, &'a mut [T])>
}

trait DefaultSpec: Default {
    #[logic]
    fn default_log() -> Self;
}

extern_spec! {
    #[ensures(result === *dest)]
    #[ensures(^dest === T::default_log())]
    fn std::mem::take<T : DefaultSpec>(dest: &mut T) -> T
}

impl<'a, T> DefaultSpec for &'a mut [T] {
    #[logic]
    #[trusted]
    #[ensures(@*result === Seq::EMPTY)]
    #[ensures(@^result === Seq::EMPTY)]
    fn default_log() -> Self {
        std::process::abort()
    }
}

#[ensures(match result {
    Some(r) => {
        * r === (@**self_)[0] &&
        ^ r === (@^*self_)[0] &&
        (@**self_).len() > 0 && // ^*s.len === **s.len ? (i dont think so)
        (@^*self_).len() > 0 &&
        @*^self_ === (@**self_).tail() && @^^self_ === (@^*self_).tail()
    }
    None => ^self_ === * self_ && (@**self_).len() === 0
})]
pub fn take_first_mut<'a, T>(self_: &mut &'a mut [T]) -> Option<&'a mut T> {
    match mem::take(self_).split_first_mut() {
        None => return None,
        Some((first, rem)) => {
            *self_ = rem;
            Some(first)
        }
    }
}
