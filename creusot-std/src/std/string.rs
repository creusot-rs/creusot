use crate::prelude::*;
#[cfg(all(creusot, feature = "std"))]
use core::ops::Deref;

impl View for str {
    type ViewTy = Seq<char>;

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl DeepModel for str {
    type DeepModelTy = Seq<char>;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        self.view()
    }
}

#[cfg(feature = "std")]
impl View for String {
    type ViewTy = Seq<char>;

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

#[cfg(feature = "std")]
impl DeepModel for String {
    type DeepModelTy = Seq<char>;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        self.view()
    }
}

#[cfg(feature = "std")]
extern_spec! {
    impl Deref for String {
        #[check(ghost)]
        #[ensures(result@ == self@)]
        fn deref(&self) -> &str;
    }

    impl String {
        #[check(ghost)]
        #[ensures(result@ == self@.to_bytes().len())]
        fn len(&self) -> usize;

        #[check(ghost)]
        #[requires(exists<s: Seq<char>> s.to_bytes() == bytes@)]
        #[ensures(result@.to_bytes() == bytes@)]
        unsafe fn from_utf8_unchecked(bytes: Vec<u8>) -> String;
    }

    impl Clone for Box<str> {
        #[check(ghost)]
        #[ensures((*result)@ == (**self)@)]
        fn clone(&self) -> Box<str>;
    }

    impl ToOwned for str {
        #[check(terminates)] // can OOM (?)
        #[ensures(result@ == self@)]
        fn to_owned(&self) -> String;
    }

    impl FromIterator<char> for String {
        #[requires(I::into_iter.precondition((iter,)))]
        #[ensures(exists<into_iter: I::IntoIter, done: &mut I::IntoIter>
            I::into_iter.postcondition((iter,), into_iter) &&
            into_iter.produces(result@, *done) && done.completed() && resolve(^done)
        )]
        fn from_iter<I: IntoIterator<Item = char, IntoIter: IteratorSpec>>(iter: I) -> Self;
    }

    impl FromIterator<char> for Box<str> {
        #[requires(I::into_iter.precondition((iter,)))]
        #[ensures(exists<into_iter: I::IntoIter, done: &mut I::IntoIter>
            I::into_iter.postcondition((iter,), into_iter) &&
            into_iter.produces(result@, *done) && done.completed() && resolve(^done)
        )]
        fn from_iter<I: IntoIterator<Item = char, IntoIter: IteratorSpec>>(iter: I) -> Self;
    }

    impl<'a> FromIterator<&'a char> for String {
        #[requires(I::into_iter.precondition((iter,)))]
        #[ensures(exists<into_iter: I::IntoIter, produced: Seq<I::Item>, done: &mut I::IntoIter>
            I::into_iter.postcondition((iter,), into_iter) &&
            into_iter.produces(produced, *done) && done.completed() && resolve(^done) &&
            result@ == produced.map(|c: &char| *c)
        )]
        fn from_iter<I: IntoIterator<Item = &'a char, IntoIter: IteratorSpec>>(iter: I) -> Self;
    }

    impl<'a> FromIterator<&'a char> for Box<str> {
        #[requires(I::into_iter.precondition((iter,)))]
        #[ensures(exists<into_iter: I::IntoIter, produced: Seq<I::Item>, done: &mut I::IntoIter>
            I::into_iter.postcondition((iter,), into_iter) &&
            into_iter.produces(produced, *done) && done.completed() && resolve(^done) &&
            result@ == produced.map(|c: &char| *c)
        )]
        fn from_iter<I: IntoIterator<Item = &'a char, IntoIter: IteratorSpec>>(iter: I) -> Self;
    }

    impl<'a> FromIterator<&'a str> for String {
        #[requires(I::into_iter.precondition((iter,)))]
        #[ensures(exists<into_iter: I::IntoIter, produced: Seq<I::Item>, done: &mut I::IntoIter>
            I::into_iter.postcondition((iter,), into_iter) &&
            into_iter.produces(produced, *done) && done.completed() && resolve(^done) &&
            result@ == produced.flat_map(|s: I::Item| s@)
        )]
        fn from_iter<I: IntoIterator<Item = &'a str, IntoIter: IteratorSpec>>(iter: I) -> Self;
    }

    impl<'a> FromIterator<&'a str> for Box<str> {
        #[requires(I::into_iter.precondition((iter,)))]
        #[ensures(exists<into_iter: I::IntoIter, produced: Seq<I::Item>, done: &mut I::IntoIter>
            I::into_iter.postcondition((iter,), into_iter) &&
            into_iter.produces(produced, *done) && done.completed() && resolve(^done) &&
            result@ == produced.flat_map(|s: &str| s@)
        )]
        fn from_iter<I: IntoIterator<Item = &'a str, IntoIter: IteratorSpec>>(iter: I) -> Self;
    }

    impl<A: std::alloc::Allocator> FromIterator<Box<str, A>> for String {
        #[requires(I::into_iter.precondition((iter,)))]
        #[ensures(exists<into_iter: I::IntoIter, produced: Seq<I::Item>, done: &mut I::IntoIter>
            I::into_iter.postcondition((iter,), into_iter) &&
            into_iter.produces(produced, *done) && done.completed() && resolve(^done) &&
            result@ == produced.flat_map(|s: I::Item| s@)
        )]
        fn from_iter<I: IntoIterator<Item = Box<str, A>, IntoIter: IteratorSpec>>(iter: I) -> Self;
    }

    impl<A: std::alloc::Allocator> FromIterator<Box<str, A>> for Box<str> {
        #[requires(I::into_iter.precondition((iter,)))]
        #[ensures(exists<into_iter: I::IntoIter, produced: Seq<I::Item>, done: &mut I::IntoIter>
            I::into_iter.postcondition((iter,), into_iter) &&
            into_iter.produces(produced, *done) && done.completed() && resolve(^done) &&
            result@ == produced.flat_map(|s: I::Item| s@)
        )]
        fn from_iter<I: IntoIterator<Item = Box<str, A>, IntoIter: IteratorSpec>>(iter: I) -> Self;
    }

    impl FromIterator<String> for Box<str> {
        #[requires(I::into_iter.precondition((iter,)))]
        #[ensures(exists<into_iter: I::IntoIter, produced: Seq<I::Item>, done: &mut I::IntoIter>
            I::into_iter.postcondition((iter,), into_iter) &&
            into_iter.produces(produced, *done) && done.completed() && resolve(^done) &&
            result@ == produced.flat_map(|s: I::Item| s@)
        )]
        fn from_iter<I: IntoIterator<Item = String, IntoIter: IteratorSpec>>(iter: I) -> Self;
    }

    impl FromIterator<String> for String {
        #[requires(I::into_iter.precondition((iter,)))]
        #[ensures(exists<into_iter: I::IntoIter, produced: Seq<I::Item>, done: &mut I::IntoIter>
            I::into_iter.postcondition((iter,), into_iter) &&
            into_iter.produces(produced, *done) && done.completed() && resolve(^done) &&
            result@ == produced.flat_map(|s: I::Item| s@)
        )]
        fn from_iter<I: IntoIterator<Item = String, IntoIter: IteratorSpec>>(iter: I) -> Self;
    }
}

extern_spec! {
    impl str {
        #[check(ghost)]
        #[ensures(result@ == self@.to_bytes().len())]
        fn len(&self) -> usize;

        #[check(ghost)]
        #[requires(exists<i0> 0 <= i0 && i0 <= self@.len() && self@.subsequence(0, i0).to_bytes().len() == ix@)]
        #[ensures(result.0@.concat(result.1@) == self@)]
        #[ensures(result.0@.to_bytes().len() == ix@)]
        fn split_at(&self, ix: usize) -> (&str, &str);
    }
}

impl Seq<char> {
    #[logic(open)]
    pub fn to_bytes(self) -> Seq<u8> {
        pearlite! { self.flat_map(|c: char| c.to_utf8()) }
    }
}

#[trusted]
#[logic(open)]
#[ensures(forall<s1: Seq<char>, s2: Seq<char>> s1.to_bytes() == s2.to_bytes() ==> s1 == s2)]
pub fn injective_to_bytes() {}
