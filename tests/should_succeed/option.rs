extern crate creusot_contracts;
use creusot_contracts::prelude::*;

pub fn is_some_none() {
    let none: Option<i32> = None;
    let some: Option<i32> = Some(1);

    assert!(some.is_some() && !none.is_some());
    assert!(!some.is_none() && none.is_none());
}

pub fn unwrap() {
    let none: Option<i32> = None;
    let some: Option<i32> = Some(1);

    assert!(some.unwrap() == 1);
    assert!(some.expect("failed") == 1);

    assert!(some.unwrap_or(2) == 1);
    assert!(none.unwrap_or(2) == 2);

    assert!(some.unwrap_or_default() == 1);
    assert!(none.unwrap_or_default() == 0);

    assert!(some.unwrap_or_else(|| panic!()) == 1);
    assert!(none.unwrap_or_else(|| 3) == 3);

    assert!(unsafe { some.unwrap_unchecked() } == 1);
}

pub fn map() {
    let none: Option<i32> = None;
    let some: Option<i32> = Some(1);

    assert!(
        none.map(|_| {
            panic!();
            #[allow(unreachable_code)]
            ()
        }) == None
    );
    assert!(some.map(|_| 3) == Some(3));
    assert!(some.map(|x| x + 1) == Some(2));
}

pub fn inspect() {
    let none: Option<i32> = None;
    let some: Option<i32> = Some(1);

    assert!(none.inspect(|_| panic!()) == None);
    assert!(some.inspect(|_| {}) == Some(1));
}

pub fn map_or() {
    let none: Option<i32> = None;
    let some: Option<i32> = Some(1);

    // map_or
    assert!(none.map_or(2, |_| panic!()) == 2);
    assert!(some.map_or(-1, |_| 3) == 3);
    assert!(some.map_or(-1, |x| x + 1) == 2);

    // map_or_else
    assert!(none.map_or_else(|| 2, |_| panic!()) == 2);
    assert!(some.map_or_else(|| panic!(), |x| x + 1) == 2);
}

pub fn ok_or() {
    let none: Option<i32> = None;
    let some: Option<i32> = Some(1);

    let err = none.ok_or(true);
    proof_assert!(err == Err(true));
    let ok = some.ok_or(false);
    proof_assert!(ok == Ok(1i32));

    let err = none.ok_or_else(|| true);
    proof_assert!(err == Err(true));
    let ok = some.ok_or_else(|| false);
    proof_assert!(ok == Ok(1i32));
}

pub fn as_mut() {
    let mut none: Option<i32> = None;
    let mut some: Option<i32> = Some(1);

    assert!(none.as_mut().is_none());
    *some.as_mut().unwrap() = 2;
    assert!(some.unwrap() == 2);
    *some.as_mut().unwrap() = 1;
    assert!(some.unwrap() == 1);
}

pub fn as_ref() {
    let none: Option<i32> = None;
    let some: Option<i32> = Some(1);

    assert!(none.as_ref().is_none());
    assert!(*some.as_ref().unwrap() == 1);
}

pub fn replace() {
    let mut none: Option<i32> = None;
    let mut some: Option<i32> = Some(1);

    assert!(none.replace(2).is_none());
    assert!(none.unwrap() == 2);
    assert!(some.replace(2).unwrap() == 1);
    assert!(some.unwrap() == 2);
    assert!(some.replace(1).unwrap() == 2);
    assert!(some.unwrap() == 1);
}

pub fn and_or_xor() {
    let none: Option<i32> = None;
    let some: Option<i32> = Some(1);

    // Test `and`
    assert!(none.and(none) == None);
    assert!(none.and(Some(2)) == None);
    assert!(some.and(none) == None);
    assert!(some.and(Some(2)) == Some(2));
    // Test `or`
    assert!(none.or(none) == None);
    assert!(none.or(Some(2)) == Some(2));
    assert!(some.or(none) == Some(1));
    assert!(some.or(Some(2)) == Some(1));
    // Test `xor`
    assert!(none.xor(none) == None);
    assert!(none.xor(Some(2)) == Some(2));
    assert!(some.xor(none) == Some(1));
    assert!(some.xor(Some(2)) == None);
}

pub fn and_then() {
    let none: Option<i32> = None;
    let some1: Option<i32> = Some(1);
    let some2: Option<i32> = Some(3);

    assert!(none.and_then(|_| -> Option<i32> { panic!() }) == None);
    let clos = #[ensures(
        (x@ == 1 && exists<y: i32> result == Some(y) && y@ == x@ + 1)
        || (x@ != 1 && result == None)
    )]
    |x: i32| {
        if x == 1 { Some(x + 1) } else { None }
    };
    assert!(some1.and_then(clos) == Some(2i32));
    assert!(some2.and_then(clos) == None);
}

pub fn filter() {
    let none: Option<i32> = None;
    let some: Option<i32> = Some(1);

    assert!(none.filter(|_| panic!()) == None);
    assert!(some.filter(|x| *x == 1) == Some(1i32));
    assert!(some.filter(|x| *x == 2) == None);
}

pub fn is_some_and() {
    let none: Option<i32> = None;
    let some1: Option<i32> = Some(1);
    let some2: Option<i32> = Some(2);

    assert!(some1.is_some_and(|x| x == 1));
    assert!(!some2.is_some_and(|x| x == 1));
    assert!(!none.is_some_and(|_| true));
}

pub fn or_else() {
    let none: Option<i32> = None;
    let some: Option<i32> = Some(1);

    assert!(none.or_else(|| Some(2)) == Some(2));
    assert!(none.or_else(|| None) == None);
    assert!(some.or_else(|| panic!()) == Some(1));
}

pub fn insert() {
    let mut none: Option<i32> = None;
    let mut some: Option<i32> = Some(1);

    let i1 = none.insert(2);
    assert!(*i1 == 2);
    *i1 = 3;
    assert!(none == Some(3));
    let i2 = some.insert(4);
    assert!(*i2 == 4);
    *i2 = 5;
    assert!(some == Some(5));
}

pub fn get_or_insert() {
    let mut none: Option<i32> = None;
    let mut some: Option<i32> = Some(1);

    // Test `get_or_insert`
    let i1 = none.get_or_insert(2);
    assert!(*i1 == 2);
    *i1 = 3;
    assert!(none == Some(3));
    let i2 = some.get_or_insert(4);
    assert!(*i2 == 1);
    *i2 = 5;
    assert!(some == Some(5));

    none = None;
    some = Some(1);

    // Test `get_or_insert_with`
    let i1 = none.get_or_insert_with(|| 2);
    assert!(*i1 == 2);
    *i1 = 3;
    assert!(none == Some(3));
    let i2 = some.get_or_insert_with(|| panic!());
    assert!(*i2 == 1);
    *i2 = 5;
    assert!(some == Some(5));
}

pub fn take() {
    let mut none: Option<i32> = None;
    let mut some: Option<i32> = Some(1);

    assert!(none.take().is_none());
    assert!(none.is_none());
    assert!(some.take().unwrap() == 1);
    assert!(some.is_none());
}

pub fn take_if() {
    let mut none: Option<i32> = None;
    let mut some: Option<i32> = Some(1);

    assert!(none.take_if(|_| panic!()) == None);
    assert!(some.take_if(|x| *x == 2) == None);
    assert!(some == Some(1));
    assert!(
        some.take_if(|x| {
            let res = *x == 1;
            *x = 3;
            res
        }) == Some(3)
    );
    assert!(some == None);
}

pub fn copied_cloned() {
    let mut none: Option<i32> = None;
    let mut some: Option<i32> = Some(1);

    // Test `copied`
    assert!(none.as_ref().copied().is_none());
    assert!(some.as_ref().copied().unwrap() == 1);
    assert!(none.as_mut().copied().is_none());
    assert!(some.as_mut().copied().unwrap() == 1);
    // Test `cloned`
    assert!(none.as_ref().cloned().is_none());
    assert!(some.as_ref().cloned().unwrap() == 1);
    assert!(none.as_mut().cloned().is_none());
    assert!(some.as_mut().cloned().unwrap() == 1);
}

pub fn zip_unzip() {
    let none_int: Option<i32> = None;
    let none_bool: Option<bool> = None;
    let some_int: Option<i32> = Some(1);
    let some_bool: Option<bool> = Some(true);

    assert!(none_int.zip(none_bool) == None);
    assert!(none_int.zip(some_bool) == None);
    assert!(some_int.zip(none_bool) == None);
    assert!(some_int.zip(some_bool) == Some((1, true)));

    let none_zipped: Option<(i32, bool)> = None;
    let some_zipped: Option<(i32, bool)> = Some((1, true));

    let none_unzip = none_zipped.unzip();
    let some_unzip = some_zipped.unzip();
    assert!(none_unzip.0 == None);
    assert!(none_unzip.1 == None);
    assert!(some_unzip.0 == Some(1));
    assert!(some_unzip.1 == Some(true));
}

pub fn transpose() {
    let none: Option<Result<i32, bool>> = None;
    let some_ok: Option<Result<i32, bool>> = Some(Ok(1));
    let some_err: Option<Result<i32, bool>> = Some(Err(true));

    assert!(none.transpose().unwrap() == None);
    assert!(some_ok.transpose().unwrap() == Some(1));
    assert!(some_err.transpose().unwrap_err() == true);
}

pub fn flatten() {
    let opt: Option<Option<i32>> = None;
    assert!(opt.flatten().is_none());
    let opt: Option<Option<i32>> = Some(None);
    assert!(opt.flatten().is_none());
    let opt: Option<Option<i32>> = Some(Some(1));
    assert!(opt.flatten().unwrap() == 1);
}

pub fn resolve() {
    // is_some_and
    let mut x = 1;
    let opt = Some(&mut x);
    assert!(opt.is_some_and(|_| true));
    assert!(x == 1);

    // and/or
    let mut x = 1;
    let opt = Some(&mut x);
    let _ = opt.and(Some(2));
    assert!(x == 1);
    let mut x = 1;
    let mut y = 2;
    let opt = Some(&mut x);
    let _ = Some(&mut y).or(opt);
    assert!(x == 1 && y == 2);

    // filter
    let mut x = 1;
    let opt = Some(&mut x);
    let _ = opt.filter(|_| false);
    assert!(x == 1);
    // xor
    let mut x = 1;
    let mut y = 2;
    let optx = Some(&mut x);
    let opty = Some(&mut y);
    let _ = optx.xor(opty);
    assert!(x == 1 && y == 2);

    // insert
    let mut x = 1;
    let mut y = 2;
    let mut opt = Some(&mut x);
    let bor = opt.insert(&mut y);
    **bor = 3;
    assert!(x == 1 && y == 3);

    // get_or_insert
    let mut x = 1;
    let mut y = 2;
    let mut opt = Some(&mut x);
    let bor = opt.get_or_insert(&mut y);
    **bor = 3;
    assert!(x == 3 && y == 2);

    // zip
    let mut x = 1;
    let opt = Some(&mut x);
    let _ = opt.zip(None::<i32>);
    assert!(x == 1);

    // copied, cloned
    let mut x = 1;
    let opt = Some(&mut x);
    let _ = opt.copied();
    assert!(x == 1);
    let opt = Some(&mut x);
    let _ = opt.cloned();
    assert!(x == 1);
}
