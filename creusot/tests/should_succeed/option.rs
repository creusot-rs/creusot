extern crate creusot_contracts;

pub fn test_option() {
    let mut none: Option<i32> = None;
    let mut some: Option<i32> = Some(1);

    // Test `is_some`
    assert!(some.is_some() && !none.is_some());
    // Test `is_none`
    assert!(none.is_none() && !some.is_none());

    // Test `unwrap`
    assert!(some.unwrap() == 1);
    // Test `expect`
    assert!(some.expect("failed") == 1);

    // Test `unwrap_or`
    assert!(some.unwrap_or(2) == 1);
    assert!(none.unwrap_or(2) == 2);
    // // Test `unwrap_or_else`
    // assert!(some.unwrap_or_else(|| 2) == 1);
    // assert!(none.unwrap_or_else(|| 2) == 2);

    // Test `as_mut`
    assert!(none.as_mut().is_none());
    *some.as_mut().unwrap() = 2;
    assert!(some.unwrap() == 2);
    *some.as_mut().unwrap() = 1;
    assert!(some.unwrap() == 1);
    // Test `as_ref`
    assert!(none.as_ref().is_none());
    assert!(*some.as_ref().unwrap() == 1);

    // // Test `ok_or`
    // assert!(none.ok_or(2) == Err(2));
    // assert!(some.ok_or(2) == Ok(1));
    // // Test `ok_or_else`
    // assert!(none.ok_or_else(|| 2) == Err(2));
    // assert!(some.ok_or_else(|| 2) == Ok(1));

    // // Test `map`
    // assert!(none.map(|x| x + 1).is_none());
    // assert!(some.map(|x| x + 1).unwrap() == 2);
    // // Test `map_or`
    // assert!(none.map_or(5, |x| x + 1) == 5);
    // assert!(some.map_or(5, |x| x + 1) == 2);
    // // Test `map_or_else`
    // assert!(none.map_or_else(|| 5, |x| x + 1) == 5);
    // assert!(some.map_or_else(|| 5, |x| x + 1) == 2);

    // Test `and`
    assert!(none.and(none).is_none());
    assert!(none.and(Some(2)).is_none());
    assert!(some.and(none).is_none());
    assert!(some.and(Some(2)).unwrap() == 2);
    // // Test `and_then`
    // assert!(none.and_then(|_| none).is_none());
    // assert!(none.and_then(|x| Some(x + 1)).is_none());
    // assert!(some.and_then(|_| none).is_none());
    // assert!(some.and_then(|x| Some(x + 1)).unwrap() == 2);
    // Test `or`
    assert!(none.or(none).is_none());
    assert!(none.or(Some(2)).unwrap() == 2);
    assert!(some.or(none).unwrap() == 1);
    assert!(some.or(Some(2)).unwrap() == 1);
    // // Test `or_else`
    // assert!(none.or_else(|| none).is_none());
    // assert!(none.or_else(|| Some(2)).unwrap() == 2);
    // assert!(some.or_else(|| none).unwrap() == 1);
    // assert!(some.or_else(|| Some(2)).unwrap() == 1);

    // // Test `filter`
    // assert!(none.filter(|x| *x == 1).is_none());
    // assert!(some.filter(|x| *x == 1).unwrap() == 1);
    // assert!(some.filter(|x| *x == 2).is_none());

    // Test `take`
    assert!(none.take().is_none());
    assert!(none.is_none());
    assert!(some.take().unwrap() == 1);
    assert!(some.is_none());
    some = Some(1);
    // Test `replace`
    assert!(none.replace(2).is_none());
    assert!(none.unwrap() == 2);
    none = None;
    assert!(some.replace(2).unwrap() == 1);
    assert!(some.unwrap() == 2);
    assert!(some.replace(1).unwrap() == 2);
    assert!(some.unwrap() == 1);

    // Test `unwrap_or_default`
    assert!(none.unwrap_or_default() == 0);
    assert!(some.unwrap_or_default() == 1);

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

    // Test `flatten`
    let opt: Option<Option<i32>> = None;
    assert!(opt.flatten().is_none());
    let opt: Option<Option<i32>> = Some(None);
    assert!(opt.flatten().is_none());
    let opt: Option<Option<i32>> = Some(Some(1));
    assert!(opt.flatten().unwrap() == 1);
}
