extern crate creusot_contracts;

pub fn test_result() {
    let mut ok: Result<i32, i32> = Ok(1);
    let mut err: Result<i32, i32> = Err(-1);

    // Test `is_ok`
    assert!(ok.is_ok() && !err.is_ok());
    // Test `is_err`
    assert!(err.is_err() && !ok.is_err());

    // Test `ok`
    assert!(ok.ok().unwrap() == 1);
    assert!(err.ok().is_none());
    // Test `err`
    assert!(ok.err().is_none());
    assert!(err.err().unwrap() == -1);

    // Test `as_ref`
    assert!(*ok.as_ref().unwrap() == 1);
    assert!(*err.as_ref().unwrap_err() == -1);
    // Test `as_mut`
    *ok.as_mut().unwrap() = 0;
    assert!(ok.unwrap() == 0);
    *ok.as_mut().unwrap() = 1;
    assert!(ok.unwrap() == 1);
    *err.as_mut().unwrap_err() = 0;
    assert!(err.unwrap_err() == 0);
    *err.as_mut().unwrap_err() = -1;
    assert!(err.unwrap_err() == -1);

    // Test `unwrap`
    assert!(ok.unwrap() == 1);
    // Test `expect`
    assert!(ok.expect("failed") == 1);
    // Test `unwrap_err`
    assert!(err.unwrap_err() == -1);

    // Test `unwrap_or`
    assert!(ok.unwrap_or(0) == 1);
    assert!(err.unwrap_or(0) == 0);
    // Test `unwrap_or_default`
    assert!(ok.unwrap_or_default() == 1);
    assert!(err.unwrap_or_default() == 0);
    // // Test `unwrap_or_else`
    // assert!(ok.unwrap_or_else(|x| x - 1) == 1);
    // assert!(err.unwrap_or_else(|x| x - 1) == -2);

    // // Test `map`
    // assert!(ok.map(|x| x + 1).unwrap() == 2);
    // assert!(err.map(|x| x + 1).unwrap_err() == -1);
    // // Test `map_or`
    // assert!(ok.map_or(0, |x| x + 1) == 2);
    // assert!(err.map_or(0, |x| x + 1) == 0);
    // // Test `map_or_else`
    // assert!(ok.map_or_else(|x| x - 1, |x| x + 1) == 2);
    // assert!(err.map_or_else(|x| x - 1, |x| x + 1) == -2);
    // // Test `map_err`
    // assert!(ok.map_err(|x| x - 1).unwrap() == 1);
    // assert!(err.map_err(|x| x - 1).unwrap_err() == -2);

    // Test `and`
    assert!(ok.and::<i32>(Err(-2)).unwrap_err() == -2);
    assert!(ok.and(Ok(2)).unwrap() == 2);
    assert!(err.and::<i32>(Err(-2)).unwrap_err() == -1);
    assert!(err.and(Ok(2)).unwrap_err() == -1);
    // // Test `and_then`
    // assert!(ok.and_then(|x| Err::<i32, i32>(x + 1)).unwrap_err() == 2);
    // assert!(ok.and_then(|x| Ok(x + 1)).unwrap() == 2);
    // assert!(err.and_then(|x| Err::<i32, i32>(x - 1)).unwrap_err() == -1);
    // assert!(err.and_then(|x| Ok(x - 1)).unwrap_err() == -1);

    // Test `or`
    assert!(ok.or(Err(-2)).unwrap() == 1);
    assert!(ok.or::<i32>(Ok(2)).unwrap() == 1);
    assert!(err.or(Err(-2)).unwrap_err() == -2);
    assert!(err.or::<i32>(Ok(2)).unwrap() == 2);
    // // Test `or_else`
    // assert!(ok.or_else(|x| Err(x + 1)).unwrap() == 1);
    // assert!(ok.or_else(|x| Ok::<i32, i32>(x + 1)).unwrap() == 1);
    // assert!(err.or_else(|x| Err(x - 1)).unwrap_err() == -2);
    // assert!(err.or_else(|x| Ok::<i32, i32>(x - 1)).unwrap() == -2);

    // Test `copied`
    assert!(ok.as_ref().copied().unwrap() == 1);
    assert!(*err.as_ref().copied().unwrap_err() == -1);
    assert!(ok.as_mut().copied().unwrap() == 1);
    assert!(*err.as_mut().copied().unwrap_err() == -1);
    // Test `cloned`
    assert!(ok.as_ref().cloned().unwrap() == 1);
    assert!(*err.as_ref().cloned().unwrap_err() == -1);
    assert!(ok.as_mut().cloned().unwrap() == 1);
    assert!(*err.as_mut().cloned().unwrap_err() == -1);

    // Test `transpose`
    let res: Result<Option<i32>, i32> = Ok(None);
    assert!(res.transpose().is_none());
    let res: Result<Option<i32>, i32> = Ok(Some(1));
    assert!(res.transpose().unwrap().unwrap() == 1);
    let res: Result<Option<i32>, i32> = Err(-1);
    assert!(res.transpose().unwrap().unwrap_err() == -1);
}
