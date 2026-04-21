extern crate creusot_std;

struct Q<T>(T);

impl<T> Q<T> {
    const W: Option<T> = const { None };
}

pub fn f<T>() -> Option<Option<T>> {
    <Q<Option<T>>>::W
}
