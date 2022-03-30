trait Tr {
    type A;
}

struct Assoc<T: Tr> {
    item: T::A,
}

fn uses<T: Tr>(x: Assoc<T>) {}
