extern crate creusot_std;

mod imp {
    use core::ptr::null;
    use creusot_std::{ghost::perm::Perm, prelude::*};

    struct Node<T> {
        data: T,
        next: *const Self,
        prev: *const Self,
    }

    /// A doubly linked list implemented with pointers.
    ///
    /// To insert elements in the middle of the list, use a [`Cursor`].
    pub struct List<T> {
        permissions: Ghost<Seq<Box<Perm<*const Node<T>>>>>,
        head: *const Node<T>,
        tail: *const Node<T>,
    }

    /// A cursor into a [`List`], that can be used to insert elements in the middle.
    pub struct Cursor<'a, T> {
        list: &'a mut List<T>,
        pos: Ghost<Int>,
        current: *const Node<T>,
    }

    /// Logical definitions for [`Cursor`]
    impl<'a, T> Cursor<'a, T> {
        /// The list that the cursor is visiting.
        #[logic]
        pub fn list(self) -> &'a mut List<T> {
            self.list
        }

        /// The current position of the cursor in the [list](Self::list).
        #[logic]
        #[requires(inv(self))]
        #[ensures(self.list()@.len() > 0 ==>
            0 <= result && result < self.list()@.len()
        )]
        pub fn pos(self) -> Int {
            *self.pos
        }
    }

    impl<T> Invariant for List<T> {
        #[logic(inline)]
        fn invariant(self) -> bool {
            pearlite! {
                let len = self.permissions.len();
                if len == 0 {
                    self.head.is_null_logic() && self.tail.is_null_logic()
                } else {
                    *self.permissions[0].ward() == self.head &&
                    *self.permissions[len - 1].ward() == self.tail &&
                    self.permissions[0].val().prev.is_null_logic() &&
                    self.permissions[len - 1].val().next.is_null_logic() &&
                    forall<i> 0 <= i && i < len - 1 ==>
                        self.permissions[i].val().next == *self.permissions[i + 1].ward() &&
                        self.permissions[i + 1].val().prev == *self.permissions[i].ward()
                }
            }
        }
    }

    impl<'a, T> Invariant for Cursor<'a, T> {
        #[logic(prophetic, inline)]
        #[ensures(result ==> inv(self.list()))]
        fn invariant(self) -> bool {
            pearlite! {
                inv(self.list) &&
                (self.list()@.len() > 0 ==>
                    0 <= *self.pos && *self.pos < self.list()@.len() &&
                    self.current == *self.list.permissions[*self.pos].ward())
            }
        }
    }

    impl<T> View for List<T> {
        type ViewTy = Seq<T>;
        #[logic]
        fn view(self) -> Seq<T> {
            self.permissions.map(|p: Box<Perm<*const Node<T>>>| p.val().data)
        }
    }

    impl<T> View for Cursor<'_, T> {
        type ViewTy = Seq<T>;

        #[logic(open)]
        fn view(self) -> Seq<T> {
            self.list().view()
        }
    }

    impl<T> Resolve for Cursor<'_, T> {
        #[logic(open, inline, prophetic)]
        fn resolve(self) -> bool {
            resolve(self.list())
        }

        #[logic(prophetic)]
        #[requires(inv(self))]
        #[requires(creusot_std::resolve::structural_resolve(self))]
        #[ensures(self.resolve())]
        fn resolve_coherence(self) {}
    }

    impl<T> List<T> {
        /// Creates an empty doubly linked list.
        ///
        /// This requires proving that `T` is inhabited, so that the allocated
        /// pointers do not alias each other.
        #[ensures(result@ == Seq::empty())]
        pub fn new() -> Self {
            let permissions = Seq::new();
            Self { permissions, head: null(), tail: null() }
        }

        /// Returns a reference to the first element of the list if it exists.
        #[ensures(if self@.len() == 0 {
            result == None
        } else {
            result == Some(&self@[0])
        })]
        pub fn get_head(&self) -> Option<&T> {
            if self.head.is_null() {
                return None;
            }
            Some(&unsafe { Perm::as_ref(self.head, ghost!(&*self.permissions[0int])) }.data)
        }

        /// Returns a reference to the last element of the list if it exists.
        #[ensures(if self@.len() == 0 {
            result == None
        } else {
            result == Some(&self@[self@.len() - 1])
        })]
        pub fn get_tail(&self) -> Option<&T> {
            if self.tail.is_null() {
                return None;
            }
            Some(
                &unsafe {
                    Perm::as_ref(
                        self.tail,
                        ghost!(&*self.permissions[self.permissions.len_ghost() - 1int]),
                    )
                }
                .data,
            )
        }

        /// Returns a mutable reference to the first element of the list if it exists.
        #[ensures(match result {
            None => self@.len() == 0 && *self == ^self,
            Some(r) => self@.len() > 0 &&
                (*self)@.len() == (^self)@.len() &&
                (*self)@[0] == *r && (^self)@[0] == ^r &&
                forall<i> 0 < i && i < self@.len() ==>
                    (*self)@[i] == (^self)@[i],
        })]
        pub fn get_head_mut(&mut self) -> Option<&mut T> {
            if self.head.is_null() {
                return None;
            }
            Some(
                &mut unsafe {
                    Perm::as_mut(self.head.cast_mut(), ghost!(&mut *self.permissions[0int]))
                }
                .data,
            )
        }

        /// Returns a mutable reference to the last element of the list if it exists.
        #[ensures(match result {
            None => self@.len() == 0 && *self == ^self,
            Some(r) => {
                let len = self@.len();
                len > 0 &&
                len == (^self)@.len() &&
                (*self)@[len - 1] == *r &&
                (^self)@[len - 1] == ^r &&
                forall<i> 0 <= i && i < self@.len() - 1 ==>
                    (*self)@[i] == (^self)@[i]
            }
        })]
        pub fn get_tail_mut(&mut self) -> Option<&mut T> {
            if self.tail.is_null() {
                return None;
            }
            Some(
                &mut unsafe {
                    Perm::as_mut(
                        self.tail.cast_mut(),
                        ghost! {
                            let last = self.permissions.len_ghost() - 1int;
                            &mut *self.permissions[last]
                        },
                    )
                }
                .data,
            )
        }

        /// Add an element to the front of the list
        #[ensures((^self)@ == (*self)@.push_front(value))]
        pub fn push_front(&mut self, value: T) {
            let (new_head, perm) = Perm::new(Node { data: value, next: self.head, prev: null() });
            if self.head.is_null() {
                self.head = new_head;
                self.tail = new_head;
            } else {
                unsafe {
                    let head =
                        Perm::as_mut(self.head.cast_mut(), ghost!(&mut self.permissions[0int]));
                    head.prev = new_head;
                    self.head = new_head;
                }
            }
            ghost! {
                self.permissions.push_front_ghost(perm.into_inner())
            };
        }

        /// Add an element to the end of the list
        #[ensures((^self)@ == (*self)@.push_back(value))]
        pub fn push_back(&mut self, value: T) {
            let (new_tail, perm) = Perm::new(Node { data: value, next: null(), prev: self.tail });
            if self.tail.is_null() {
                self.head = new_tail;
                self.tail = new_tail;
            } else {
                unsafe {
                    let tail = Perm::as_mut(
                        self.tail.cast_mut(),
                        ghost! {
                            let idx = self.permissions.len_ghost() - 1int;
                            &mut self.permissions[idx]
                        },
                    );
                    tail.next = new_tail;
                    self.tail = new_tail;
                }
            }
            ghost! {
                self.permissions.push_back_ghost(perm.into_inner())
            };
        }

        /// If the list is not empty, removes an element from the front and returns it.
        #[ensures(if self@.len() == 0 {
            result == None && ^self == *self
        } else {
           result == Some(self@[0]) && (^self)@ == (*self)@.pop_front()
        })]
        pub fn pop_front(&mut self) -> Option<T> {
            if self.head.is_null() {
                return None;
            }
            let head_perm = ghost!(self.permissions.pop_front_ghost().unwrap());
            let elem = self.head;
            self.head = unsafe { Perm::as_ref(elem, ghost!(&**head_perm)) }.next;
            if !self.head.is_null() {
                unsafe {
                    Perm::as_mut(self.head.cast_mut(), ghost!(&mut self.permissions[0int])).prev =
                        null()
                };
            } else {
                self.tail = null();
            }
            Some(unsafe { Perm::to_box(elem.cast_mut(), head_perm) }.data)
        }

        /// If the list is not empty, removes an element from the back and returns it.
        #[ensures(if self@.len() == 0 {
            result == None && ^self == *self
        } else {
           result == Some(self@[self@.len() - 1]) && (^self)@ == (*self)@.pop_back()
        })]
        pub fn pop_back(&mut self) -> Option<T> {
            if self.tail.is_null() {
                return None;
            }
            let tail_perm = ghost!(self.permissions.pop_back_ghost().unwrap());
            let elem = self.tail;
            self.tail = unsafe { Perm::as_ref(elem, ghost!(&**tail_perm)) }.prev;
            if !self.tail.is_null() {
                proof_assert!(self.permissions.len() > 0);
                let last_idx: Snapshot<Int> = snapshot!(self.permissions.len() - 1);
                unsafe {
                    Perm::as_mut(
                        self.tail.cast_mut(),
                        ghost!(&mut self.permissions[*last_idx.into_ghost()]),
                    )
                    .next = null()
                };
            } else {
                self.head = null();
            }
            Some(unsafe { Perm::to_box(elem.cast_mut(), tail_perm) }.data)
        }

        /// Get a cursor to the front of the list
        #[ensures(result.list() == self)]
        #[ensures(result.pos() == 0)]
        pub fn cursor_front<'a>(&'a mut self) -> Cursor<'a, T> {
            Cursor { current: self.head, list: self, pos: ghost!(0int) }
        }

        /// Get a cursor to the tail of the list
        #[ensures(result.list() == self)]
        #[ensures(result.pos() == self@.len() - 1)]
        pub fn cursor_tail<'a>(&'a mut self) -> Cursor<'a, T> {
            Cursor {
                pos: ghost!(self.permissions.len_ghost() - 1int),
                current: self.tail,
                list: self,
            }
        }
    }

    impl<T> Drop for List<T> {
        fn drop(&mut self) {
            while !self.head.is_null() {
                self.pop_front();
            }
        }
    }

    /// ghost helpers
    impl<T> Cursor<'_, T> {
        /// If the current pointer is the head (and is non-null), then the cursor
        /// points to the first element.
        #[check(ghost)]
        #[requires(self.current == self.list.head)]
        #[requires(!self.current.is_null_logic())]
        #[ensures(*self == ^self)]
        #[ensures(*self.pos == 0)]
        fn ghost_current_at_first(&mut self) {
            ghost! {
                if *self.pos != 0int {
                    let (perm_curr, perm_head) = &mut self.list.permissions[(*self.pos, 0int)];
                    perm_curr.disjoint_lemma(perm_head); // derive a contradiction
                }
            };
        }

        /// If the current pointer is the tail (and is non-null), then the cursor
        /// points to the last element.
        #[check(ghost)]
        #[requires(self.current == self.list.tail)]
        #[requires(!self.current.is_null_logic())]
        #[ensures(*self == ^self)]
        #[ensures(*self.pos == self.list.permissions.len() - 1)]
        fn ghost_current_at_last(&mut self) {
            ghost! {
                let last = self.list.permissions.len_ghost() - 1int;
                if *self.pos != last {
                    let (perm_curr, perm_head) = &mut self.list.permissions[(*self.pos, last)];
                    perm_curr.disjoint_lemma(perm_head); // derive a contradiction
                }
            };
        }
    }

    impl<'a, T> Cursor<'a, T> {
        /// Get a reference to the cursor's current element
        #[ensures(if self.list()@.len() == 0 {
            result == None
        } else {
            result == Some(&self.list()@[self.pos()])
        })]
        pub fn get(&self) -> Option<&T> {
            if self.list.head.is_null() {
                return None;
            }
            let perm = ghost!(&*self.list.permissions[*self.pos]);
            Some(&unsafe { Perm::as_ref(self.current, perm) }.data)
        }

        /// Get a mutable reference to the cursor's current element.
        ///
        /// If the list is empty, returns `None`.
        #[ensures(match result {
            None => self@.len() == 0 && ^self == *self,
            Some(res) => self.list()@.len() > 0 &&
                (^self)@.len() == self.list()@.len() &&
                (^self).pos() == (*self).pos() &&
                *res == (*self).list()@[self.pos()] &&
                ^res == (^self).list()@[self.pos()] &&
                forall<i> 0 <= i && i < self.list()@.len() && i != self.pos() ==>
                    (^self).list()@[i] == (*self).list()@[i]
        })]
        #[ensures(^(^self).list() == ^(*self).list())]
        pub fn get_mut(&mut self) -> Option<&mut T> {
            if self.list.head.is_null() {
                return None;
            }
            let perm = ghost!(&mut *self.list.permissions[*self.pos]);
            Some(&mut unsafe { Perm::as_mut(self.current.cast_mut(), perm) }.data)
        }

        /// Move the cursor position to the next value.
        ///
        /// If the cursor is already at the end of the list, or if the list is
        /// empty, this function does nothing.
        #[ensures((^self).list() == (*self).list())]
        #[ensures(if self.list()@.len() == 0 {
            ^self == *self
        } else if self.pos() == self.list()@.len() - 1 {
            ^self == *self
        } else {
            (^self).pos() == (*self).pos() + 1
        })]
        pub fn move_next(&mut self) {
            if self.list.head.is_null() {
                return;
            }
            if self.current == self.list.tail {
                self.ghost_current_at_last();
                return;
            }
            let next = unsafe {
                Perm::as_ref(self.current, ghost!(&*self.list.permissions[*self.pos])).next
            };
            self.current = next;
            self.pos = ghost!(*self.pos + 1int);
        }

        /// Move the cursor position to the previous value.
        ///
        /// If the cursor is already at the start of the list, or if the list is
        /// empty, this function does nothing.
        #[ensures((^self).list() == (*self).list())]
        #[ensures(if self.list()@.len() == 0 {
            ^self == *self
        } else if self.pos() == 0 {
            ^self == *self
        } else {
            (^self).pos() == (*self).pos() - 1
        })]
        pub fn move_prev(&mut self) {
            if self.list.head.is_null() {
                return;
            }
            if self.current == self.list.head {
                self.ghost_current_at_first();
                return;
            }
            let prev = unsafe {
                Perm::as_ref(self.current, ghost!(&*self.list.permissions[*self.pos])).prev
            };
            self.current = prev;
            self.pos = ghost!(*self.pos - 1int);
        }

        /// Insert an element at the current cursor's position.
        ///
        /// This does _not_ change the cursor's position, meaning it will now
        /// point to the newly inserted element.
        #[ensures(if self.list()@.len() == 0 {
            (^self).pos() == 0 &&
            (^self).list()@ == Seq::singleton(value)
        } else {
            (^self).pos() == self.pos() &&
            (^self).list()@ == self.list()@.insert(self.pos(), value)
        })]
        #[ensures(^(^self).list() == ^(*self).list())]
        pub fn insert_before(&mut self, value: T) {
            if self.list.head.is_null() {
                let (ptr, perm) = Perm::new(Node { data: value, next: null(), prev: null() });
                ghost! {
                    self.list.permissions.push_back_ghost(perm.into_inner());
                };
                self.list.head = ptr;
                self.list.tail = ptr;
                self.current = ptr;
                self.pos = ghost!(0int);
            } else {
                if self.current == self.list.head {
                    self.ghost_current_at_first();
                    let (ptr, perm) =
                        Perm::new(Node { data: value, next: self.current, prev: null() });
                    let current = unsafe {
                        Perm::as_mut(
                            self.current.cast_mut(),
                            ghost!(&mut self.list.permissions[0int]),
                        )
                    };
                    current.prev = ptr;
                    self.list.head = ptr;
                    self.current = ptr;
                    ghost! {
                        self.list.permissions.push_front_ghost(perm.into_inner());
                    };
                } else {
                    let current = unsafe {
                        Perm::as_mut(
                            self.current.cast_mut(),
                            ghost!(&mut self.list.permissions[*self.pos]),
                        )
                    };
                    let prev = current.prev;
                    let (ptr, perm) =
                        Perm::new(Node { data: value, next: self.current, prev: current.prev });

                    current.prev = ptr;
                    self.current = ptr;
                    unsafe {
                        Perm::as_mut(
                            prev.cast_mut(),
                            ghost!(&mut self.list.permissions[*self.pos - 1int]),
                        )
                    }
                    .next = ptr;

                    ghost! {
                        self.list.permissions.insert_ghost(*self.pos, perm.into_inner());
                    };
                }
            }
        }

        /// Insert an element after the cursor's position.
        ///
        /// This does _not_ change the cursor's position, meaning it will still
        /// point to the same element. The only exception is if the list was empty:
        /// in this case, the cursor now points to the newly inserted value.
        #[ensures(if self.list()@.len() == 0 {
            (^self).pos() == 0 &&
            (^self).list()@ == Seq::singleton(value)
        } else {
            (^self).pos() == self.pos() &&
            (^self).list()@ == self.list()@.insert(self.pos() + 1, value)
        })]
        #[ensures(^(^self).list() == ^(*self).list())]
        pub fn insert_after(&mut self, value: T) {
            if self.list.head.is_null() {
                let (ptr, perm) = Perm::new(Node { data: value, next: null(), prev: null() });
                ghost! {
                    self.list.permissions.push_back_ghost(perm.into_inner());
                };
                self.list.head = ptr;
                self.list.tail = ptr;
                self.current = ptr;
                self.pos = ghost!(0int);
            } else {
                if self.current == self.list.tail {
                    self.ghost_current_at_last();
                    let (ptr, perm) =
                        Perm::new(Node { data: value, next: null(), prev: self.current });
                    let current = unsafe {
                        let last: Snapshot<Int> = snapshot!(self.list.permissions.len() - 1);
                        Perm::as_mut(
                            self.current.cast_mut(),
                            ghost!(&mut self.list.permissions[*last.into_ghost()]),
                        )
                    };
                    current.next = ptr;
                    self.list.tail = ptr;
                    ghost! {
                        self.list.permissions.push_back_ghost(perm.into_inner());
                    };
                } else {
                    let current = unsafe {
                        Perm::as_mut(
                            self.current.cast_mut(),
                            ghost!(&mut self.list.permissions[*self.pos]),
                        )
                    };
                    let next = current.next;
                    let (ptr, perm) =
                        Perm::new(Node { data: value, next: current.next, prev: self.current });

                    current.next = ptr;
                    unsafe {
                        Perm::as_mut(
                            next.cast_mut(),
                            ghost!(&mut self.list.permissions[*self.pos + 1int]),
                        )
                    }
                    .prev = ptr;

                    ghost! {
                        self.list.permissions.insert_ghost(*self.pos + 1int, perm.into_inner());
                    };
                }
            }
        }
    }
}

use creusot_std::prelude::*;
pub use imp::{Cursor, List};

pub fn example() {
    let mut list = List::new();
    assert!(list.pop_back() == None);
    assert!(list.pop_front() == None);

    list.push_back(2);
    list.push_front(1);
    proof_assert!(list@ == seq![1i32, 2i32]);

    list.push_back(3);
    proof_assert!(list@ == seq![1i32, 2i32, 3i32]);

    let mut cursor = list.cursor_front();

    assert!(*cursor.get().unwrap() == 1);
    cursor.insert_after(10);
    cursor.insert_after(11);
    proof_assert!(cursor@ == seq![1i32, 11i32, 10i32, 2i32, 3i32]);
    assert!(*cursor.get().unwrap() == 1);

    cursor.move_next();
    cursor.move_next();
    cursor.move_next();
    assert!(*cursor.get().unwrap() == 2);
    cursor.insert_before(12);
    proof_assert!(cursor@ == seq![1i32, 11i32, 10i32, 12i32, 2i32, 3i32]);
    assert!(*cursor.get().unwrap() == 12);

    cursor.move_prev();
    cursor.move_prev();
    cursor.move_prev();
    cursor.move_prev();
    assert!(*cursor.get().unwrap() == 1);

    assert_eq!(list.pop_back(), Some(3));
    assert_eq!(list.pop_back(), Some(2));
    assert_eq!(list.pop_front(), Some(1));

    proof_assert!(list@ == seq![11i32, 10i32, 12i32]);
}
