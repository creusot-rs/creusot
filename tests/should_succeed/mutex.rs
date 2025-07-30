extern crate creusot_contracts;

use creusot_contracts::*;

pub trait Inv<T> {
    #[logic]
    fn inv(&self, x: T) -> bool;
}

#[trusted]
struct MutexInner<T>(std::sync::Mutex<T>);

pub struct Mutex<T, I>(MutexInner<T>, I);
// We ignore poisoning, thus we don't use `LockResult` like in `std`.
impl<T, I: Inv<T>> Mutex<T, I> {
    #[trusted]
    #[requires(i.inv(val))]
    pub fn new(val: T, i: I) -> Self {
        Mutex(MutexInner(std::sync::Mutex::new(val)), i)
    }

    #[trusted]
    #[ensures(self.1.inv(result))]
    pub fn into_inner(self) -> T {
        self.0.0.into_inner().unwrap()
    }

    #[trusted]
    #[ensures((*self).1.inv(*result))]
    #[ensures(forall<v: T> (^self).1.inv(v) == true)]
    pub fn get_mut(&mut self) -> &mut T {
        self.0.0.get_mut().unwrap()
    }

    #[trusted]
    #[ensures(self.1 == *result.1)]
    pub fn lock(&self) -> MutexGuard<'_, T, I> {
        MutexGuard(GuardInner(self.0.0.lock().unwrap()), snapshot! { self.1 })
    }
}

#[trusted]
struct GuardInner<'a, T: ?Sized + 'a>(std::sync::MutexGuard<'a, T>);

pub struct MutexGuard<'a, T: ?Sized + 'a, I>(GuardInner<'a, T>, Snapshot<I>);

impl<'a, T, I: Inv<T>> MutexGuard<'a, T, I> {
    #[trusted]
    #[ensures(self.1.inv(*result))]
    fn deref(&self) -> &T {
        &*self.0.0
    }

    #[trusted]
    #[requires(self.1.inv(v))]
    fn set(&mut self, v: T) {
        *self.0.0 = v;
    }
}

struct Even;

impl Inv<u32> for Even {
    #[open(self)]
    #[logic]
    fn inv(&self, x: u32) -> bool {
        x.view() % 2 == 0
    }
}

struct AddsTwo<'a> {
    mutex: &'a Mutex<u32, Even>,
}

trait FakeFnOnce {
    type Return;
    #[logic]
    fn precondition(self) -> bool;

    #[logic]
    fn postcondition(self, _: Self::Return) -> bool;

    #[requires(self.precondition())]
    #[ensures(self.postcondition(result))]
    fn call(self) -> Self::Return;
}

impl<'a> FakeFnOnce for AddsTwo<'a> {
    type Return = ();
    #[logic]
    fn precondition(self) -> bool {
        true
    }

    #[logic]
    fn postcondition(self, _: ()) -> bool {
        true
    }

    fn call(self) -> () {
        let mut v = self.mutex.lock();
        let val = *v.deref();
        if val < 100000 {
            v.set(val + 2);
        } else {
            v.set(0);
        }
    }
}

#[trusted]
struct JoinHandleInner<T>(std::thread::JoinHandle<T>);
struct JoinHandle<T, I>(JoinHandleInner<T>, Snapshot<I>);

impl<T, I: Inv<T>> JoinHandle<T, I> {
    #[trusted]
    #[ensures(match result {
      Ok(v) => self.1.inv(v),
      _ => true,
    })]
    fn join(self) -> Result<T, ()> {
        match self.0.0.join() {
            Ok(v) => Ok(v),
            Err(_) => Err(()),
        }
    }
}

#[trusted]
#[requires(f.precondition())]
fn spawn<T: Send + 'static, F: Send + 'static + FakeFnOnce<Return = T>>(
    f: F,
) -> JoinHandle<T, SpawnPostCond<F>> {
    JoinHandle(
        JoinHandleInner(std::thread::spawn(
            #[creusot::no_translate]
            || f.call(),
        )),
        snapshot! { SpawnPostCond { f } },
    )
}

struct SpawnPostCond<F> {
    f: F,
}

impl<F: FakeFnOnce> Inv<F::Return> for SpawnPostCond<F> {
    #[open(self)]
    #[logic]
    fn inv(&self, v: F::Return) -> bool {
        self.f.postcondition(v)
    }
}

// A version of Box::leak

#[trusted]
#[ensures(*result == *b)]
fn leak<'a, T: 'a>(b: Box<T>) -> &'a mut T {
    Box::leak(b)
}

pub fn concurrent() {
    let m: &'static _ = leak(Box::new(Mutex::new(0, Even)));
    let t1 = AddsTwo { mutex: &m };
    let j1 = spawn(t1);
    let t2 = AddsTwo { mutex: &m };
    let j2 = spawn(t2);

    // FIXME: cannot unwrap() here
    let _ = j1.join();
    let _ = j2.join();

    // assert!(m.into_inner() % 2 == 0);
}
