use smallvec::SmallVec;
use std::{
    fmt::{Debug, Formatter},
    iter, slice,
};

type BitVecElt = u32;
const BITS: u8 = BitVecElt::BITS as u8;
const BITS_USIZE: usize = BitVecElt::BITS as usize;

pub struct BitVec {
    data: SmallVec<[BitVecElt; 4]>,
    extra_len: u8,
}

impl Default for BitVec {
    fn default() -> Self {
        BitVec { data: SmallVec::new(), extra_len: BITS }
    }
}

impl BitVec {
    pub fn push(&mut self, b: bool) {
        if self.extra_len == BITS {
            self.data.push(0);
            self.extra_len = 0;
        }
        let last = self.data.last_mut().unwrap();
        *last |= (b as BitVecElt) << self.extra_len;
        self.extra_len += 1
    }

    pub fn len(&self) -> usize {
        (self.data.len() * BITS_USIZE) + self.extra_len as usize - BITS_USIZE
    }

    pub fn get(&self, idx: usize) -> bool {
        assert!(idx <= self.len());
        let elt = self.data[idx / BITS_USIZE];
        elt & (1 << (idx % BITS_USIZE)) != 0
    }

    pub fn set(&mut self, idx: usize, b: bool) {
        assert!(idx <= self.len());
        let elt = &mut self.data[idx / BITS_USIZE];
        *elt |= (b as BitVecElt) << (idx % BITS_USIZE)
    }

    pub fn iter(&self) -> Iter<'_> {
        self.into_iter()
    }
}

pub struct Biterator {
    bits: BitVecElt,
    elts: u8,
}

impl Biterator {
    fn new_full(bits: BitVecElt) -> Biterator {
        Biterator { bits, elts: BITS }
    }
}

pub type Iter<'a> = iter::Chain<
    iter::FlatMap<iter::Copied<slice::Iter<'a, BitVecElt>>, Biterator, fn(BitVecElt) -> Biterator>,
    Biterator,
>; // TODO use TAIT

impl<'a> IntoIterator for &'a BitVec {
    type Item = bool;
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        match self.data.split_last() {
            None => (&[] as &[BitVecElt])
                .iter()
                .copied()
                .flat_map(Biterator::new_full as _)
                .chain(Biterator { bits: 0, elts: 0 }),
            Some((&bits, rest)) => rest
                .iter()
                .copied()
                .flat_map(Biterator::new_full as _)
                .chain(Biterator { bits, elts: self.extra_len }),
        }
    }
}

impl Iterator for Biterator {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.elts == 0 {
            None
        } else {
            let b = self.bits & 1 != 0;
            self.bits >>= 1;
            self.elts -= 1;
            Some(b)
        }
    }
}

impl Debug for BitVec {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.into_iter()).finish()
    }
}
