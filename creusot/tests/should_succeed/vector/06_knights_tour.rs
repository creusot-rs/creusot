extern crate creusot_contracts;
use creusot_contracts::{derive::Clone, *};

#[derive(Copy, Clone)]
struct Point {
    x: isize,
    y: isize,
}

// ISSUE: patterns in function binders are unsupported!
impl Point {
    #[requires(-10000 <= @self.x && @self.x <= 10000)]
    #[requires(-10000 <= @self.y && @self.y <= 10000)]
    #[requires(-10000 <= @p.0 && @p.0 <= 10000)]
    #[requires(-10000 <= @p.1 && @p.1 <= 10000)]
    #[ensures(@result.x == @self.x + @p.0)]
    #[ensures(@result.y == @self.y + @p.1)]
    fn mov(&self, p: &(isize, isize)) -> Self {
        Self { x: (self.x + p.0), y: (self.y + p.1) }
    }
}

pub struct Board {
    pub size: usize,
    pub field: Vec<Vec<usize>>,
}

impl Board {
    #[predicate]
    fn wf(self) -> bool {
        pearlite! {
            @self.size <= 1_000 &&
            (@self.field).len() == @self.size &&
            forall<i : Int> 0 <= i && i < @self.size ==> (@(@self.field)[i]).len() == @self.size
        }
    }
    #[requires(@size <= 1000)]
    #[ensures(result.size == size)]
    #[ensures(result.wf())]
    fn new(size: usize) -> Self {
        let mut rows: Vec<Vec<_>> = Vec::with_capacity(size);

        let mut i = 0;
        #[invariant(i_size, i <= size)]
        #[invariant(rows,
            forall<j : Int> 0 <= j && j < @i ==> (@(@rows)[j]).len() == @size)]
        #[invariant(row_len, (@rows).len() == @i )]
        while i < size {
            rows.push(std::vec::from_elem(0, size));
            i += 1;
        }

        Self { size, field: rows }
    }

    #[requires(self.wf())]
    #[ensures(result ==> self.in_bounds(p))]
    fn available(&self, p: Point) -> bool {
        0 <= p.x
            && (p.x as usize) < self.size
            && 0 <= p.y
            && (p.y as usize) < self.size
            && self.field[p.x as usize][p.y as usize] == 0
    }

    #[predicate]
    fn in_bounds(self, p: Point) -> bool {
        pearlite! {
            0 <= @p.x && @p.x< @self.size && 0 <= @p.y && @p.y < @self.size
        }
    }

    // calculate the number of possible moves
    #[requires(self.wf())]
    #[requires(self.in_bounds(p))]
    fn count_degree(&self, p: Point) -> usize {
        let mut count = 0;

        let mut i = 0;
        #[invariant(count, count <= i)]
        while i < moves().len() {
            let next = p.mov(&moves()[i]);
            if self.available(next) {
                count += 1;
            }
            i += 1;
        }
        count
    }

    #[requires(self.wf())]
    #[requires(self.in_bounds(p))]
    #[ensures((^self).wf())]
    #[ensures((^self).size == (*self).size)]
    fn set(&mut self, p: Point, v: usize) {
        self.field[p.x as usize][p.y as usize] = v
    }
}

#[trusted]
#[ensures((@result).len() == 8)]
#[ensures(forall<i : Int> 0 <= i && i < 8 ==> -2 <= @(@result)[i].0 && @(@result)[i].0 <= 2 && -2 <= @(@result)[i].1 && @(@result)[i].1 <= 2)]
fn moves() -> Vec<(isize, isize)> {
    let mut v = Vec::new();
    v.push((2, 1));
    v.push((1, 2));
    v.push((-1, 2));
    v.push((-2, 1));
    v.push((-2, -1));
    v.push((-1, -2));
    v.push((1, -2));
    v.push((2, -1));

    v
}

#[ensures(forall<r: &(usize, Point)> result == Some(r) ==>
          exists<i:Int> 0 <= i && i < (@v).len() && (@v)[i] == *r)]
fn min(v: &Vec<(usize, Point)>) -> Option<&(usize, Point)> {
    let mut i = 0;
    let mut min = None;
    #[invariant(post, forall<r: &(usize, Point)> min == Some(r) ==>
                      exists<i:Int> 0 <= i && i < (@v).len() && (@v)[i] == *r)]
    while i < v.len() {
        match min {
            None => min = Some(&v[i]),
            Some(m) => {
                if v[i].0 < m.0 {
                    min = Some(&v[i])
                }
            }
        };
        i += 1;
    }
    min
}

#[logic]
#[requires(@a <= 1_000)]
#[ensures(@a * @a <= 1_000_000)]
fn dumb_nonlinear_arith(a: usize) {}

#[requires(0 < @size && @size <= 1000)]
#[requires(x < size)]
#[requires(y < size)]
pub fn knights_tour(size: usize, x: usize, y: usize) -> Option<Board> {
    let mut board = Board::new(size);
    let mut p = Point { x: x as isize, y: y as isize };
    let mut step = 1;

    board.set(p, step);
    step += 1;

    ghost! { dumb_nonlinear_arith(size) };
    #[invariant(b, board.size == size)]
    #[invariant(b, board.wf())]
    #[invariant(p, board.in_bounds(p))]
    // rather annoyingly z3 gets stuck proving size * size is inbounds, seemingly
    // due to a why3 bug / limitation in mlcfg
    while step <= (size * size) {
        // choose next square by Warnsdorf's rule
        let mut candidates: Vec<(usize, Point)> = Vec::new();
        let mut i = 0;
        #[invariant(c, forall<i: Int> 0 <= i && i < (@candidates).len() ==>
                    board.in_bounds((@candidates)[i].1))]
        while i < moves().len() {
            let adj = p.mov(&moves()[i]);
            if board.available(adj) {
                let degree = board.count_degree(adj);
                candidates.push((degree, adj));
            }
            i += 1;
        }
        match min(&candidates) {
            Some(&(_, adj)) => p = adj,
            None => return None,
        };
        board.set(p, step);
        step += 1;
    }
    Some(board)
}

// fn main() {
//     let (x, y) = (3, 1);
//     // println!("Board size: {}", SIZE);
//     // println!("Starting position: ({}, {})", x, y);
//     // match knights_tour(x, y) {
//     //     Some(b) => print!("{}", b),
//     //     None => println!("Fail!"),
//     // }
// }
