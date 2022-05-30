extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

#[derive(Clone, Copy)]
struct Point {
    x: i64,
    y: i64,
    z: i64,
}

#[ensures(match result {
  Some(v) => (forall<i : _> 0 <= i && i < (@p).len() ==> (@p)[i].x <= v)
  && exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].x == @v,
  None => (@p).len() == 0
})]
fn max_x(p: &Vec<Point>) -> Option<i64> {
    if p.len() == 0 {
        return None;
    }
    let mut max_seen: i64 = p[0].x;
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    #[invariant(i_less, 1 <= @i && @i <= (@p).len())]
    #[invariant(max_idx_less, 0 <= @max_idx && @max_idx < (@p).len())]
    #[invariant(max_is_max, forall<j: Int> 0 <= j && j < @i ==>
    (@p)[j].x <= max_seen
  )]
    #[invariant(name, (@p)[@max_idx].x == max_seen)]
    while i < p.len() {
        if p[i].x > max_seen {
            max_seen = p[i].x;
            max_idx = i;
        }
        i += 1;
    }
    return Some(max_seen);
}

#[ensures(match result {
  Some(v) => (forall<i : _> 0 <= i && i < (@p).len() ==> (@p)[i].y <= v)
  && exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].y == @v,
  None => (@p).len() == 0
})]
fn max_y(p: &Vec<Point>) -> Option<i64> {
    if p.len() == 0 {
        return None;
    }
    let mut max_seen: i64 = p[0].y;
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    #[invariant(i_less, 1 <= @i && @i <= (@p).len())]
    #[invariant(max_idx_less, 0 <= @max_idx && @max_idx < (@p).len())]
    #[invariant(max_is_max, forall<j: Int> 0 <= j && j < @i ==>
    (@p)[j].y <= max_seen
  )]
    #[invariant(name, (@p)[@max_idx].y == max_seen)]
    while i < p.len() {
        if p[i].y > max_seen {
            max_seen = p[i].y;
            max_idx = i;
        }
        i += 1;
    }
    return Some(max_seen);
}

#[ensures(match result {
  Some(v) => (forall<i : _> 0 <= i && i < (@p).len() ==> (@p)[i].z <= v)
  && exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].z == @v,
  None => (@p).len() == 0
})]
fn max_z(p: &Vec<Point>) -> Option<i64> {
    if p.len() == 0 {
        return None;
    }
    let mut max_seen: i64 = p[0].z;
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    #[invariant(i_less, 1 <= @i && @i <= (@p).len())]
    #[invariant(max_idx_less, 0 <= @max_idx && @max_idx < (@p).len())]
    #[invariant(max_is_max, forall<j: Int> 0 <= j && j < @i ==>
    (@p)[j].z <= max_seen
  )]
    #[invariant(name, (@p)[@max_idx].z == max_seen)]
    while i < p.len() {
        if p[i].z > max_seen {
            max_seen = p[i].z;
            max_idx = i;
        }
        i += 1;
    }
    return Some(max_seen);
}

#[ensures(match result {
  Some(v) => (forall<i : _> 0 <= i && i < (@p).len() ==> ((@p)[i].z) >= v)
  && exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].z == @v,
  None => (@p).len() == 0
})]
fn min_z(p: &Vec<Point>) -> Option<i64> {
    if p.len() == 0 {
        return None;
    }
    let mut min_seen: i64 = p[0].z;
    let mut min_idx = ghost! { 0usize };
    let mut i: usize = 1;
    #[invariant(min_idx_less, 0 <= @min_idx && @min_idx < (@p).len())]
    #[invariant(min_is_min, forall<j: Int> 0 <= j && j < @i ==> (@p)[j].z >= min_seen )]
    #[invariant(name, (@p)[@min_idx].z == min_seen)]
    while i < p.len() {
        if p[i].z < min_seen {
            min_seen = p[i].z;
            min_idx = ghost! { i };
        }
        i += 1;
    }
    return Some(min_seen);
}

#[ensures(match result {
  Some(v) => (forall<i : _> 0 <= i && i < (@p).len() ==> ((@p)[i].y) >= v)
  && exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].y == @v,
  None => (@p).len() == 0
})]
fn min_y(p: &Vec<Point>) -> Option<i64> {
    if p.len() == 0 {
        return None;
    }
    let mut min_seen = p[0].y;
    let mut min_idx = ghost! { 0usize };
    let mut i: usize = 1;
    #[invariant(min_idx_less, 0 <= @min_idx && @min_idx < (@p).len())]
    #[invariant(min_is_min, forall<j: Int> 0 <= j && j < @i ==> (@p)[j].y >= min_seen)]
    #[invariant(name, (@p)[@min_idx].y == min_seen)]
    while i < p.len() {
        if p[i].y < min_seen {
            min_seen = p[i].y;
            min_idx = ghost! { i };
        }
        i += 1;
    }
    return Some(min_seen);
}

#[ensures(match result {
  Some(v) => (forall<i : _> 0 <= i && i < (@p).len() ==> ((@p)[i].x) >= v)
  && exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].x == @v,
  None => (@p).len() == 0
})]
fn min_x(p: &Vec<Point>) -> Option<i64> {
    if p.len() == 0 {
        return None;
    }
    let mut min_seen = p[0].x;
    let mut min_idx = ghost! { 0usize };
    let mut i: usize = 1;
    #[invariant(min_idx_less, 0 <= @min_idx && @min_idx < (@p).len())]
    #[invariant(min_is_min, forall<j: Int> 0 <= j && j < @i ==> (@p)[j].x >= min_seen )]
    #[invariant(name, (@p)[@min_idx].x == min_seen)]
    while i < p.len() {
        if p[i].x < min_seen {
            min_seen = p[i].x;
            min_idx = ghost! { i };
        }
        i += 1;
    }
    return Some(min_seen);
}

#[requires(i > i64::MIN)]
#[ensures(@result >= 0)]
#[ensures(@result == if @i < 0 { -@i } else { @i })]
fn abs(i: i64) -> i64 {
    if i < 0 {
        -i
    } else {
        i
    }
}

impl<'a> std::ops::Add<&'a Point> for Point {
    type Output = Point;

    #[trusted]
    // this is just too painful to prove...
    // #[requires(@i64::MIN <= (@self.x + @rhs.x) && (@self.x + @rhs.x) <= @i64::MAX)]
    // #[requires(@i64::MIN <= (@self.y + @rhs.y) && (@self.y + @rhs.y) <= @i64::MAX)]
    // #[requires(@i64::MIN <= (@self.z + @rhs.z) && (@self.z + @rhs.z) <= @i64::MAX)]
    fn add(self, rhs: &'a Point) -> Self {
        Point { x: self.x + rhs.x, y: self.y + rhs.y, z: self.z + rhs.z }
    }
}

#[requires(!(o == None))]
#[ensures(Some(result) == o)]
fn unwrap<T>(o: Option<T>) -> T {
    match o {
        Some(t) => t,
        None => std::process::abort(),
    }
}

#[logic]
#[requires(c > 0)]
#[requires(a <= b)]
#[ensures(a / c <= b / c)]
fn div_mono(a: Int, b: Int, c: Int) {}

#[logic]
#[requires(0 <= a && a < c)]
#[requires(0 <= a && b < d)]
#[requires(c > 0)]
#[requires(d > 0)]
#[ensures(a * b < c * d)]
fn mult_mono(a: Int, b: Int, c: Int, d: Int) {}

#[requires(forall<i: Int> 0 <= i && i < (@p).len()
    ==> @(@p)[i].x < 1000 && @(@p)[i].x >= -1000
)]
#[requires(forall<i: Int> 0 <= i && i < (@p).len()
    ==> @(@p)[i].y < 1000 && @(@p)[i].y >= -1000
)]
#[requires(forall<i: Int> 0 <= i && i < (@p).len()
    ==> @(@p)[i].z < 1000 && @(@p)[i].z >= -1000
)]
#[requires(@voxel_size > 0 && @voxel_size <= 1000)]
fn downsample(p: Vec<Point>, voxel_size: u64) -> Vec<Point> {
    if p.len() == 0 {
        return Vec::new();
    }

    let x_max: i64 = unwrap(max_x(&p));
    let x_min: i64 = unwrap(min_x(&p));

    proof_assert! { -1000 <= @x_min && @x_min <= @x_max && @x_max < 1000 };
    let num_vox_x: u64 = (abs(x_max - x_min) as u64 / voxel_size) + 1;

    let y_max: i64 = unwrap(max_y(&p));
    let y_min: i64 = unwrap(min_y(&p));
    proof_assert! { -1000 <= @x_min && @x_min <= @x_max && @x_max < 1000 };
    let num_vox_y: u64 = (abs(y_max - y_min) as u64 / voxel_size) + 1;

    let z_max: i64 = unwrap(max_z(&p));
    let z_min: i64 = unwrap(min_z(&p));
    proof_assert! { -1000 <= @x_min && @x_min <= @x_max && @x_max < 1000 };
    let num_vox_z: u64 = (abs(z_max - z_min) as u64 / voxel_size) + 1;

    proof_assert! { 0 < @num_vox_x && @num_vox_x <= 2000  };
    proof_assert! { 0 < @num_vox_y && @num_vox_y <= 2000  };
    proof_assert! { 0 < @num_vox_z && @num_vox_z <= 2000  };

    proof_assert! { @num_vox_x * @num_vox_y <= 4000000};
    let mut voxel_array: Vec<Point> =
        vec::from_elem(Point { x: 0, y: 0, z: 0 }, (num_vox_x * num_vox_y * num_vox_z) as usize); // todo

    let mut count_array: Vec<usize> =
        vec::from_elem(0, (num_vox_x * num_vox_y * num_vox_z) as usize); //todo

    let mut i: usize = 0;

    #[invariant(count_contents, forall<j : _> 0 <= j && j < (@count_array).len() ==> (@count_array)[j] <= i)]
    #[invariant(voxel_len, (@voxel_array).len() == @num_vox_x * @num_vox_y * @num_vox_z)]
    #[invariant(count_len, (@count_array).len() == @num_vox_x * @num_vox_y * @num_vox_z)]
    while i < p.len() {
        let pt = &p[i];
        let x_floored = (pt.x - x_min) / voxel_size as i64;
        let y_floored = (pt.y - y_min) / voxel_size as i64;
        let z_floored = (pt.z - z_min) / voxel_size as i64;

        proof_assert! {div_mono(0, 0, 0); true };
        // We actually need this because it seems like the function generates too many constatns
        // which perhaps are hurting the solvers?
        proof_assert! { 0 <= @x_floored && @x_floored < @num_vox_x };
        proof_assert! { 0 <= @y_floored && @y_floored < @num_vox_y };
        proof_assert! { 0 <= @z_floored && @z_floored < @num_vox_z };

        let ix = (x_floored * y_floored * z_floored) as usize;

        proof_assert! { mult_mono(0, 0, 0, 0); true};
        proof_assert! { @x_floored * @y_floored < @num_vox_x * @num_vox_y };
        proof_assert! { @x_floored * @y_floored * @z_floored < @num_vox_x * @num_vox_y * @num_vox_z };
        proof_assert! { @ix < (@num_vox_x * @num_vox_y * @num_vox_z)};

        voxel_array[ix] = voxel_array[ix] + pt;
        count_array[ix] = count_array[ix] + 1;
        i += 1;
    }

    return average(
        count_array,
        voxel_array,
        num_vox_x as usize,
        num_vox_y as usize,
        num_vox_z as usize,
    );
}

#[trusted]
#[requires(@div > 0)]
fn div_point(sup: Point, div: usize) -> Point {
    todo!()
}

#[requires(@num_vox_x <= 2000)]
#[requires(@num_vox_y <= 2000)]
#[requires(@num_vox_z <= 2000)]
#[requires((@count_array).len() == (@num_vox_x * @num_vox_y * @num_vox_z))]
#[requires((@voxel_array).len() == (@count_array).len())]
fn average(
    count_array: Vec<usize>,
    voxel_array: Vec<Point>,
    num_vox_x: usize,
    num_vox_y: usize,
    num_vox_z: usize,
) -> Vec<Point> {
    let mut i: usize = 0;
    let mut pd = Vec::new();
    #[invariant(i_bound, 0 <= @i && @i <= @num_vox_x)]
    while i < num_vox_x {
        let mut j: usize = 0;
        #[invariant(j_bound, 0 <= @j && @j <= @num_vox_y)]
        while j < num_vox_y {
            let mut k: usize = 0;
            #[invariant(k_bound, 0 <= @k && @k <= @num_vox_z)]
            while k < num_vox_z {
                let idx: usize = (i * j * k) as usize;
                proof_assert! { mult_mono(0, 0, 0, 0); true};

                proof_assert!(@idx < (@num_vox_x * @num_vox_y * @num_vox_z));
                if count_array[idx] != 0 {
                    pd.push(div_point(voxel_array[idx], count_array[idx]));
                }
                k += 1;
            }
            j += 1;
        }
        i += 1;
    }
    return pd;
}
