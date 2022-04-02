extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

#[derive(Clone, Copy)]
struct Point { x: i64, y: i64, z: i64 }

#[ensures(match result {
  Some(v) => (forall<i : _> 0 <= i && i < (@p).len() ==> (@p)[i].x <= v)
  && exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].x === @v,
  None => (@p).len() === 0
})]
fn max_x(p: &Vec<Point>) -> Option<i64> {
  if p.len() == 0 { return None; }
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
  && exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].y === @v,
  None => (@p).len() === 0
})]
fn max_y(p: &Vec<Point>) -> Option<i64> {
  if p.len() == 0 { return None; }
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
  && exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].z === @v,
  None => (@p).len() === 0
})]
fn max_z(p: &Vec<Point>) -> Option<i64> {
  if p.len() == 0 { return None; }
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

//#[trusted] // OK
#[ensures(match result {
  Some(v) => (forall<i : _> 0 <= i && i < (@p).len() ==> ((@p)[i].z) >= v)
  && exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].z === @v,
  None => (@p).len() === 0
})]
fn min_z(p: &Vec<Point>) -> Option<i64> {
  if p.len() == 0 { return None; }
  let mut min_seen: i64 = p[0].z;
  let mut min_idx: usize = 0;
  let mut i: usize = 1;
  #[invariant(i_less, 1 <= @i && @i <= (@p).len())]
  #[invariant(min_idx_less, 0 <= @min_idx && @min_idx < (@p).len())]
  #[invariant(min_is_min, forall<j: Int> 0 <= j && j < @i ==>
    (@p)[j].z >= min_seen
  )]
  #[invariant(name, (@p)[@min_idx].z == min_seen)]
  while i < p.len() {
    if p[i].z < min_seen {
      min_seen = p[i].z;
      min_idx = i;
    }
    i += 1;
  }
  return Some(min_seen);
}

/*
#[ensures(match result {
  Some(v) => (forall<i : _> 0 <= i && i < (@p).len() ==> ((@p)[i].z) >= v)
  && exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].z === @v,
  None => (@p).len() === 0
})]
fn min_y(p: &Vec<Point>) -> Option<i64> {
  if p.len() == 0 { return None; }
  let mut min_seen: i64 = p[0].z;
  let mut min_idx: usize = 0;
  let mut i: usize = 1;
  #[invariant(i_less, 1 <= @i && @i <= (@p).len())]
  #[invariant(min_idx_less, 0 <= @min_idx && @min_idx < (@p).len())]
  #[invariant(min_is_min, forall<j: Int> 0 <= j && j < @i ==>
    (@p)[j].z >= min_seen
  )]
  while i < p.len() {
    if p[i].z < min_seen {
      min_seen = p[i].z;
      min_idx = i;
    }
    i += 1;
  }
  return Some(min_seen);
}
*/

#[trusted] // OK
#[ensures(match result {
  Some(v) => (forall<i : _> 0 <= i && i < (@p).len() ==> ((@p)[i].y) >= v)
  && exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].y === @v,
  None => (@p).len() === 0
})]
fn min_y(p: &Vec<Point>) -> Option<i64> {
  if p.len() == 0 { return None; }
  let mut min_seen = p[0].y;
  let mut i: usize = 1;
  #[invariant(i_less, 1 <= @i && @i <= (@p).len())]
  #[invariant(min_is_min, forall<j: Int> 0 <= j && j < @i ==>
    (@p)[j].y >= min_seen
  )]
  while i < p.len() {
    if p[i].y < min_seen {
      min_seen = p[i].y;
    }
    i += 1;
  }
  return Some(min_seen);
}

#[trusted] // OK
#[ensures(match result {
  Some(v) => (forall<i : _> 0 <= i && i < (@p).len() ==> ((@p)[i].x) >= v)
  && exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].x === @v,
  None => (@p).len() === 0
})]
fn min_x(p: &Vec<Point>) -> Option<i64> {
  if p.len() == 0 { return None; }
  let mut min_seen = p[0].x;
  let mut i: usize = 1;
  #[invariant(i_less, 1 <= @i && @i <= (@p).len())]
  #[invariant(min_is_min, forall<j: Int> 0 <= j && j < @i ==>
    (@p)[j].x >= min_seen
  )]
  while i < p.len() {
    if p[i].x < min_seen {
      min_seen = p[i].x;
    }
    i += 1;
  }
  return Some(min_seen);
}


#[ensures(@result >= 0)]
#[ensures(@result === if @i < 0 { -@i } else { @i })]
fn abs(i: i64) -> i64 { if i < 0 { -i } else { i } }

#[trusted]
#[requires(!(@d === 0))]
#[ensures(@result === @sup / @d )]
fn int_div(sup : i64, d: i64) -> i64 { todo!() }

impl<'a> std::ops::Add<&'a Point> for Point {
  type Output = Point;

  #[trusted]
  fn add(self, rhs: &'a Point) -> Self {
    Point { x: self.x + rhs.x, y: self.y + rhs.y, z : self.z + rhs.z }
  }
}

#[requires(@x >= 0)]
#[requires(@y >= 0)]
#[requires(@z >= 0)]
#[ensures(@result === @x * @y * @z)]
fn offset(x: i64, y: i64, z: i64) -> usize { (x * y * z) as usize }

#[requires(!(o === None))]
#[ensures(Some(result) === o)]
fn unwrap<T>(o : Option<T>) -> T {
  match o {
    Some(t) => t,
    None => std::process::abort()
  }
}
 
#[requires(forall<i: Int> 0 <= i && i < (@p).len() 
    ==> @(@p)[i].x < 1000 && @(@p)[i].x >= -1000
)]
#[requires(forall<i: Int> 0 <= i && i < (@p).len() 
    ==> @(@p)[i].y < 1000 && @(@p)[i].y >= -1000
)]
#[requires(forall<i: Int> 0 <= i && i < (@p).len() 
    ==> @(@p)[i].z < 1000 && @(@p)[i].z >= -1000
)]
#[requires(@voxel_size > 0)]
fn downsample(p: Vec<Point>, voxel_size: i64) -> Vec<Point> {
  if p.len() == 0 {
    return Vec::new()
  }
  
  let x_max: i64 = unwrap(max_x(&p));
  let x_min: i64 = unwrap(min_x(&p));

  proof_assert! { exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].x === @x_max};
  proof_assert! { exists<i : Int> 0 <= i && i < (@p).len() && @(@p)[i].x === @x_min};

  proof_assert! { -1000 <= @x_min && @x_min <= @x_max && @x_max < 1000 };
  let num_vox_x: i64 = int_div(abs(x_max - x_min), voxel_size) + 1; 

  let y_max: i64 = unwrap(max_y(&p));
  let y_min: i64 = unwrap(min_y(&p));
  proof_assert! { -1000 <= @x_min && @x_min <= @x_max && @x_max < 1000 };
  let num_vox_y: i64 = int_div(abs(y_max - y_min), voxel_size) + 1;

  let z_max: i64 = unwrap(max_z(&p));
  let z_min: i64 = unwrap(min_z(&p));
  proof_assert! { -1000 <= @x_min && @x_min <= @x_max && @x_max < 1000 };
  let num_vox_z: i64 = int_div(abs(z_max - z_min), voxel_size) + 1;

  proof_assert! { @num_vox_x > 0 };
  proof_assert! { @num_vox_y > 0 };
  proof_assert! { @num_vox_z > 0 };

  // let voxel_array = Point {}
  let mut voxel_array: Vec<Point> = vec::from_elem(Point { x: 0, y: 0, z: 0}, (num_vox_x * num_vox_y * num_vox_z) as usize); // todo

  let mut count_array: Vec<usize> = vec::from_elem(0, (num_vox_x * num_vox_y * num_vox_z) as usize); //todo
  

  let mut i: usize = 0;
  
  // #[invariant(i_bound, 0 <= @i && @i < (@p).len())]
  // #[invariant(voxel_OK, 0 <= @i && @i < (@voxel_array).len())]
  // #[invariant(count_OK, 0 <= @i && @i < (@count_array).len())]
  #[invariant(voxel_len, (@voxel_array).len() === @num_vox_x * @num_vox_y * @num_vox_z)]
  #[invariant(count_len, (@count_array).len() === @num_vox_x * @num_vox_y * @num_vox_z)]
  while i < p.len() {
    let pt = &p[i];
    let x_floored = int_div(pt.x - x_min, voxel_size);
    let y_floored = int_div(pt.y - y_min, voxel_size);
    let z_floored = int_div(pt.z - z_min, voxel_size);

    proof_assert! { pt.x - x_min < x_max - x_min};
    proof_assert! { x_floored < num_vox_x };
    proof_assert! { y_floored < num_vox_y };
    proof_assert! { z_floored < num_vox_z };
    proof_assert! { @x_floored >= 0 };
    proof_assert! { @y_floored >= 0 };
    proof_assert! { @z_floored >= 0 };

    let ix = offset(x_floored, y_floored, z_floored);

    proof_assert! { @ix < (@num_vox_x * @num_vox_y * @num_vox_z)};

    voxel_array[ix] = voxel_array[ix] + pt;
    count_array[ix] = count_array[ix] + 1;
  }

  return average(count_array, voxel_array, num_vox_x as usize, num_vox_y as usize, num_vox_z as usize);
}


#[trusted]
#[requires(@div > 0)]
fn div_point(sup : Point, div: usize) -> Point { todo!() }

#[trusted]
#[requires(@x >= 0)]
#[requires(@y >= 0)]
#[requires(@z >= 0)]
#[ensures(@result === @x * @y * @z)]
fn offset2(x: usize, y: usize, z: usize) -> usize { (x * y * z) as usize }

#[trusted]
#[requires(@num_vox_x <= 1000)]
#[requires(@num_vox_y <= 1000)]
#[requires(@num_vox_z <= 1000)]
#[requires((@count_array).len() === (@num_vox_x * @num_vox_y * @num_vox_z))]
#[requires((@voxel_array).len() === (@count_array).len())]
fn average(count_array: Vec<usize>, voxel_array: Vec<Point>, num_vox_x: usize, num_vox_y: usize, num_vox_z: usize) -> Vec<Point> {
  let mut i : usize = 0;
  let mut pd = Vec::new();
  #[invariant(i_bound, 0 <= @i && @i <= @num_vox_x)]
  while i < num_vox_x {
    let mut j : usize = 0;
    #[invariant(i_bound, 0 <= @i && @i <= @num_vox_x)]
    #[invariant(j_bound, 0 <= @j && @j <= @num_vox_y)]
    while j < num_vox_y  {
       let mut k : usize = 0;
      #[invariant(i_bound, 0 <= @i && @i <= @num_vox_x)]
      #[invariant(j_bound, 0 <= @j && @j <= @num_vox_y)]
      #[invariant(k_bound, 0 <= @k && @k <= @num_vox_z)]
      while k < num_vox_z {
        let idx: usize = offset2(i, j, k);
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