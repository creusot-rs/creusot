extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

struct Sr<T> {
    runs: Vec<usize>,
    data: Vec<T>
}

#[predicate]
fn sorted_range<T: Ord>(s: Seq<T>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i: Int, j :Int> l <= i && i < j && j < u ==> s[i] <= s[j]
    }
}

#[predicate]
fn sorted<T: Ord>(s: Seq<T>) -> bool {
    pearlite! {
        sorted_range(s, 0, s.len())
    }
}

#[predicate]
fn sorted_range_usize(s: Seq<usize>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i: Int, j :Int> l <= i && i < j && j < u ==> s[i] <= s[j]
    }
}

#[predicate]
fn sorted_usize(s: Seq<usize>) -> bool {
    pearlite! {
        sorted_range_usize(s, 0, s.len())
    }
}


#[predicate]
fn partition<T: Ord>(s: Seq<T>, i: Int) -> bool{
    pearlite! {
        forall<l: Int, r: Int> 0 <= l && l < i && i <= r
        && r < s.len() ==> s[l] <= s[r]
    }
}

#[predicate]
fn correct_run_indexes<T: Ord>(s: Seq<usize>, d: Seq<T>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < s.len() ==>
        true
    }
}


//extend_vec(&mut res.data, &r1.data, di1, r1.runs[ri1]);
// #[requires(@left_data_idx <= @left_idx)]
// #[requires(@right_data_idx <= @right_idx)]
// #[requires(@left_idx <= (@left.data).len())]
// #[requires(@right_idx <= (@right.data).len())]
// #[requires(@left_idx <= (@left.runs).len())] // correct?
// #[requires(@right_idx <= (@right.runs).len())] // correct?
// #[requires(@left_data_idx < (@left.data).len())]
// #[requires(@right_data_idx < (@right.data).len())]
#[ensures(@left_idx === (@left.runs).len() ==> result === false)]
fn do_check<T : Ord + Clone>(left: &Sr<T>, right: &Sr<T>, left_idx: usize, 
    right_idx: usize, left_data_idx: usize, right_data_idx: usize) -> bool {
    if left_idx < left.runs.len() {
        if right_idx == right.runs.len() {
            return true;
        } else {
            return left.data[left_data_idx].le(&right.data[right_data_idx]);
        }
    } else {
        false
    }
}

#[trusted]
#[requires(@h <= (@src).len())]
#[requires(@l <= @h)]
#[ensures(@^tgt === (@*tgt).concat((@src).subsequence(@l, @h)))]
#[ensures((@^tgt).len() === (@*tgt).len() + @h - @l)]
fn extend_vec<T: Clone>(tgt: &mut Vec<T>, src: &Vec<T>, mut l: usize, h: usize) {
    let old_tgt = Ghost::record(&tgt);
    let old_l = l;
    #[invariant(old_unchanged, forall<i: Int> 0 <= i && i < (@@old_tgt).len() ==>
        (@@old_tgt)[i] === (@tgt)[i])]
    #[invariant(len_gt, (@@old_tgt).len() <= (@tgt).len())]
    #[invariant(proph_const, ^@old_tgt === ^tgt)]
    #[invariant(lless, @l <= @h)]
    #[invariant(hless, @h <= (@src).len())]
    //#[invariant(els_from_src, forall<i: Int> @old_l <= i && i < @l ==>
    //    (@tgt)[(@@old_tgt).len() + i - @old_l] === (@src)[i])]
    //#[invariant(els_from_src, @*tgt === (@@old_tgt).concat((@src).subsequence(@old_l, @l)))]
    //#[invariant(els_from_src(
            //forall<i: Int> @old_l <= i && i < @l ==>))]
    #[invariant(len_ok, (@tgt).len() === (@@old_tgt).len() + @l - @old_l)]
    while l < h {
        tgt.push(src[l].clone());
        proof_assert!((@tgt)[(@tgt).len() - 1] === (@src)[@l]);
        l += 1;
    }
}

#[predicate]
fn sr_invariant<T>(s: Sr<T>) -> bool {
    pearlite! {
        sorted_usize((@s.runs)) &&

       (forall<i : _> 0<= i && i < (@s.runs).len() ==>  @(@s.runs)[i] <= (@s.data).len())
    }
}

//#[ensures((@result.data).permutation_of(@arr))]
//#[ensures(sorted(@result.data))]
#[requires((@r1.runs).len() < 1_000)]
#[requires((@r2.runs).len() < 1_000)]
#[requires(sr_invariant(r1))]
#[requires(sr_invariant(r2))]
#[ensures((@result.runs).len() < 1_000)]
#[ensures(sr_invariant(result))]
fn merge<T : Ord + Clone>(r1: Sr<T>, r2: Sr<T>) -> Sr<T> {
    let mut res: Sr<T> = Sr { runs: Vec::new(), data: Vec::new()};
    let mut di1: usize = 0;
    let mut ri1: usize = 0;
    let mut di2: usize = 0;
    let mut ri2: usize = 0;

    //#[invariant(idx1, @di1 <= 0)]
    // #[invariant(idx2, true)]
    // #[invariant(idx3, true)]
    // #[invariant(idx4, true)]
    // #[invariant(di_ri,  di1 <= (@res.runs)[@ri1])]
    #[invariant(di_data, @ri1 < (@r1.runs).len() ==> @di1 <= (@r1.data).len() && di1 <= (@r1.runs)[@ri1])]
    #[invariant(di_data,  @ri2 < (@r2.runs).len() ==>  @di2 <= (@r2.data).len() && di2 <= (@r2.runs)[@ri2])]
    #[invariant(res_inv, sr_invariant(res))]
    // #[invariant(ris, @ri1 < (@res.runs).len() && @ri2 < (@res.runs).len())]
    // #[invariant(dis, @di1 < (@res.data).len() && @di2 < (@res.data).len())]
    while ri1 < r1.runs.len() || ri2 < r2.runs.len() {
        let old_data = Ghost::record(&res.data);
        let t1 = do_check(&r1, &r2, ri1, ri2, di1, di2);
        let t2 = do_check(&r2, &r1, ri2, ri1, di2, di1);
        if t1 {
            proof_assert!{ @ri1 < (@r1.runs).len() };
            extend_vec(&mut res.data, &r1.data, di1, r1.runs[ri1]);
            di1 = r1.runs[ri1];
            proof_assert! { @di1 <= (@r1.data).len() };
            ri1 += 1;

            proof_assert! { (@@old_data).len() <= (@res.data).len() };
        }
        if t2 {
            proof_assert!{ @ri2 < (@r2.runs).len() };
            extend_vec(&mut res.data, &r2.data, di2, r2.runs[ri2]);
            di2 = r2.runs[ri2];
            ri2 += 1;
            proof_assert! { (@@old_data).len() <= (@res.data).len() };
        }
        // Add new segment boundary
        let l = res.data.len();
        res.runs.push(l);
    }

    return res;
}

// Task 3:
//#[ensures((@result.data).permutation_of(@arr))]
//#[ensures(sorted(@result.data))]
// Task 4:
// Correct run indexes
//#[ensures(correct_run_indexes(@result.runs))]
#[requires(@l <= @h)]
#[requires(@h < (@arr).len())]
#[requires((@arr).len() <= 1000)]
#[ensures(sr_invariant(result))]
#[ensures((@result.runs).len() < 1000)]
fn msort<T : Ord + Clone>(arr: &Vec<T>, l: usize, h: usize) -> Sr<T> {
   
    if l == h { 
        let res = Sr { runs: Vec::new(), data: Vec::new() };
        return res; 
    }

    if h - l == 1  {
        let mut res = Sr { runs: Vec::new(), data: Vec::new() };
        res.data.push(arr[l].clone());
        // putting in in the next line causes invalid code gen
        let l = res.data.len();
        res.runs.push(l);
        return res;
    }

    let m = l + (h - l) / 2;
    
    proof_assert! { @m < @h };
    let res1 = msort(arr, l, m);
    let res2 = msort(arr, m, h);

    return merge(res1, res2);
}