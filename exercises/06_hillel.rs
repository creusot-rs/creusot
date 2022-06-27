// Implement and prove the following:

// Leftpad. Takes a padding character, a string, and a total length, returns
// the string padded to that length with that character. If length is less
// than the length of the string, does nothing.

fn left_pad<T : Copy>(str: &mut [T], len: usize, pad: T) {
	todo!()
}

// Unique. Takes a sequence of integers, returns the unique elements of that
// list. There is no requirement on the ordering of the returned values.
// Hint: Use a helper function to insert new elements into your unique vector
fn unique<T : Eq + Model>(str: &[T]) -> Vec<T> {
	todo!()
}

// Fulcrum. Given a sequence of integers, returns the index i that minimizes
// |sum(seq[..i]) - sum(seq[i..])|. Does this in O(n) time and O(n) memory.
// Hard
fn fulcrum(s : &[u32]) -> usize {
	todo!()
}