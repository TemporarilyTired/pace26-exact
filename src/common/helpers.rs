#[inline(always)]
pub fn sort_tup<T: PartialOrd>(ab: (T, T)) -> (T, T) {
    if ab.0 < ab.1 { ab } else { (ab.1, ab.0) }
}
