import data.int.basic
import data.polynomial


theorem non_empty_supp (f : polynomial ℤ) (hf : f ≠ 0) : f.support.nonempty :=
begin
  contrapose hf, rw finset.nonempty at hf, rw not_exists at hf, simp, ext, simp,
  have triv := (f.3 n).2 , contrapose triv, rw not_imp, split, exact triv, exact hf n,
end


def min_degree_term (f : polynomial ℤ) (hf : f ≠ 0) : ℕ := finset.min' (f.support) (non_empty_supp f hf)
def make_const_term_nonzero (f : polynomial ℤ) (hf : f ≠ 0) : polynomial ℤ := 
begin
  constructor, swap 2,
  {
    exact finset.image (λ i : ℕ, i-(min_degree_term f hf)) f.support,
  },
  swap 2, {
    intro n, exact (f.coeff (n+(min_degree_term f hf))),
  },
  {
    intro n, split, intro hn, rw finset.mem_image at hn, choose a ha using hn, rw <-ha.2, rw nat.sub_add_cancel,
    have eq2 := (f.3 a).1 ha.1, exact eq2,
    rw min_degree_term, exact finset.min'_le f.support (non_empty_supp f hf) a ha.1,

    intro hn, rw finset.mem_image, use n + min_degree_term f hf,
    split,
    exact (f.3 (n + min_degree_term f hf)).2 hn, simp,
  },
end

theorem supp_after_change (f : polynomial ℤ) (hf : f ≠ 0) : (make_const_term_nonzero f hf).support = finset.image (λ i : ℕ, i-(min_degree_term f hf)) f.support :=
begin
  simp [make_const_term_nonzero],
end

theorem nat_degree_decrease : Π (f:polynomial ℤ) (hf : f ≠ 0), (make_const_term_nonzero f hf).nat_degree ≤ f.nat_degree :=
begin
  sorry
end
