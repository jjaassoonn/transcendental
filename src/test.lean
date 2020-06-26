import data.int.basic
import data.polynomial


open_locale big_operators

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


theorem coeff_sum (f : ℕ -> polynomial ℤ) (s : finset ℕ) (n : ℕ) : (∑ i in s, f i).coeff n = (∑ i in s, (f i).coeff n) :=
begin
    apply finset.induction_on s, simp,
    intros a s ha H, rw finset.sum_insert, rw finset.sum_insert, rw polynomial.coeff_add, rw H, assumption, assumption,
end

theorem as_sum' (f : polynomial ℤ) : f = ∑ i in f.support, (polynomial.C (f.coeff i)) * (polynomial.X^i) :=
begin
    
    ext, rw coeff_sum,
    have triv : ∑ (i : ℕ) in f.support, (polynomial.C (f.coeff i) * polynomial.X ^ i).coeff n =
        ∑ (i : ℕ) in f.support, (f.coeff i) * ((polynomial.X ^ i).coeff n),
    {
        apply congr_arg, ext, simp,
    },
    rw triv,
    replace triv : ∑ (i : ℕ) in f.support, f.coeff i * (polynomial.X ^ i).coeff n =
        ∑ (i : ℕ) in f.support, (ite (n = i) (f.coeff i) 0),
    {
        apply congr_arg, simp,
    },
    rw triv, rw finset.sum_ite, simp, rw finset.filter_eq,
    split_ifs, simp, simp, have f3 := (f.3 n).2, rw <-not_imp_not at f3, rw not_not at f3, replace h := f3 h, exact h,
end


theorem transform_eq (f : polynomial ℤ) (hf : f ≠ 0) : f = (make_const_term_nonzero f hf) * (polynomial.X) ^ (min_degree_term f hf) :=
begin
    
    have H := @finset.sum_bij _ _ _ _ f.1 (make_const_term_nonzero f hf).1
        (λ i, (polynomial.C (f.coeff i)) * polynomial.X ^ i)
        (λ i, (polynomial.C ((make_const_term_nonzero f hf).coeff i)) * (polynomial.X) ^ (i+ (min_degree_term f hf))),
    let i : Π (a : ℕ), a ∈ f.support → ℕ,
  {
    intros a ha, exact a - (min_degree_term f hf),
  },
  have i_eq : i = λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf, exact rfl,
  replace H := H i,
  have hi : ∀ (a : ℕ) (ha : a ∈ f.support), i a ha ∈ (make_const_term_nonzero f hf).support,
  {
    intros a ha, rw i_eq, 
    have triv : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a ha = a - min_degree_term f hf,
    {
      exact rfl,
    },
    rw triv, rw supp_after_change, rw finset.mem_image, use a, split, exact ha, refl,
  },
  replace H := H hi,
  have assump1 : (∀ (a : ℕ) (ha : a ∈ f.support),
     (λ (i : ℕ), (polynomial.C (f.coeff i)) * (polynomial.X) ^ i) a =
       (λ (i : ℕ), (polynomial.C ((make_const_term_nonzero f hf).coeff i)) * (polynomial.X) ^ (i + min_degree_term f hf)) (i a ha)),
  {
    intros a ha, 
    have triv1 : (λ (i : ℕ), (polynomial.C (f.coeff i)) * (polynomial.X) ^ i) a = (polynomial.C (f.coeff a)) * (polynomial.X) ^ a,
    {
      exact rfl,
    }, rw triv1,
    have triv2 : (λ (i : ℕ), (polynomial.C ((make_const_term_nonzero f hf).coeff i)) * (polynomial.X) ^ (i + min_degree_term f hf)) (i a ha) 
        = (polynomial.C ((make_const_term_nonzero f hf).coeff (i a ha))) * (polynomial.X) ^ (i a ha + min_degree_term f hf),
    {
      exact rfl,
    },
    rw triv2, rw i_eq,
    have triv3 : ((λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a ha) = a - min_degree_term f hf,
    {
      exact rfl,
    }, rw triv3, rw coeff_after_change, rw nat.sub_add_cancel, rw min_degree_term, exact f.support.min'_le (non_empty_supp f hf) a ha,
  },
  replace H := H assump1,
  have assump2 : (∀ (a₁ a₂ : ℕ) (ha₁ : a₁ ∈ f.support) (ha₂ : a₂ ∈ f.support),
     i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂),
  {
    intros a1 a2 ha1 ha2 H, rw i_eq at H, 
    have triv1 : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a1 ha1 = a1 - min_degree_term f hf, exact rfl, rw triv1 at H,
    have triv2 : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a2 ha2 = a2 - min_degree_term f hf, exact rfl, rw triv2 at H,
    have triv3 := (@add_left_inj ℕ _ (min_degree_term f hf) (a1 - min_degree_term f hf) (a2 - min_degree_term f hf)).2 H,
    rw nat.sub_add_cancel at triv3, rw nat.sub_add_cancel at triv3, exact triv3, rw min_degree_term, exact f.support.min'_le (non_empty_supp f hf) a2 ha2, exact f.support.min'_le (non_empty_supp f hf) a1 ha1,
  },
  replace H := H assump2,
  have assump3 : ∀ (b : ℕ),
     b ∈ (make_const_term_nonzero f hf).support → (∃ (a : ℕ) (ha : a ∈ f.support), b = i a ha),
  {
    intros b hb, rw supp_after_change at hb, rw finset.mem_image at hb, rw i_eq, choose a Ha using hb, use a, use Ha.1,
    have triv1 : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a _ = a - min_degree_term f hf, exact rfl, exact Ha.1, rw triv1, exact eq.symm Ha.2,
  },
  replace H := H assump3,
  have eq1 := as_sum' f,
  have eq2 := as_sum' (make_const_term_nonzero f hf), rw eq2,
  simp at H ⊢, rw finset.sum_mul,

  
  have eq3 : ∑ (x : ℕ) in
      (make_const_term_nonzero f hf).support,
      polynomial.C ((make_const_term_nonzero f hf).coeff x) * polynomial.X ^ (x + min_degree_term f hf) =
    ∑ (x : ℕ) in
      (make_const_term_nonzero f hf).support,
      polynomial.C ((make_const_term_nonzero f hf).coeff x) * polynomial.X ^ x * polynomial.X ^ min_degree_term f hf,
  {
      apply finset.sum_congr, exact rfl, intros, rw pow_add, ring,
  },
  rw <-eq3, rw <-H, exact eq1,
end

theorem nat_degree_decrease (f:polynomial ℤ) (hf : f ≠ 0) : (make_const_term_nonzero f hf).nat_degree ≤ f.nat_degree :=
begin
  have transform_eq := transform_eq f hf,
  have eq1 := @polynomial.nat_degree_mul_eq ℤ _ (make_const_term_nonzero f hf) (polynomial.X ^ min_degree_term f hf) _ _,
  have triv : (make_const_term_nonzero f hf * polynomial.X ^ min_degree_term f hf).nat_degree = f.nat_degree,
  {
      apply congr_arg, exact eq.symm transform_eq,
  }, rw triv at eq1, exact nat.le.intro (eq.symm eq1),
end
