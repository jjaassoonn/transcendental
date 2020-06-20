import data.real.basic
import data.complex.exponential
import ring_theory.algebraic
import e_trans_helpers

noncomputable theory
local attribute [instance] classical.prop_decidable

open small_things
open_locale big_operators

def e : ℝ := real.exp 1

section e

private lemma nonneg_nat (i : ℕ) : (i : ℝ) ≥ 0 :=
begin
  norm_cast, exact bot_le,
end

theorem prod_deg (s : ℕ) (f : ℕ -> polynomial ℤ) (hf : ∀ i ∈ finset.range s, f i ≠ 0) : (∏ i in finset.range s, f i).nat_degree = ∑ i in finset.range s, (f i).nat_degree :=
begin
  induction s with s ih,
  simp,

  rw finset.sum_range_succ, rw finset.prod_range_succ,
  have triv : (∀ (i : ℕ), i ∈ finset.range s → f i ≠ 0),
  {
    intros i hi, apply hf, simp at hi ⊢, exact nat.lt.step hi,
  },
  replace ih := ih triv, rw <-ih, apply polynomial.nat_degree_mul_eq,
  apply hf, simp,
  intro rid, rw [finset.prod_eq_zero_iff] at rid,
  choose a ha using rid,
  refine hf a _ ha.2, simp at ha ⊢, exact nat.lt.step ha.left,
end

def f_p (p : ℕ) (hp : nat.prime p) (n : ℕ): polynomial ℤ := polynomial.X ^ (p - 1) * (∏ i in finset.range n, (polynomial.X - (polynomial.C (i+1:ℤ)))^p)

theorem deg_f_p (p : ℕ) (hp : nat.prime p) (n : ℕ) : (f_p p hp n).nat_degree = (n+1)*p - 1 :=
begin
  rw f_p,
  have eq1 := @polynomial.nat_degree_mul_eq ℤ _ (polynomial.X ^ (p - 1)) (∏ i in finset.range n, (polynomial.X - (polynomial.C (i+1:ℤ)))^p) _ _,
  
  rw eq1,
  have triv : (polynomial.X : polynomial ℤ).degree = 1,
  {
    simp,
  },
  replace triv : polynomial.X.nat_degree = 1,
  {
    have triv' : ↑polynomial.X.nat_degree = polynomial.X.degree,  
    { 
      apply eq.symm,
      apply polynomial.degree_eq_nat_degree, intro rid, rw rid at triv, simp at triv, exact option.not_mem_none 1 triv,
    },
    rw triv at triv', 
    rw polynomial.nat_degree, rw triv, exact rfl,
  }, simp,
  rw triv, simp,

  have triv' : (∏ (i : ℕ) in finset.range n, (polynomial.X - polynomial.C (i+1:ℤ)) ^ p).nat_degree 
              = ∑ i in finset.range n, ((polynomial.X - polynomial.C (i+1:ℤ)) ^ p).nat_degree,
  {
    apply prod_deg, 
    intros i hi, intro rid, 
    replace rid := @pow_eq_zero (polynomial ℤ) _ (polynomial.X - polynomial.C (i+1:ℤ)) p rid,
    rw sub_eq_zero_iff_eq at rid,
    have rid' : (polynomial.C (i+1:ℤ)).nat_degree = 1,
    rw <-rid, exact triv, have rid'' := polynomial.nat_degree_C (i+1:ℤ), rw rid' at rid'', linarith,
  }, simp at triv',
  rw triv',
  have triv'' : (∑ (x : ℕ) in finset.range n, p * (polynomial.X - (polynomial.C ↑x + 1)).nat_degree) = ∑ x in finset.range n, p,
  {
    apply congr_arg, ext, rename x i,
    have eq1 : (polynomial.X - (polynomial.C (i:ℤ) + 1)) =  (polynomial.X - (polynomial.C (i + 1:ℤ))),
    {
      simp,
    },
    rw eq1,
    have deg1 : (polynomial.X - polynomial.C (i + 1:ℤ)).degree = 1,
    {
      apply polynomial.degree_X_sub_C,
    },
    have deg2 : (polynomial.X - polynomial.C (i + 1:ℤ)).nat_degree = 1,
    {
      rw polynomial.nat_degree, rw deg1, exact rfl,
    },
    rw deg2, rw mul_one,
  },
  rw triv'', rw finset.sum_const, simp, ring, have eq2 := (@nat.add_sub_assoc p 1 _ (p*n)),
  rw eq2, rw add_comm,
  linarith [((@nat.prime_def_lt p).1 hp).1],

  {
    intro rid, replace rid := pow_eq_zero rid, exact polynomial.X_ne_zero rid,
  },

  {
    intro rid, rw finset.prod_eq_zero_iff at rid,
    choose i hi using rid,
    have hi1 := hi.1, have hi2 := hi.2, replace hi2 := pow_eq_zero hi2,
    have deg1 := polynomial.degree_X_sub_C (i+1:ℤ), rw hi2 at deg1, simp at deg1,
    have triv := @ne_bot_of_gt ℕ _ 0 1 _, exact option.not_mem_none 1 deg1, exact lt_add_one 0,
  }
end


def J (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) : ℝ := 
  ∑ i in finset.range g.nat_degree.succ, (g.coeff i : ℝ) * (II (f_p p hp g.nat_degree) i (nonneg_nat i))


theorem e_transcendental : ¬ is_algebraic ℤ e :=
begin
  by_contra e_algebraic,
  rw is_algebraic at e_algebraic,
  choose g g_def using e_algebraic,
  have g_nonzero := g_def.1,
  have e_root_g := g_def.2,
  
  sorry
end


end e