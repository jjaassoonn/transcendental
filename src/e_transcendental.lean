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

def f_p (p : ℕ) (hp : prime p) (n : ℕ): polynomial ℤ := polynomial.X ^ (p - 1) * (∏ i in finset.range n, (polynomial.X - (polynomial.C (i+1)))^p)

theorem deg_f_p (p : ℕ) (hp : prime p) (n : ℕ) : (f_p p hp n).nat_degree = (n+1)*p - 1 :=
begin
  rw f_p,
  have eq1 := @polynomial.nat_degree_mul_eq ℤ _ (polynomial.X ^ (p - 1)) (∏ i in finset.range n, (polynomial.X - (polynomial.C (i+1)))^p) _ _,
  
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
    apply prod_deg, intros i hi, intro rid, replace rid := @pow_eq_zero (polynomial ℤ) _ (polynomial.X - polynomial.C ↑i) p rid,
    rw sub_eq_zero_iff_eq at rid,
    have rid' : (polynomial.C (i:ℤ)).nat_degree = 1, rw <-rid, exact triv, simp at rid', exact rid',
  },
  rw triv',
  have triv'' : (∑ (i : ℕ) in finset.range n.succ, ((polynomial.X - polynomial.C (i:ℤ)) ^ p).nat_degree) = ∑ i in finset.range n.succ, p,
  {
    apply congr_arg, ext, rename x i,
    rw polynomial.nat_degree_pow_eq,
    

    have tirv_d : (polynomial.X - polynomial.C (i:ℤ)).degree = 1,
    {
      cases i, norm_cast, simp,
      apply polynomial.degree_X_sub_C,
    },
    replace tirv_d : (polynomial.X - polynomial.C (i:int)).nat_degree = 1,
    {
      rw polynomial.nat_degree, rw tirv_d, exact rfl,
    },
    rw tirv_d, simp,
  },
  rw triv'',
  rw finset.sum_const, simp, rw nat.succ_eq_add_one, 
end


def J (g : polynomial ℤ) (p : ℕ) (hp : prime p) : ℝ := 
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