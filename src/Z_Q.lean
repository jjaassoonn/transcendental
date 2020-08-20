import data.real.basic
import ring_theory.algebraic

open_locale classical
open_locale big_operators

theorem aeval_sum' (s : finset ℕ) (f : ℕ -> (polynomial ℤ)) (t : ℝ) : @polynomial.aeval ℤ ℝ _ _ _ t (∑ i in s, f i) = ∑ i in s, @polynomial.aeval ℤ ℝ _ _ _ t (f i) :=
begin
  apply finset.induction_on s, simp only [finset.sum_empty, alg_hom.map_zero],
  intros a s ha ih, rw finset.sum_insert, simp only [alg_hom.map_add], rw ih,
  rw finset.sum_insert, exact ha, exact ha,
end

theorem eval₂_sum' (s : finset ℕ) (g : ℤ →+* ℝ) (f : ℕ -> (polynomial ℤ)) (t : ℝ) : 
  polynomial.eval₂ g t (∑ i in s, f i) = ∑ i in s, polynomial.eval₂ g t (f i) :=
begin
  apply finset.induction_on s, simp only [finset.sum_empty, alg_hom.map_zero],
  exact is_ring_hom.map_zero (polynomial.eval₂ g t),
  intros a s ha ih, rw finset.sum_insert, simp only [polynomial.eval₂_add], rw ih,
  rw finset.sum_insert, exact ha, exact ha,
end

theorem algebraic_over_Z_iff_algebraic_over_Q (x : ℝ) : is_algebraic ℤ x -> is_algebraic ℚ x :=
begin
  rintro ⟨p, p_nonzero, root⟩,
  use (p.map (algebra_map ℤ ℚ)),
  split,
  intro rid,
  apply p_nonzero,
  apply polynomial.map_injective (algebra_map ℤ ℚ) _,
  simp only [polynomial.map_zero], exact rid,

  intros x y h, simp only [ring_hom.eq_int_cast, int.cast_inj] at h ⊢, exact h,

  rw polynomial.aeval_def,
  rw polynomial.eval₂_map,
  rw polynomial.as_sum p at root ⊢,
  rw aeval_sum' at root,
  rw eval₂_sum',
  rw <-root,
  apply finset.sum_congr, refl, intros m h,
  simp only [polynomial.aeval_X, alg_hom.map_pow, polynomial.eval₂_mul, polynomial.eval₂_X_pow, alg_hom.map_mul],
  apply congr_arg2,
  rw polynomial.eval₂_C,
  rw polynomial.aeval_C,
  apply congr_fun, ext y,
  simp only [ring_hom.eq_int_cast],
  refl,
end