import measure_theory.interval_integral
import measure_theory.lebesgue_measure 

example (f : ℝ -> ℝ) {h1 : measurable f ∧ measure_theory.integrable f} (a b : ℝ) (h : b ≥ a) (c : ℝ) 
  (f_nonneg : ∀ x ∈ set.Icc a b, f x ≥ 0) : 0 ≤ ∫ x in a .. b, f x :=
begin
  rw interval_integral.integral_of_le h,
  apply measure_theory.integral_nonneg_of_ae,
  apply (@measure_theory.ae_restrict_iff ℝ _ _ (set.Ioc a b) _ _).2,
  apply measure_theory.ae_of_all,
  intros x hx,
  simp only [and_imp, set.mem_Ioc, pi.zero_apply, ge_iff_le, set.mem_Icc] at *,
  refine f_nonneg x _ _,
  linarith, linarith,
  simp only [pi.zero_apply],
  refine is_measurable_le measurable_zero h1.1,
end