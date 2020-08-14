-- import measure_theory.set_integral
-- import measure_theory.bochner_integration
-- import measure_theory.interval_integral
-- import measure_theory.lebesgue_measure
-- import analysis.special_functions.exp_log
-- import small_things

-- noncomputable theory
-- open_locale classical
-- open_locale big_operators

-- notation α`[X]` := polynomial α

-- -- F(x) = ∫ t in a .. x, f t
-- -- F'(x) = f(x) for x in [a,b]

-- private lemma ftc1 (f : ℝ -> ℝ) {hf : measurable f} {hf2 : continuous f} (a b : ℝ) (h : a ≤ b) {hf3 : measure_theory.integrable_on f (set.Icc a b)} (x0 : ℝ) (hx0 : x0 ∈ set.Icc a b) : 
--   has_deriv_at (λ (b : ℝ), ∫ (x : ℝ) in a..b, f x) (f x0) x0 :=
-- begin
--   apply interval_integral.integral_has_deriv_at_of_tendsto_ae,
--   simp only [], exact hf,
--   unfold interval_integrable,
--   split,
--   apply measure_theory.integrable_on.mono hf3,
--   intros y hy,
--   simp only [set.mem_Ioc, set.mem_Icc] at ⊢ hy hx0,
--   split, linarith, linarith,
--   apply le_refl _,

--   apply measure_theory.integrable_on.mono hf3,
--   intros y hy,
--   simp only [set.mem_Ioc, set.mem_Icc] at ⊢ hy hx0,
--   split, linarith, linarith,
--   apply le_refl _,

--   apply filter.tendsto_inf_left,
--   exact continuous.tendsto hf2 x0,
-- end


-- /-- # Assumption-/
-- /-Theorem
-- fundamental theorem of calculus and integration by part is assumed. I am waiting for them to arrive in `mathlib` and I will update this part and prove relatvent additional assumptions.
-- -/

-- axiom ftc (f: ℝ -> ℝ) (a b : ℝ) (h : b ≥ a) :  (∫ x in a..b, (deriv f) x) = f b - f a

-- theorem integrate_by_part (f g : ℝ -> ℝ)
--   {hf : differentiable ℝ f} {hf2 : measurable (deriv f)} 
--   {hf3 : measurable f} {hf4 : continuous (deriv f)}
--   {hg : differentiable ℝ g} {hg2 : measurable (deriv g)} 
--   {hg3 : measurable g} {hg4 : continuous (deriv g)}
--   (a b : ℝ) (h : b ≥ a) :
--   (∫ x in a..b, (f x)*(deriv g x)) = (f b) * (g b) - (f a) * (g a) - (∫ x in a..b, (deriv f x) * (g x)) :=

-- begin
--   have eq1 := ftc (f * g) a b h,
--   have eq2 :  (∫ (x : ℝ) in a..b, deriv (f * g) x) =  (∫ (x : ℝ) in a..b, (deriv f x) * g x + f x * (deriv g x)),
--   {
--     rw interval_integral.integral_of_le h,
--     rw interval_integral.integral_of_le h,
--     apply congr_arg, ext y,
--     apply deriv_mul,
--     simp only [],
--     exact hf y,
--     simp only [],
--     exact hg y,
--   },
--   rw eq2 at eq1,
--   rw interval_integral.integral_add at eq1,
--   simp only [pi.mul_apply] at eq1 ⊢,
--   rw <-eq1, simp only [add_sub_cancel'],
--   apply measurable.mul,
--   simp only [], exact hf2,
--   simp only [], exact hg3,
--   rw interval_integrable,
--   have H1 : continuous (λ x, (deriv f x) * g x),
--   {
--     apply continuous.mul _ _, exact normed_ring_top_monoid,
--     exact hf4, apply @differentiable.continuous ℝ _ ℝ _ _ ℝ _ _ _,
--     exact hg,
--   },
  
--   split,
--   apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) H1),
--   exact set.Ioc_subset_Icc_self,
--   exact real.locally_finite_volume,
--   apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) H1),
--   rw set.Ioc_eq_empty, exact (set.Icc a b).empty_subset, exact h,
--   exact real.locally_finite_volume,
  
--   apply measurable.mul, exact hf3, exact hg2,
--   rw interval_integrable,
--   have H2 : continuous (λ x, f x * deriv g x),
--   {
--     apply continuous.mul _ _, exact normed_ring_top_monoid,
--     apply @differentiable.continuous ℝ _ ℝ _ _ ℝ _ _ _,
--     exact hf, exact hg4,
--   },
--   split,
  

--   apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) H2),
--   exact set.Ioc_subset_Icc_self,
--   exact real.locally_finite_volume,
--   apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) H2),
--   rw set.Ioc_eq_empty, exact (set.Icc a b).empty_subset, exact h,
--   exact real.locally_finite_volume,
-- end
