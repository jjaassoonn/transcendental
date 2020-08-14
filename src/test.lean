import measure_theory.set_integral
import measure_theory.bochner_integration
import measure_theory.interval_integral
import measure_theory.lebesgue_measure
import analysis.special_functions.exp_log
import small_things
import tactic

noncomputable theory
open_locale classical
open_locale big_operators

notation α`[X]` := polynomial α

-- F(x) = ∫ t in a .. x, f t
-- F'(x) = f(x) for x in [a,b]

private lemma ftc1 (f : ℝ -> ℝ) {hf : measurable f} {hf2 : continuous f} (a b : ℝ) (h : a ≤ b) {hf3 : measure_theory.integrable_on f (set.Icc a b)} (x0 : ℝ) (hx0 : x0 ∈ set.Icc a b) : 
  has_deriv_at (λ (b : ℝ), ∫ (x : ℝ) in a..b, f x) (f x0) x0 :=
begin
  apply interval_integral.integral_has_deriv_at_of_tendsto_ae,
  simp only [], exact hf,
  unfold interval_integrable,
  split,
  apply measure_theory.integrable_on.mono hf3,
  intros y hy,
  simp only [set.mem_Ioc, set.mem_Icc] at ⊢ hy hx0,
  split, linarith, linarith,
  apply le_refl _,

  apply measure_theory.integrable_on.mono hf3,
  intros y hy,
  simp only [set.mem_Ioc, set.mem_Icc] at ⊢ hy hx0,
  split, linarith, linarith,
  apply le_refl _,

  apply filter.tendsto_inf_left,
  exact continuous.tendsto hf2 x0,
end


/-- # Assumption-/
/-Theorem
fundamental theorem of calculus and integration by part is assumed. I am waiting for them to arrive in `mathlib` and I will update this part and prove relatvent additional assumptions.
-/

theorem ftc' (F f: ℝ -> ℝ) {hF : differentiable ℝ F} 
{F_deriv : deriv F = f} {hf : measurable f} {hf1 : continuous f}
(a b : ℝ) (h : b ≥ a) :  (∫ x in a..b, f x) = F b - F a :=
begin
  by_cases hab : (a = b),
  rw hab, simp only [interval_integral.integral_same, sub_self],

  set G := (λ x, (∫ t in a..x, f t)) with hG,
  have prop := ftc1 f a b h,
  rw <-hG at prop,
  have hG1 : differentiable_on ℝ G (set.Icc a b),
  {
    intros x hx,
    have prop := ftc1 f a b h x hx,
    refine differentiable_at.differentiable_within_at _,
    rw hG,
    exact has_deriv_at.differentiable_at prop,
    exact hf, exact hf1,

    apply continuous.integrable_on_compact _ hf1,
    exact real.locally_finite_volume, exact compact_Icc,
  },
  have H : (set.Icc a b).indicator (deriv G) = (set.Icc a b).indicator f,
  {
    apply set.indicator_congr,
    intros x0 hx0,
    replace prop := prop x0 hx0,
    exact has_deriv_at.deriv prop,
  },
  have H2 : (set.Icc a b).indicator (deriv G) = (set.Icc a b).indicator (deriv F),
  {
    exact eq.trans H (congr_arg (set.Icc a b).indicator (eq.symm F_deriv)),
  },
  
  replace H2 : ∀ y ∈ set.Icc a b, (deriv (F - G)) y = 0,
  {
    intros y hy,
    change deriv (λ t, F t - G t) y = 0,
    rw deriv_sub, rw sub_eq_zero,

    have eq1 : (set.Icc a b).indicator (deriv F) y = deriv F y,
    exact if_pos hy, rw <-eq1,
    have eq2 : (set.Icc a b).indicator (deriv G) y = deriv G y,
    exact if_pos hy, rw <-eq2, exact congr_fun H2.symm y,

    dsimp only [],
    exact hF y,

    dsimp only [],
    exact has_deriv_at.differentiable_at (prop y hy),
  },

  have key : ∀ y ∈ set.Ioc a b, (F - G) y = (F - G) a,
  {
    intros y hy,
    have ineq : a < y, simp only [set.mem_Ioc] at hy, exact hy.1,
    have key := exists_deriv_eq_slope (F - G) ineq _ _,
    rcases key with ⟨c, hc, hc2⟩,
    have hc' : c ∈ set.Icc a b, 
      simp only [set.mem_Icc, set.mem_Ioc, set.mem_Ioo] at hy ⊢ hc,
      split, linarith, linarith,
    rw H2 c hc' at hc2,
    replace hc2 := eq.symm hc2,
    rw div_eq_zero_iff at hc2,
    cases hc2, exact sub_eq_zero.mp hc2,
    simp only [set.mem_Icc, set.mem_Ioc, set.mem_Ioo] at hy ⊢ hc, linarith,

    apply continuous_on.sub,
    simp only [], apply continuous.continuous_on,
    apply differentiable.continuous hF,

    have hG1' : continuous_on G (set.Icc a b),
      apply differentiable_on.continuous_on hG1,
    simp only [], apply continuous_on.mono hG1',
    apply set.Icc_subset_Icc, exact le_refl a, exact hy.2,

    apply differentiable_on.sub,
    simp only [], exact differentiable.differentiable_on hF,
    simp only [], apply differentiable_on.mono hG1,
    intros z hz, 
    simp only [set.mem_Icc, set.mem_Ioc, set.mem_Ioo] at *,
    split, linarith, linarith,
  },

  have G_a : G a = 0,
  {
    rw hG, simp only [interval_integral.integral_same],
  },
  have G_b : G b = ∫ x in a .. b, f x,
  {
    rw hG,
  },
  rw <-G_b,
  have eq : G b = G b - 0, rw sub_zero, rw eq, rw <-G_a,
  rw sub_eq_sub_iff_sub_eq_sub,
  suffices : F b - G b = F a - G a, linarith,
  replace key := key b _,
  simp only [pi.sub_apply] at key ⊢, exact key,
  simp only [set.mem_Icc, set.mem_Ioc, set.mem_Ioo] at *,
  split, exact lt_of_le_of_ne h hab, exact le_refl b,

  exact hf, exact hf1,
  apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) hf1),
  exact set.subset.rfl,
  exact real.locally_finite_volume,
end

theorem ftc (f: ℝ -> ℝ) {hf : differentiable ℝ f} {hf2 : measurable (deriv f)} {hf3 : continuous (deriv f)} (a b : ℝ) (h : b ≥ a) :  (∫ x in a..b, (deriv f) x) = f b - f a :=
begin
  refine ftc' f (deriv f) a b h,
  simp only [], exact hf,
  refl, exact hf2, exact hf3,
end

theorem integrate_by_part (f g : ℝ -> ℝ)
  {hf : differentiable ℝ f} {hf2 : measurable (deriv f)} 
  {hf3 : measurable f} {hf4 : continuous (deriv f)}
  {hg : differentiable ℝ g} {hg2 : measurable (deriv g)} 
  {hg3 : measurable g} {hg4 : continuous (deriv g)}
  (a b : ℝ) (h : b ≥ a) :
  (∫ x in a..b, (f x)*(deriv g x)) = (f b) * (g b) - (f a) * (g a) - (∫ x in a..b, (deriv f x) * (g x)) :=

begin
  have eq1 := ftc (f * g) a b h,
  have eq2 :  (∫ (x : ℝ) in a..b, deriv (f * g) x) =  (∫ (x : ℝ) in a..b, (deriv f x) * g x + f x * (deriv g x)),
  {
    rw interval_integral.integral_of_le h,
    rw interval_integral.integral_of_le h,
    apply congr_arg, ext y,
    apply deriv_mul,
    simp only [],
    exact hf y,
    simp only [],
    exact hg y,
  },
  rw eq2 at eq1,
  rw interval_integral.integral_add at eq1,
  simp only [pi.mul_apply] at eq1 ⊢,
  rw <-eq1, simp only [add_sub_cancel'],
  apply measurable.mul,
  simp only [], exact hf2,
  simp only [], exact hg3,
  rw interval_integrable,
  have H1 : continuous (λ x, (deriv f x) * g x),
  {
    apply continuous.mul _ _, exact normed_ring_top_monoid,
    exact hf4, apply @differentiable.continuous ℝ _ ℝ _ _ ℝ _ _ _,
    exact hg,
  },
  
  split,
  apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) H1),
  exact set.Ioc_subset_Icc_self,
  exact real.locally_finite_volume,
  apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) H1),
  rw set.Ioc_eq_empty, exact (set.Icc a b).empty_subset, exact h,
  exact real.locally_finite_volume,
  
  apply measurable.mul, exact hf3, exact hg2,
  rw interval_integrable,
  have H2 : continuous (λ x, f x * deriv g x),
  {
    apply continuous.mul _ _, exact normed_ring_top_monoid,
    apply @differentiable.continuous ℝ _ ℝ _ _ ℝ _ _ _,
    exact hf, exact hg4,
  },
  split,
  

  apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) H2),
  exact set.Ioc_subset_Icc_self,
  exact real.locally_finite_volume,
  apply measure_theory.integrable_on.mono_set (continuous.integrable_on_compact (@compact_Icc a b) H2),
  rw set.Ioc_eq_empty, exact (set.Icc a b).empty_subset, exact h,
  exact real.locally_finite_volume,

  apply differentiable.mul hf hg,
  apply continuous.measurable,
  {
    have eq1 : deriv (f * g) = (deriv f) * g + f * (deriv g),
      ext, simp only [pi.add_apply, pi.mul_apply],
      change (deriv (λ x, (f x * g x))) x = deriv f x * g x + f x * deriv g x,
    rw deriv_mul,
    simp only [], exact hf x,
    simp only [], exact hg x,
    rw eq1, apply continuous.add _ _,
    exact normed_top_monoid, apply continuous.mul _ _,
    exact normed_ring_top_monoid, exact hf4,
    apply differentiable.continuous hg,
    apply continuous.mul _ _, exact normed_ring_top_monoid,
    apply differentiable.continuous hf, exact hg4,
  },
  {
    have eq1 : deriv (f * g) = (deriv f) * g + f * (deriv g),
      ext, simp only [pi.add_apply, pi.mul_apply],
      change (deriv (λ x, (f x * g x))) x = deriv f x * g x + f x * deriv g x,
    rw deriv_mul,
    simp only [], exact hf x,
    simp only [], exact hg x,
    rw eq1, apply continuous.add _ _,
    exact normed_top_monoid, apply continuous.mul _ _,
    exact normed_ring_top_monoid, exact hf4,
    apply differentiable.continuous hg,
    apply continuous.mul _ _, exact normed_ring_top_monoid,
    apply differentiable.continuous hf, exact hg4,
  },
end
