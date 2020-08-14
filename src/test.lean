import measure_theory.set_integral
import measure_theory.bochner_integration
import measure_theory.interval_integral
import measure_theory.lebesgue_measure
import analysis.special_functions.exp_log
import small_things

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

axiom ftc (f: ℝ -> ℝ) (a b : ℝ) (h : b ≥ a) :  (∫ x in set.Icc a b, (deriv f) x) = f b - f a

axiom integrate_by_part (f g : ℝ -> ℝ) (a b : ℝ) (h : b ≥ a) :
    (∫ x in a..b, (f x)*(deriv g x)) = (f b) * (g b) - (f a) * (g a) - (∫ x in a..b, (deriv f x) * (g x))
