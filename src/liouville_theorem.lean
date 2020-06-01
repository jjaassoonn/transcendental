import data.rat.basic
import data.real.basic
import data.finsupp algebra.big_operators
import algebra.ring
import ring_theory.algebraic
import field_theory.minimal_polynomial
import tactic.linarith
import tactic
import topology.metric_space.basic
import topology.basic
import topology.algebra.polynomial
import analysis.normed_space.basic analysis.specific_limits analysis.calculus.mean_value
import small_things

noncomputable theory
local attribute [instance] classical.prop_decidable

open small_things

def transcendental (x : real) := ¬(is_algebraic rat x)

def liouville_number (x : real) := ∀ n : nat, ∃ a b : int, b ≥ 1 ∧ 0 < abs(x - a / b) ∧ abs(x - a / b) < 1/b^n


def irrational (x : real) := ∀ a b : int, b > 0 -> x - a / b ≠ 0

#check metric.compact_iff_closed_bounded

-- [a-1, a+1] is compact, hence a continuous function attains a maximum and a minimum.
lemma closed_interval_compact (a : real) : compact $ set.Icc (a-1) (a+1) :=
begin
  rw metric.compact_iff_closed_bounded, split,
  {
    -- closed
    exact is_closed_Icc,
  },
  {
    unfold metric.bounded,
    use 2, intros x₁ x₂ h1 h2, simp at h1 h2, unfold dist, rw abs_le, split,
    {
      have eq1 : a + 1 = -(-(a + 1)) := by norm_num,
      have ineq1 := h2.2, conv_rhs at ineq1 {rw eq1}, rw le_neg at ineq1,
      have ineq2 := h1.1, have ineq3 := add_le_add ineq1 ineq2,
      have eq2 : -(a + 1) + (a - 1) = -2 := by ring,
      have eq3 : -x₂ + x₁ = x₁ - x₂ := by ring,
      conv_lhs at ineq3 {rw eq2},conv_rhs at ineq3 {rw eq3}, exact ineq3,
    },
    {
      have ineq1 := h1.2,
      have ineq2 := h2.1, have eq1 : x₂ = -(-x₂) := by norm_num,
      rw [eq1, le_neg] at ineq2, have ineq3 := add_le_add ineq1 ineq2,
      have eq2 : a + 1 + -(a - 1) = 2 := by ring, rw eq2 at ineq3,
      have eq3 : x₁ + -x₂ = x₁ - x₂ := by ring, rw eq3 at ineq3, exact ineq3,
    },
  }
end


-- This is should be the hardest part
/-
Lemma 1. Let α be an irrational number which is a root of f(x) = Σ aⱼ Xᶨ ∈ Z[x] with
f(x) ≢  0.

Then there is a constant A = A(α) > 0 such that 
  if a and b are integers with b > 0,
  then |α - a / b| > A / b^n
-/

def f_eval_on_ℝ (f : polynomial ℤ) (α : ℝ) : ℝ := (f.map ℤembℝ).eval α

-- deriv (f_eval_on_ℝ f)
-- theorem deriv_f_ℝ (f : polynomial ℤ) : ∀ x : ℝ, deriv (f_eval_on_ℝ f) x = (f.map ℤembℝ).derivative.eval x :=
-- begin
--   -- intro x, type_check (f_eval_on_ℝ f),
-- end

theorem abs_f_eval_around_α_continuous (f : polynomial ℝ) (α : ℝ) : continuous_on (λ x : ℝ, (abs (f.eval x))) (set.Icc (α-1) (α+1)) :=
begin
  have H : (λ x : ℝ, (abs (f.eval x))) = abs ∘ (λ x, f.eval x),
  {
    exact rfl,
  },
  rw H,
  have H2 := polynomial.continuous_eval f,
  have H3 := continuous.comp real.continuous_abs H2,
  exact continuous.continuous_on H3
end

-- theorem f_nonzero_max_abs_f (f : polynomial ℝ) (f_nonzero : f ≠ 0) : ∃ 

-- private lemma f_eq_g_sum_f_eq_sum_g (f g : ℕ -> ℝ) (s : finset ℕ) : (∀ x ∈ s, f x = g x) -> (s.sum f) = (s.sum g) :=

private lemma same_coeff (f : polynomial ℤ) (n : ℕ): ℤembℝ (f.coeff n) = ((f.map ℤembℝ).coeff n) :=
begin
  simp, rw [polynomial.coeff_map], simp,
end

private lemma same_support (f : polynomial ℤ) : f.support = (f.map ℤembℝ).support :=
begin
  ext, split,
  {
    intro ha, replace ha : f.coeff a ≠ 0, exact finsupp.mem_support_iff.mp ha,
    have ineq1 : ℤembℝ (f.coeff a) ≠ 0, norm_num, exact ha,
    suffices : (polynomial.map ℤembℝ f).coeff a ≠ 0, exact finsupp.mem_support_iff.mpr this,
    rwa [polynomial.coeff_map],
  },
  {
    intro ha, replace ha : (polynomial.map ℤembℝ f).coeff a ≠ 0, exact finsupp.mem_support_iff.mp ha,
    rw [<-same_coeff] at ha,
    have ineq1 : f.coeff a ≠ 0,  simp at ha, exact ha,
    exact finsupp.mem_support_iff.mpr ineq1,
  }
end

-- private lemma same_function (f : polynomial ℤ) (a b : ℤ) (b_non_zero : b ≠ 0) : 
--   (λ (x : ℕ), (polynomial.map ℤembℝ f).coeff x * (↑a ^ x / ↑b ^ x)) =
--   (λ (x : ℕ), (1/b^f.nat_degree) * ((polynomial.map ℤembℝ f).coeff x * (↑a ^ x * ↑b ^ (f.nat_degree - x)))) :=
-- begin
--   ext, conv_rhs {
--     rw [mul_comm, mul_assoc],
--   }, 
--   suffices : ((a:ℝ) ^ x / (b:ℝ) ^ x) = (↑a ^ x * ↑b ^ (f.nat_degree - x) * (1 / ↑b ^ f.nat_degree)),
--   exact congr_arg (has_mul.mul ((polynomial.map ℤembℝ f).coeff x)) this,
--   have eq : (1 / ↑b ^ f.nat_degree) = (b:ℝ)^(-(f.nat_degree:ℤ)), norm_num,
--   rw div_eq_iff, simp,
--     conv_rhs {
--     rw [mul_assoc, mul_assoc, (mul_comm (↑b ^ (f.nat_degree - x))),
--     (mul_assoc (↑b ^ f.nat_degree)⁻¹), <-pow_add, <-nat.add_sub_assoc],
--   }, simp,
-- end

open_locale big_operators

private lemma sum_eq (S : finset ℕ) (f g : ℕ -> ℝ) : (∀ x ∈ S, f x = g x) -> S.sum f = S.sum g :=
begin
  intro h,
  have H := @finset.sum_congr _ _ S S f g _ _ h, exact H, refl,
end

-- set_option trace.simplify true

-- private lemma pow_div (b : ℝ) (hb : b ≠ 0) (m n : ℕ) : (b ^ m) / (b ^ n) = 1 / b ^ (n - m) :=
-- begin
--   sorry
-- end

theorem abs_f_at_p_div_q_ge_1_div_q_pow_n
  (f : polynomial ℤ) : (f.nat_degree > 1) -> 
  (∀ (a b : ℤ), (b ≠ 0) ->
  abs ((f.map ℤembℝ).eval (↑a/↑b)) > 1/(b^(f.nat_degree))) :=
begin
  intros f_deg a b b_non_zero,
  have eq : ((f.map ℤembℝ).eval (↑a/↑b)) = (∑ n in f.support, ℤembℝ (f.coeff n) * ↑a^n/↑b^n),
  {
    rw [polynomial.eval, polynomial.eval₂, finsupp.sum], simp, rw <-same_support,
    rw sum_eq, intros n hn,
    have H : (@coe_fn (polynomial ℝ) polynomial.coeff_coe_to_fun (f.map ℤembℝ))= (f.map ℤembℝ).coeff,
    {
      exact rfl,
    },
    rw H, replace H : (polynomial.map ℤembℝ f).coeff n = ↑(f.coeff n),
    {
      rw polynomial.coeff_map, simp,
    },
    rw H, ring,
  },
  rw eq, simp, -- TODO : I think I am stucked here
  have eq2 : (∑ n in f.support, ℤembℝ (f.coeff n) * ↑a^n/↑b^n) = (∑ n in f.support, ((ℤembℝ (f.coeff n)) * (↑a^n * ↑b^(f.nat_degree-n))) * (1/↑b^f.nat_degree)),
  {
    rw sum_eq, intros m hm,
    -- have H : (polynomial.map ℤembℝ f).coeff m = ↑(f.coeff m), rw polynomial.coeff_map, simp,
    -- simp only [eq,]
    conv_lhs {
      rw mul_div_assoc,
    },
    conv_rhs {rw mul_assoc},
    have eq3 := @mul_div_assoc ℝ _ (↑a ^ m * ↑b ^ (f.nat_degree - m)) 1 (↑b ^ f.nat_degree),
    rw <-eq3,
    simp only [mul_one],
    conv_rhs {rw mul_div_assoc}, 
    --rw (pow_div ↑b _ (f.nat_degree - m) f.nat_degree),
  }
  -- rw [polynomial.eval, polynomial.eval₂, finsupp.sum], simp, rw <-same_support,

  -- generalize fun1_def : (λ (x:ℕ), ((polynomial.map ℤembℝ f).coeff x) * ((a:ℝ)^x / (b:ℝ)^x)) = fun1,
  -- generalize fun2_def : (λ (x:ℕ), ((polynomial.map ℤembℝ f).coeff x) * (↑a^x * ↑b^(f.nat_degree-x)) * (1/(b^f.nat_degree:ℝ))) = fun2,

  -- have eq1 : (f.support.sum fun1) = (f.support.sum fun2),
  -- {
  --   suffices eq2 : (f.support.sum fun1) - (f.support.sum fun2) = 0, linarith,
  --   type_check @finsupp.sum_sub _ _ _ _ _ f fun1 fun2,
  -- }
  -- (f.support.sum 
    -- (λ (x : ℕ), ⇑(polynomial.map ℤembℝ f) x * (↑a ^ x / ↑b ^ x))) =
    -- f.support.sum 

  --abs (f.support.sum (λ (x : ℕ), ⇑f x * (↑a ^ x / ↑b ^ x))
end

-- theorem abs_f_at_p_div_q_ge_1_div_q_pow_n
--   (f : polynomial ℝ) : (f.degree > 1) -> 
--   (∀ (a b : ℤ), (b ≠ 0) ->
--   abs (f.eval (↑a/↑b)) > 1/(b^(f.nat_degree))) :=
-- begin
--   apply polynomial.induction_on f,
--   {
--     -- constant case,
--     -- not possible
--     intros c absurd,
--     by_cases (c = 0), rw h at absurd, simp at absurd, exfalso, assumption, 
--     have h' := polynomial.degree_C h, rw h' at absurd,  simp at absurd, exfalso,
--     exact option.not_is_some_iff_eq_none.mpr absurd rfl,
--   },
--   {
--     intros p q hp hq p_add_q_deg a b b_non_zero,
--     -- degree_add_le
--     rw polynomial.eval_add,

--     have h := abs_abs_sub_abs_le_abs_sub (polynomial.eval (↑a / ↑b) p) (- polynomial.eval (↑a / ↑b) q),
--     simp at h,
--     suffices : abs (abs (polynomial.eval (↑a / ↑b) p) - abs (polynomial.eval (↑a / ↑b) q)) > 1 / ↑b ^ (p + q).nat_degree,
--     linarith,
--     by_cases hpq : (p.degree ≥ q.degree),
--     {
--       have p_deg : p.degree > 1,
--       {
--         by_contra absurd, simp at absurd,
--         -- because otherwise q has degree ≤ 1
--         have q_deg : q.degree ≤ 1, exact le_trans hpq absurd,
--         -- then p + q degree < 1
--         have ineq := polynomial.degree_add_le p q,
--         have ineq2 := max_le absurd q_deg, 
--         replace absurd : (p + q).degree ≤ 1, exact le_trans ineq ineq2,
--         rw [gt_iff_lt, lt_iff_not_ge, ge_iff_le] at p_add_q_deg, exact p_add_q_deg absurd,
--       },
--       replace hp := hp p_deg a b b_non_zero,
--     }
--     -- type_check abs_add (polynomial.eval (↑a / ↑b) p) (polynomial.eval (↑a / ↑b) q),
--   }
-- end


lemma about_irrational_root (α : real) (hα : irrational α) (f : polynomial ℤ) 
  (f_nonzero : f ≠ 0) (α_root : f_eval_on_ℝ f α = 0) :
  ∃ A : real, ∀ a b : int, b > 0 -> abs(α - a / b) > (A / b ^ (f.nat_degree)) :=
begin
  generalize hfℝ: f.map ℤembℝ = f_ℝ,
  have hfℝ_nonzero : f_ℝ ≠ 0,
  {
    by_contra absurd, simp at absurd, rw [polynomial.ext_iff] at absurd,
    have absurd2 : f = 0,
    {
      ext, replace absurd := absurd n, simp at absurd ⊢,
      rw [<-hfℝ, polynomial.coeff_map, ℤembℝ] at absurd,
      simp at absurd, exact absurd,
    },
    exact f_nonzero absurd2,
  },
  generalize hDf: f_ℝ.derivative = Df_ℝ,
  have H := compact.exists_forall_ge (@compact_Icc (α-1) (α+1)) 
              begin rw set.nonempty, use α, rw set.mem_Icc, split, linarith, linarith end
              (abs_f_eval_around_α_continuous Df_ℝ α),

  choose x_max hx_max using H,
  generalize M_def: abs (Df_ℝ.eval x_max) = M,
  have hM := hx_max.2, rw M_def at hM,
  have M_non_zero : M ≠ 0,
  {
    -- by_contra absurd,
    -- simp at absurd, rw absurd at hM,
    -- replace hM : ∀ (y : ℝ), y ∈ set.Icc (α - 1) (α + 1) → (polynomial.eval y Df_ℝ) = 0,
    -- {
    --   intros y hy,
    --   have H := hM y hy, simp at H, rw H,
    -- },
    -- replace hM : Df_ℝ = 0,
    -- {
    --   exact f_zero_on_interval_f_zero Df_ℝ hM,
    -- },
    -- rename hM Df_ℝ_zero,
    -- have f_ℝ_0 : f_ℝ.nat_degree = 0,
    -- {
    --   have H := small_things.zero_deriv_imp_const_poly_ℝ f_ℝ _, exact H,
    --   rw [<-hDf] at Df_ℝ_zero, assumption,
    -- },
    -- replace f_ℝ_0 := small_things.degree_0_constant f_ℝ f_ℝ_0,
    -- choose c hc using f_ℝ_0,
    -- -- f = c constant
    -- -- c must be 0 because f(α) = 0
    -- have absurd2 : c = 0,
    -- {
    --   rw [f_eval_on_ℝ, hfℝ, hc] at α_root, simp at α_root, assumption,
    -- },
    -- -- if c is zero contradiction to f_nonzero
    -- -- {
    -- rw absurd2 at hc,
    -- have f_zero : f = 0,
    -- {
    --   ext,
    --   have f_ℝ_n : f_ℝ.coeff n = 0, 
    --   have H := @polynomial.coeff_map _ _ _ f _ ℤembℝ n,
    --   rw [hfℝ, hc] at H, simp at H, 
    --   rw [<-hfℝ, @polynomial.coeff_map _ _ _ f _ ℤembℝ n], simp at H ⊢, norm_cast at H, exact eq.symm H,
    --   simp, rw [<-hfℝ, @polynomial.coeff_map _ _ _ f _ ℤembℝ n] at f_ℝ_n, simp at f_ℝ_n, assumption,
    -- },
    -- exact f_nonzero f_zero,
    sorry -- compiles, but too slow
  },
  have M_pos : M > 0,
  {
    rw <-M_def at M_non_zero ⊢,
    have H := abs_pos_iff.2 M_non_zero, simp [abs_abs] at H, exact H,
  },
  generalize roots_def :  f_ℝ.roots = f_roots,
  generalize roots'_def : f_roots.erase α = f_roots', 
  generalize roots_distance_to_α : f_roots'.image (λ x, abs (α - x)) = distances,
  generalize hdistances' : insert (1/M) (insert (1:ℝ) distances) = distances',
  have hnon_empty: distances'.nonempty,
  {
    rw <-hdistances',
    rw [finset.nonempty], use (1/M), simp,
  },
  generalize hB : finset.min' distances' hnon_empty = B,
  have allpos : ∀ x : ℝ, x ∈ distances' -> x > 0,
  {
    intros x hx, rw [<-hdistances', finset.mem_insert, finset.mem_insert] at hx,
    cases hx,
    {
      -- 1 / M
      rw hx, simp, exact M_pos,
    },
    cases hx,
    {
      -- 1
      rw hx, exact zero_lt_one,
    },
    {
      -- x is abs (root - α) with root not α
      simp [<-roots_distance_to_α] at hx,
      choose α0 hα0 using hx,
      rw [<-roots'_def, finset.mem_erase] at hα0,
      rw <-(hα0.2), simp, apply (@abs_pos_iff ℝ _ (α - α0)).2,
      by_contra absurd, simp at absurd, rw sub_eq_zero_iff_eq at absurd,
      have absurd2 := hα0.1.1, exact f_nonzero (false.rec (f = 0) (absurd2 (eq.symm absurd))),
    },
  },
  have B_pos : B > 0,
  {
    have h := allpos (finset.min' distances' hnon_empty) (finset.min'_mem distances' hnon_empty),
    rw <-hB, assumption,
  },
  generalize hA : B / 2 = A,
  use A,
  by_contra absurd, simp at absurd,
  choose a ha using absurd,
  choose b hb using ha,


  have hb2 : b ^ f.nat_degree ≥ 1,
  {
    rw <-(pow_zero b),
    have hbge1 : b ≥ 1 := hb.1,
    have htrivial : 0 ≤ f.nat_degree := by exact bot_le,
    exact pow_le_pow hbge1 htrivial,
  },
  have hb21 : abs (α - a / b) ≤ A,
  {
    suffices H : (A / b ^ f.nat_degree) ≤ A,
    have H2 := hb.2, exact le_trans H2 H,
    apply (@div_le_iff ℝ _ A (b ^ f.nat_degree) A _).2,
    apply (@le_mul_iff_one_le_right ℝ _ (b ^ f.nat_degree) A _).2, norm_cast at hb2 ⊢, exact hb2,
    norm_cast, linarith, norm_cast, linarith,
  },
  have hb22 : abs (α - a/b) < B,
  {
    have H := half_lt_self B_pos, rw hA at H, exact gt_of_gt_of_ge H hb21,
  },
  -- then a / b is in [α-1, α+1]
  have hab0 : (a/b:ℝ) ∈ set.Icc (α-1) (α+1),
  {
    suffices H : abs (α - a/b) ≤ 1, 
    have eq1 : ↑a / ↑b - α = - (α - ↑a / ↑b) := by norm_num,
    rw [<-closed_ball_Icc, metric.mem_closed_ball, real.dist_eq, eq1, abs_neg], exact H,
    suffices : B ≤ 1, linarith,
    rw <-hB, have ineq1 := finset.min'_le distances' hnon_empty 1 _, exact ineq1,
    rw [<-hdistances', finset.mem_insert, finset.mem_insert], right, left, refl,
  },
  -- a/b is not a root
  have hab1 : (↑a/↑b:ℝ) ≠ α,
  {
    have H := hα a b hb.1, rw sub_ne_zero at H, exact ne.symm H,
  },
  have hab2 : (↑a/↑b:ℝ) ∉ f_roots,
  {
    by_contra absurd,
    have H : ↑a/↑b ∈ f_roots',
    {
      rw [<-roots'_def, finset.mem_erase], exact ⟨hab1, absurd⟩,
    },
    have H2 : abs (α - ↑a/↑b) ∈ distances',
    {
      rw [<-hdistances', finset.mem_insert, finset.mem_insert], right, right,
      rw [<-roots_distance_to_α, finset.mem_image], use ↑a/↑b, split, exact H, refl,
    },
    have H3 := finset.min'_le distances' hnon_empty (abs (α - ↑a / ↑b)) H2,
    rw hB at H3, linarith,
  },
  -- either α > a/b or α < a/b, two cases essentially have the same proof
  have hab3 := ne_iff_lt_or_gt.1 hab1,
  cases hab3,
  {
    -- α > a/b subcase
    have H := exists_deriv_eq_slope (λ x, f_ℝ.eval x) hab3 _ _,
    choose x0 hx0 using H,
    have hx0l := hx0.1,
    have hx0r := hx0.2,
    -- clean hx0 a bit to be more usable,
    rw [polynomial.deriv, hDf, <-hfℝ] at hx0r,
    rw [f_eval_on_ℝ] at α_root, rw [α_root, hfℝ] at hx0r, simp at hx0r,

    have H2 : abs(α - ↑a/↑b) = abs((f_ℝ.eval (↑a/↑b)) / (Df_ℝ.eval x0)),
    {
      norm_num [hx0r], 
      rw [neg_div, div_neg, abs_neg, div_div_cancel'],
      rw [<-roots_def] at hab2, by_contra absurd, simp at absurd,
      have H := polynomial.mem_roots _, rw polynomial.is_root at H,
      replace H := H.2 absurd, exact hab2 H,
      exact hfℝ_nonzero,
    },

  }


end

-- #reduce (polynomial ℤ)

def divide_f_by_gcd_of_coeff_make_leading_term_pos (f : polynomial ℤ) : polynomial ℤ :=
{
  to_fun := (λ n, if f.coeff (f.nat_degree) > 0 
                  then f.coeff n / gcd_int.gcd_of_list (list_coeff f)
                  else -(f.coeff n / gcd_int.gcd_of_list (list_coeff f))),
  support := f.support,
  mem_support_to_fun :=
  begin
    intro n, split,
    by_cases (f.coeff (f.nat_degree) > 0), rename h pos,
    {
      intro hn, have h := (f.3 n).1 hn, simp [pos],
      type_check gcd_int.gcd_of_list_dvd_mem_of_list (list_coeff f) (f.coeff n) (coeff_in_list_coeff f n hn),
      have H := @int.div_eq_iff_eq_mul_left (f.coeff n) (gcd_int.gcd_of_list (list_coeff f)) 0 (gcd_int.gcd_of_list_non_zero (list_coeff f))
        (gcd_int.gcd_of_list_dvd_mem_of_list (list_coeff f) (f.coeff n) (coeff_in_list_coeff f n hn)),
      intro absurd,
      replace absurd := H.1 absurd, simp at absurd,
      exact h absurd,
    },
    rename h neg,
    {
      intro hn, simp [neg],
      have h := (f.3 n).1 hn,
      have H := @int.div_eq_iff_eq_mul_left (f.coeff n) (gcd_int.gcd_of_list (list_coeff f)) 0 (gcd_int.gcd_of_list_non_zero (list_coeff f))
        (gcd_int.gcd_of_list_dvd_mem_of_list (list_coeff f) (f.coeff n) (coeff_in_list_coeff f n hn)),
      intro absurd,
      replace absurd := H.1 absurd, simp at absurd,
      exact h absurd,
    },
    by_cases (f.coeff (f.nat_degree) > 0), rename h pos,
    {
      contrapose,
      intro hn, simp [pos],
      have h := (not_in_support_iff_coeff_zero f n).2 hn, rw h, norm_num,
    }, rename h neg,
    {
      contrapose,
      intro hn, simp [neg],
      have h := (not_in_support_iff_coeff_zero f n).2 hn, rw h, norm_num,
    }
  end
}

-- def neg_f (f : polynomial ℤ) : polynomial ℤ :=
-- {
--   support := f.support,
--   to_fun := (λ n, - (f.coeff n)),
--   mem_support_to_fun :=
--   begin
--     intro n, split,
--     {
--       intro hn,  exact norm_num.ne_zero_neg (polynomial.coeff f n) ((f.3 n).1 hn),
--     },
--     {
--       intro hn, have h := norm_num.ne_zero_neg (-f.coeff n) hn, simp at h, exact finsupp.mem_support_iff.mpr h,
--     }
--   end
-- }

-- lemma neg_f_f_have_same_nat_deg (f : polynomial ℤ) (n : ℕ) : f.nat_degree = (-f).nat_degree :=
-- begin
--   rw [polynomial.nat_degree, polynomial.nat_degree],
-- end


#reduce (1: int) / (2 : int)

-- lemma about_irrational_root_f_leading_term_pos_all_coeffs_coprime_trivial_subcase
--   (α : real) (hα : irrational α) (f : polynomial ℤ) 
--   (f_nonzero : f ≠ 0)
--   (f_leading_term_pos : f.coeff (f.nat_degree) > 0)
--   (f_coeffs_coprime : gcd_int.gcd_of_list (list_coeff f) = 1)
--   (α_root : (f.map ℤembℝ).eval α = 0) :
--   ∀ a b : ℤ, b > 0 -> abs(α - a / b) ≥ 1 -> abs(α - a / b) > (1 / b ^ (f.nat_degree)) := 
-- begin
--   intros a b hb h,
--   sorry
-- end

-- lemma about_irrational_root_f_leading_term_pos_all_coeffs_coprime
--   (α : real) (hα : irrational α) (f : polynomial ℤ) 
--   (f_nonzero : f ≠ 0)
--   (f_leading_term_pos : f.coeff (f.nat_degree) > 0)
--   (f_coeffs_coprime : gcd_int.gcd_of_list (list_coeff f) = 1)
--   (α_root : (f.map ℤembℝ).eval α = 0) :
--   ∃ A : real, ∀ a b : ℤ, b > 0 -> abs(α - a / b) > (A / b ^ (f.nat_degree)) := 

-- begin

-- end


lemma liouville_numbers_irrational: ∀ (x : real), (liouville_number x) -> irrational x :=
begin
  sorry
end



theorem liouville_numbers_transcendental : ∀ x : real, liouville_number x -> ¬(is_algebraic rat x) := sorry


-- define an example of Liouville number Σᵢ 1/2^(i!)

-- function n -> 1/2^n! 
def two_pow_n_fact_inverse (n : nat) : real := (1/2)^n.fact
-- function n -> 1/2^n
def two_pow_n_inverse (n : nat) : real := (1/2)^n

lemma two_pow_n_fact_inverse_ge_0 (n : nat) : two_pow_n_fact_inverse n ≥ 0 :=
begin
    unfold two_pow_n_fact_inverse,
    simp, have h := le_of_lt (@pow_pos _ _ (2:real) _ n.fact),
    norm_cast at h ⊢, exact h, norm_num, done
end

lemma useless_elsewhere : ∀ n : nat, n ≤ n.fact
| 0                         := by norm_num
| 1                         := by norm_num
| (nat.succ (nat.succ n))   := begin 
    have H := useless_elsewhere n.succ,
    conv_rhs {rw (nat.fact_succ n.succ)},
    have ineq1 : n.succ.succ * n.succ ≤ n.succ.succ * n.succ.fact, {exact nat.mul_le_mul_left (nat.succ (nat.succ n)) (useless_elsewhere (nat.succ n))},
    suffices ineq2 : n.succ.succ ≤ n.succ.succ * n.succ, {exact nat.le_trans ineq2 ineq1},
    have H' : ∀ m : nat, m.succ.succ ≤ m.succ.succ * m.succ,
    {
        intro m, induction m with m hm,
        norm_num,
        simp [nat.succ_mul, nat.mul_succ, nat.succ_eq_add_one] at hm ⊢,
    },
    exact H' n,
end

lemma useless_elsewhere2 : 2 ≠ 0 := by norm_num

lemma two_pow_n_fact_inverse_le_two_pow_n_inverse (n : nat) : two_pow_n_fact_inverse n ≤ two_pow_n_inverse n :=
begin
  unfold two_pow_n_fact_inverse,
  unfold two_pow_n_inverse, simp,
  by_cases (n = 0),
  -- if n is 0
  rw h, simp, norm_num,
  -- if n > 0
  have n_pos : n > 0 := by exact bot_lt_iff_ne_bot.mpr h,
  have H := (@inv_le_inv ℝ _ (2 ^ n.fact) (2 ^ n) _ _).2 _, exact H,
  have H := @pow_pos ℝ _ 2 _ n.fact,  exact H, exact two_pos,
  have H := @pow_pos ℝ _ 2 _ n, exact H, exact two_pos,
  have H := @pow_le_pow ℝ _ 2 n n.fact _ _, exact H, norm_num, exact useless_elsewhere n,
end

-- Σᵢ 1/2ⁱ exists
theorem summable_two_pow_n_inverse : summable two_pow_n_inverse :=
begin
  exact summable_geometric_two,
end

-- Hence Σᵢ 1/2^i! exists by comparison test
theorem summable_two_pow_n_fact_inverse : summable two_pow_n_fact_inverse :=
begin
  exact @summable_of_nonneg_of_le _ two_pow_n_inverse two_pow_n_fact_inverse two_pow_n_fact_inverse_ge_0 two_pow_n_fact_inverse_le_two_pow_n_inverse summable_two_pow_n_inverse,
end

-- define α to be Σᵢ 1/2^i!
def α := classical.some summable_two_pow_n_fact_inverse

-- Then α is a Liouville number hence a transcendental number.
theorem liouville_α : liouville_number α :=
begin
  intro n,
  sorry
end

theorem transcendental_α : transcendental α := liouville_numbers_transcendental α liouville_α

