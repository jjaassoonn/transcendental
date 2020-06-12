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

def transcendental (x : real) := ¬(is_algebraic ℤ x)

def liouville_number (x : real) := ∀ n : nat, ∃ a b : int, b > 1 ∧ 0 < abs(x - a / b) ∧ abs(x - a / b) < 1/b^n


def irrational (x : real) := ∀ a b : int, b > 0 -> x - a / b ≠ 0

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

open_locale big_operators

private lemma sum_eq (S : finset ℕ) (f g : ℕ -> ℝ) : (∀ x ∈ S, f x = g x) -> ∑ i in S, f i = ∑ i in S, g i :=
begin
  intro h,
  have H := @finset.sum_congr _ _ S S f g _ _ h, exact H, refl,
end

private lemma eval_f_a_div_b (f : polynomial ℤ) (f_deg : f.nat_degree > 1) (a b : ℤ) (b_non_zero : b > 0) (a_div_b_not_root : (f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ)) ≠ 0) :
  ((f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ))) = ((1:ℝ)/(b:ℝ)^f.nat_degree) * (∑ i in f.support, (f.coeff i : ℝ)*(a:ℝ)^i*(b:ℝ)^(f.nat_degree - i)) :=
begin
  rw [finset.mul_sum, polynomial.eval_map, polynomial.eval₂, finsupp.sum, sum_eq], intros i hi,
  rw polynomial.apply_eq_coeff, 
  simp, rw <-mul_assoc (↑b ^ f.nat_degree)⁻¹, rw <-mul_assoc (↑b ^ f.nat_degree)⁻¹, field_simp,

  suffices eq : ↑a ^ i / ↑b ^ i = ↑a ^ i * ↑b ^ (f.nat_degree - i) / ↑b ^ f.nat_degree,
  {
    have H := (@mul_left_inj' ℝ _ (↑a ^ i / ↑b ^ i) (↑a ^ i * ↑b ^ (f.nat_degree - i) / ↑b ^ f.nat_degree) ↑(f.coeff i) _).2 eq,
    conv_lhs at H {rw mul_comm, rw <-mul_div_assoc}, conv_rhs at H {rw mul_comm}, rw H, ring,

    have H := (f.3 i).1 hi, rw polynomial.coeff, norm_cast, exact H,
  },

  have eq1 := @fpow_sub ℝ _ (b:ℝ) _ (f.nat_degree - i) f.nat_degree,
  have eq2 : (f.nat_degree:ℤ) - (i:ℤ) - (f.nat_degree:ℤ) = - i,
  {
    rw [sub_sub, add_comm, <-sub_sub], simp,
  }, 
  rw eq2 at eq1, rw [fpow_neg, inv_eq_one_div] at eq1,
  have eqb1 : (b:ℝ) ^ (i:ℤ) = (b:ℝ) ^ i, 
  {
    norm_num,
  },
  rw eqb1 at eq1,
  have eq3 : (f.nat_degree : ℤ) - (i:ℤ) = int.of_nat (f.nat_degree - i),
  {
    norm_num, rw int.coe_nat_sub, by_contra rid, simp at rid,
    have hi' := polynomial.coeff_eq_zero_of_nat_degree_lt rid,
    have ineq2 := (f.3 i).1 hi, exact a_div_b_not_root (false.rec (polynomial.eval (↑a / ↑b) (polynomial.map ℤembℝ f) = 0) (ineq2 hi')),
  },
  have eqb2 : (b:ℝ) ^ ((f.nat_degree:ℤ) - (i:ℤ)) = (b:ℝ) ^ (f.nat_degree - i),
  {
    rw eq3, norm_num,
  }, rw eqb2 at eq1,

  have eqb3 : (b:ℝ)^(f.nat_degree:ℤ)= (b:ℝ)^f.nat_degree := by norm_num, rw eqb3 at eq1, conv_rhs {rw [mul_div_assoc, <-eq1]},
  simp, rw <-div_eq_mul_inv,


  norm_cast, linarith,
end

private lemma cast1 (f : polynomial ℤ) (f_deg : f.nat_degree > 1) (a b : ℤ) (b_non_zero : b > 0) (a_div_b_not_root : (f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ)) ≠ 0) :
  ∑ i in f.support, (f.coeff i : ℝ)*(a:ℝ)^i*(b:ℝ)^(f.nat_degree - i) = (ℤembℝ (∑ i in f.support, (f.coeff i) * a^i * b ^ (f.nat_degree - i))) :=
begin
  rw ring_hom.map_sum, rw sum_eq, intros i hi, norm_num,
end

private lemma ineq1 (f : polynomial ℤ) (f_deg : f.nat_degree > 1) (a b : ℤ) (b_non_zero : b > 0) (a_div_b_not_root : (f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ)) ≠ 0) : 
  ∑ i in f.support, (f.coeff i) * a^i * b ^ (f.nat_degree - i) ≠ 0 :=
begin
  suffices eq1 : ℤembℝ (∑ i in f.support, (f.coeff i) * a^i * b ^ (f.nat_degree - i)) ≠ 0,
  {
    intro rid, rw rid at eq1,
    conv_rhs at eq1 {rw <-ℤembℝ_zero}, simpa,
  },
  intro rid,
  have cast1 := cast1 f f_deg a b b_non_zero a_div_b_not_root, rw rid at cast1,
  have eq2 := (@domain.mul_right_inj ℝ _ ((1:ℝ)/(b:ℝ)^f.nat_degree) _ _ _).2 cast1,
  rw <-eval_f_a_div_b at eq2, simp at eq2, exact a_div_b_not_root eq2,
  exact f_deg, exact b_non_zero, exact a_div_b_not_root,
  
  intro rid, norm_num at rid, replace rid := pow_eq_zero rid, norm_cast at rid, linarith,
end

private lemma ineq2 (f : polynomial ℤ) (f_deg : f.nat_degree > 1) (a b : ℤ) (b_non_zero : b > 0) (a_div_b_not_root : (f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ)) ≠ 0) : 
  ℤembℝ (∑ i in f.support, (f.coeff i) * a^i * b ^ (f.nat_degree - i)) ≠ 0 :=
begin
  have cast1 := cast1 f f_deg a b b_non_zero a_div_b_not_root,
  have ineq1 := ineq1 f f_deg a b b_non_zero a_div_b_not_root,
  norm_cast, intro rid, rw <-ℤembℝ_zero at rid, replace rid := ℤembℝ_inj rid,
  exact a_div_b_not_root (false.rec (polynomial.eval (↑a / ↑b) (polynomial.map ℤembℝ f) = 0) (ineq1 rid)),
end

private lemma ineqb (f : polynomial ℤ) (f_deg : f.nat_degree > 1) (a b : ℤ) (b_non_zero : b > 0) (a_div_b_not_root : (f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ)) ≠ 0) :
  abs (1/(b:ℝ)^f.nat_degree) = 1/(b:ℝ)^f.nat_degree := 
begin
  rw abs_of_pos, norm_num, norm_cast, refine pow_pos _ f.nat_degree, exact b_non_zero,
end

private lemma abs_ℤembℝ (x : ℤ) : ℤembℝ (abs x) = abs (ℤembℝ x) :=
begin
  simp,
end

private lemma ineq3 (x : ℤ) (hx : x ≥ 1) : ℤembℝ x ≥ 1 :=
begin
  simp, norm_cast, exact hx,
end

theorem abs_f_at_p_div_q_ge_1_div_q_pow_n (f : polynomial ℤ) (f_deg : f.nat_degree > 1) (a b : ℤ) (b_non_zero : b > 0) (a_div_b_not_root : (f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ)) ≠ 0) :
  @abs ℝ _ ((f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ))) ≥ 1/(b:ℝ)^f.nat_degree :=
begin
  have eval1 := eval_f_a_div_b f f_deg a b b_non_zero a_div_b_not_root,
  have cast1 := cast1 f f_deg a b b_non_zero a_div_b_not_root,
  have ineq1 := ineq1 f f_deg a b b_non_zero a_div_b_not_root,
  have ineq2 := ineq2 f f_deg a b b_non_zero a_div_b_not_root,
  rw [eval1, abs_mul, ineqb f f_deg a b b_non_zero a_div_b_not_root, cast1],
  suffices ineq3 : abs (ℤembℝ (∑ (i : ℕ) in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i))) ≥ 1,
  {
    rw ge_iff_le,
    have H := @mul_le_mul ℝ _ 1 (1/(b:ℝ)^f.nat_degree) (abs (ℤembℝ (∑ (i : ℕ) in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i)))) (1/(b:ℝ)^f.nat_degree) ineq3 _ _ _,
    rw one_mul at H, rw mul_comm at H, exact H,
    exact le_refl (1 / ↑b ^ polynomial.nat_degree f),
    norm_num, replace H := @pow_nonneg ℝ _ b _ f.nat_degree, exact H, norm_cast, exact ge_trans b_non_zero trivial,

    exact abs_nonneg _,
  },
  rw <-abs_ℤembℝ, apply ineq3,
  have ineq4 : abs (∑ (i : ℕ) in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i)) > 0,
  {
    apply abs_pos_iff.2, exact ineq1,
    
  }, 
  exact ineq4,
end

lemma about_irrational_root (α : real) (hα : irrational α) (f : polynomial ℤ) 
  (f_deg : f.nat_degree > 1) (α_root : f_eval_on_ℝ f α = 0) :
  ∃ A : real, A > 0 ∧ ∀ a b : int, b > 0 -> abs(α - a / b) > (A / b ^ (f.nat_degree)) := sorry -- compiles in terminal but is very slow
-- begin
--   have f_nonzero : f ≠ 0,
--   {
--     by_contra rid,
--     simp at rid, have f_nat_deg_zero : f.nat_degree = 0, exact (congr_arg polynomial.nat_degree rid).trans rfl,
--     rw f_nat_deg_zero at f_deg, linarith,
--   },
--   generalize hfℝ: f.map ℤembℝ = f_ℝ,
--   have hfℝ_nonzero : f_ℝ ≠ 0,
--   {
--     by_contra absurd, simp at absurd, rw [polynomial.ext_iff] at absurd,
--     have absurd2 : f = 0,
--     {
--       ext, replace absurd := absurd n, simp at absurd ⊢,
--       rw [<-hfℝ, polynomial.coeff_map, ℤembℝ] at absurd,
--       simp at absurd, exact absurd,
--     },
--     exact f_nonzero absurd2,
--   },
--   generalize hDf: f_ℝ.derivative = Df_ℝ,
--   have H := compact.exists_forall_ge (@compact_Icc (α-1) (α+1)) 
--               begin rw set.nonempty, use α, rw set.mem_Icc, split, linarith, linarith end
--               (abs_f_eval_around_α_continuous Df_ℝ α),

--   choose x_max hx_max using H,
--   generalize M_def: abs (Df_ℝ.eval x_max) = M,
--   have hM := hx_max.2, rw M_def at hM,
--   have M_non_zero : M ≠ 0,
--   {
--     by_contra absurd,
--     simp at absurd, rw absurd at hM,
--     replace hM : ∀ (y : ℝ), y ∈ set.Icc (α - 1) (α + 1) → (polynomial.eval y Df_ℝ) = 0,
--     {
--       intros y hy,
--       have H := hM y hy, simp at H, rw H,
--     },
--     replace hM : Df_ℝ = 0,
--     {
--       exact f_zero_on_interval_f_zero Df_ℝ hM,
--     },
--     rename hM Df_ℝ_zero,
--     have f_ℝ_0 : f_ℝ.nat_degree = 0,
--     {
--       have H := small_things.zero_deriv_imp_const_poly_ℝ f_ℝ _, exact H,
--       rw [<-hDf] at Df_ℝ_zero, assumption,
--     },
--     replace f_ℝ_0 := small_things.degree_0_constant f_ℝ f_ℝ_0,
--     choose c hc using f_ℝ_0,
--     -- f = c constant
--     -- c must be 0 because f(α) = 0
--     have absurd2 : c = 0,
--     {
--       rw [f_eval_on_ℝ, hfℝ, hc] at α_root, simp at α_root, assumption,
--     },
--     -- if c is zero contradiction to f_nonzero
--     -- {
--     rw absurd2 at hc,
--     have f_zero : f = 0,
--     {
--       ext,
--       have f_ℝ_n : f_ℝ.coeff n = 0, 
--       have H := @polynomial.coeff_map _ _ _ f _ ℤembℝ n,
--       rw [hfℝ, hc] at H, simp at H, 
--       rw [<-hfℝ, @polynomial.coeff_map _ _ _ f _ ℤembℝ n], simp at H ⊢, norm_cast at H, exact eq.symm H,
--       simp, rw [<-hfℝ, @polynomial.coeff_map _ _ _ f _ ℤembℝ n] at f_ℝ_n, simp at f_ℝ_n, assumption,
--     },
--     exact f_nonzero f_zero,
    
--   },
--   have M_pos : M > 0,
--   {
--     rw <-M_def at M_non_zero ⊢,
--     have H := abs_pos_iff.2 M_non_zero, simp [abs_abs] at H, exact H,
--   },
--   generalize roots_def :  f_ℝ.roots = f_roots,
--   generalize roots'_def : f_roots.erase α = f_roots', 
--   generalize roots_distance_to_α : f_roots'.image (λ x, abs (α - x)) = distances,
--   generalize hdistances' : insert (1/M) (insert (1:ℝ) distances) = distances',
--   have hnon_empty: distances'.nonempty,
--   {
--     rw <-hdistances',
--     rw [finset.nonempty], use (1/M), simp,
--   },
--   generalize hB : finset.min' distances' hnon_empty = B,
--   have allpos : ∀ x : ℝ, x ∈ distances' -> x > 0,
--   {
--     intros x hx, rw [<-hdistances', finset.mem_insert, finset.mem_insert] at hx,
--     cases hx,
--     {
--       -- 1 / M
--       rw hx, simp, exact M_pos,
--     },
--     cases hx,
--     {
--       -- 1
--       rw hx, exact zero_lt_one,
--     },
--     {
--       -- x is abs (root - α) with root not α
--       simp [<-roots_distance_to_α] at hx,
--       choose α0 hα0 using hx,
--       rw [<-roots'_def, finset.mem_erase] at hα0,
--       rw <-(hα0.2), simp, apply (@abs_pos_iff ℝ _ (α - α0)).2,
--       by_contra absurd, simp at absurd, rw sub_eq_zero_iff_eq at absurd,
--       have absurd2 := hα0.1.1, exact f_nonzero (false.rec (f = 0) (absurd2 (eq.symm absurd))),
--     },
--   },
--   have B_pos : B > 0,
--   {
--     have h := allpos (finset.min' distances' hnon_empty) (finset.min'_mem distances' hnon_empty),
--     rw <-hB, assumption,
--   },
--   generalize hA : B / 2 = A,
--   use A, split,
--   -- A > 0
--   rw [<-hA], apply half_pos, assumption,

--   by_contra absurd, simp at absurd,
--   choose a ha using absurd,
--   choose b hb using ha,


--   have hb2 : b ^ f.nat_degree ≥ 1,
--   {
--     rw <-(pow_zero b),
--     have hbge1 : b ≥ 1 := hb.1,
--     have htrivial : 0 ≤ f.nat_degree := by exact bot_le,
--     exact pow_le_pow hbge1 htrivial,
--   },
--   have hb21 : abs (α - a / b) ≤ A,
--   {
--     suffices H : (A / b ^ f.nat_degree) ≤ A,
--     have H2 := hb.2, exact le_trans H2 H,
--     apply (@div_le_iff ℝ _ A (b ^ f.nat_degree) A _).2,
--     apply (@le_mul_iff_one_le_right ℝ _ (b ^ f.nat_degree) A _).2, norm_cast at hb2 ⊢, exact hb2,
--     norm_cast, linarith, norm_cast, linarith,
--   },
--   have hb21' : abs (α - a / b) ≤ A / (b^f.nat_degree),
--   {
--     exact hb.2,
--   },

--   have hb22 : abs (α - a/b) < B,
--   {
--     have H := half_lt_self B_pos, rw hA at H, exact gt_of_gt_of_ge H hb21,
--   },
--   -- then a / b is in [α-1, α+1]
--   have hab0 : (a/b:ℝ) ∈ set.Icc (α-1) (α+1),
--   {
--     suffices H : abs (α - a/b) ≤ 1, 
--     have eq1 : ↑a / ↑b - α = - (α - ↑a / ↑b) := by norm_num,
--     rw [<-closed_ball_Icc, metric.mem_closed_ball, real.dist_eq, eq1, abs_neg], exact H,
--     suffices : B ≤ 1, linarith,
--     rw <-hB, have ineq1 := finset.min'_le distances' hnon_empty 1 _, exact ineq1,
--     rw [<-hdistances', finset.mem_insert, finset.mem_insert], right, left, refl,
--   },
--   -- a/b is not a root
--   have hab1 : (↑a/↑b:ℝ) ≠ α,
--   {
--     have H := hα a b hb.1, rw sub_ne_zero at H, exact ne.symm H,
--   },
--   have hab2 : (↑a/↑b:ℝ) ∉ f_roots,
--   {
--     by_contra absurd,
--     have H : ↑a/↑b ∈ f_roots',
--     {
--       rw [<-roots'_def, finset.mem_erase], exact ⟨hab1, absurd⟩,
--     },
--     have H2 : abs (α - ↑a/↑b) ∈ distances',
--     {
--       rw [<-hdistances', finset.mem_insert, finset.mem_insert], right, right,
--       rw [<-roots_distance_to_α, finset.mem_image], use ↑a/↑b, split, exact H, refl,
--     },
--     have H3 := finset.min'_le distances' hnon_empty (abs (α - ↑a / ↑b)) H2,
--     rw hB at H3, linarith,
--   },
--   -- either α > a/b or α < a/b, two cases essentially have the same proof
--   have hab3 := ne_iff_lt_or_gt.1 hab1,
--   cases hab3,
--   {
--     -- α > a/b subcase
--     have H := exists_deriv_eq_slope (λ x, f_ℝ.eval x) hab3 _ _,
--     choose x0 hx0 using H,
--     have hx0l := hx0.1,
--     have hx0r := hx0.2,
--     -- clean hx0 a bit to be more usable,
--     rw [polynomial.deriv, hDf, <-hfℝ] at hx0r,
--     rw [f_eval_on_ℝ] at α_root, rw [α_root, hfℝ] at hx0r, simp at hx0r,
--     -- we have Df(x0) ≠ 0
--     have Df_x0_nonzero : Df_ℝ.eval x0 ≠ 0,
--     {
--       rw hx0r, intro rid, rw [neg_div, neg_eq_zero, div_eq_zero_iff] at rid,
--       rw [<-roots_def, polynomial.mem_roots, polynomial.is_root] at hab2, exact hab2 rid,
--       exact hfℝ_nonzero, linarith,
--       -- sorry,
--     },

--     have H2 : abs(α - ↑a/↑b) = abs((f_ℝ.eval (↑a/↑b)) / (Df_ℝ.eval x0)),
--     {
--       norm_num [hx0r], 
--       rw [neg_div, div_neg, abs_neg, div_div_cancel'],
--       rw [<-roots_def] at hab2, by_contra absurd, simp at absurd,
--       have H := polynomial.mem_roots _, rw polynomial.is_root at H,
--       replace H := H.2 absurd, exact hab2 H,
--       exact hfℝ_nonzero,
--     },

--     have ineq' : polynomial.eval (↑a / ↑b) (polynomial.map ℤembℝ f) ≠ 0,
--     {
--       rw <-roots_def at hab2, intro rid, rw [hfℝ, <-polynomial.is_root, <-polynomial.mem_roots] at rid,
--       exact hab2 rid, exact hfℝ_nonzero,
--     },

--     have ineq : abs (α - ↑a / ↑b) ≥ 1/(M*b^(f.nat_degree)),
--     {
--       rw [H2, abs_div],
--       have ineq := abs_f_at_p_div_q_ge_1_div_q_pow_n f f_deg a b hb.1 ineq',
--       rw [<-hfℝ],
--       -- have ineq2 : abs (polynomial.eval (↑a / ↑b) (polynomial.map ℤembℝ f)) / abs (polynomial.eval x0 Df_ℝ) > 1 / ↑b ^ f.nat_degree / abs (polynomial.eval x0 Df_ℝ),
--       -- type_check @div_le_iff ℝ _ (abs (polynomial.eval (↑a / ↑b) (polynomial.map ℤembℝ f))) (abs (polynomial.eval x0 Df_ℝ)),
      
--       have ineq2 : abs (polynomial.eval x0 Df_ℝ) ≤ M,
--       {
--         have H := hM x0 _, exact H,
--         have h1 := hx0.1,
--         have h2 := @set.Ioo_subset_Icc_self ℝ _ (α-1) (α+1),
--         have h3 := (@set.Ioo_subset_Ioo_iff ℝ _ _ (α-1) _ (α+1) _ hab3).2 _,
--         have h4 : set.Ioo (↑a / ↑b) α ⊆ set.Icc (α-1) (α+1), exact set.subset.trans h3 h2,
--         exact set.mem_of_subset_of_mem h4 h1, split,
--         rw set.mem_Icc at hab0, exact hab0.1, linarith,
--         -- sorry,
--       },
      
--       have ineq3 := small_things.a_ge_b_a_div_c_ge_b_div_c _ _ (abs (polynomial.eval x0 Df_ℝ)) ineq _ _,
--       suffices ineq4 : 1 / ↑b ^ f.nat_degree / abs (polynomial.eval x0 Df_ℝ) ≥ 1 / (M * ↑b ^ f.nat_degree),
--       {
--         have ineq : abs (polynomial.eval (↑a / ↑b) (polynomial.map ℤembℝ f)) / abs (polynomial.eval x0 Df_ℝ) ≥ 1 / (M * ↑b ^ f.nat_degree),
--         linarith,
--         exact ineq,
--       },
--       rw [div_div_eq_div_mul] at ineq3,
--       have ineq4 : 1 / (↑b ^ f.nat_degree * abs (polynomial.eval x0 Df_ℝ)) ≥ 1 / (M * ↑b ^ f.nat_degree),
--       {
--         rw [ge_iff_le, one_div_le_one_div], conv_rhs {rw mul_comm}, 
--         have ineq := ((@mul_le_mul_left ℝ _ (abs (polynomial.eval x0 Df_ℝ)) M (↑b ^ f.nat_degree)) _).2 ineq2, exact ineq,
--         replace ineq := pow_pos hb.1 f.nat_degree, norm_cast, exact ineq, have ineq' : (b:ℝ) ^ f.nat_degree > 0, norm_cast,
--         exact pow_pos hb.1 f.nat_degree, exact (mul_pos M_pos ineq'),
--         apply mul_pos, norm_cast, exact pow_pos hb.1 f.nat_degree, rw abs_pos_iff, exact Df_x0_nonzero,
--       },
--       rw div_div_eq_div_mul, exact ineq4, have ineq5 := @div_nonneg ℝ _ 1 (↑b ^ f.nat_degree) _ _, exact ineq5, norm_cast,
--       exact bot_le, norm_cast, exact pow_pos hb.1 f.nat_degree, rw [gt_iff_lt, abs_pos_iff], exact Df_x0_nonzero,
--     },

--     have ineq2 : 1/(M*b^(f.nat_degree)) > A / (b^f.nat_degree),
--     {
--       have ineq : A < B, rw [<-hA], exact @half_lt_self ℝ _ B B_pos,
--       have ineq2 : B ≤ 1/M, rw [<-hB], have H := finset.min'_le distances' hnon_empty (1/M) _, exact H,
--       rw [<-hdistances', finset.mem_insert], left, refl,
--       have ineq3 : A < 1/M, linarith,
--       rw [<-div_div_eq_div_mul], have ineq' := (@div_lt_div_right ℝ _ A (1/M) (↑b ^ f.nat_degree) _).2 ineq3,
--       rw <-gt_iff_lt at ineq', exact ineq', norm_cast, exact pow_pos hb.1 f.nat_degree,
--     },
--     -- hb21 : abs (α - ↑a / ↑b) ≤ A,
--     have ineq3 : abs (α - a / b) > A / b ^ f.nat_degree,
--     {
--       linarith,
--     },
--     have ineq4 : abs (α - a / b) > abs (α - a / b), {linarith}, linarith,


--     -- continuity
--     {
--       exact @polynomial.continuous_on ℝ _ (set.Icc (↑a / ↑b) α) f_ℝ,
--     },

--     -- differentiable
--     {
--       exact @polynomial.differentiable_on ℝ _ (set.Ioo (↑a / ↑b) α) f_ℝ,
--     },
--   },

--   {
--     -- α < a/b subcase
--     have H := exists_deriv_eq_slope (λ x, f_ℝ.eval x) hab3 _ _,
--     choose x0 hx0 using H,
--     have hx0l := hx0.1,
--     have hx0r := hx0.2,
--     -- clean hx0 a bit to be more usable,
--     rw [polynomial.deriv, hDf, <-hfℝ] at hx0r,
--     rw [f_eval_on_ℝ] at α_root, rw [α_root, hfℝ] at hx0r, simp at hx0r,
--     -- we have Df(x0) ≠ 0
--     have Df_x0_nonzero : Df_ℝ.eval x0 ≠ 0,
--     {
--       rw hx0r, intro rid, rw [div_eq_zero_iff] at rid,
--       rw [<-roots_def, polynomial.mem_roots, polynomial.is_root] at hab2, exact hab2 rid,
--       exact hfℝ_nonzero, linarith,
--       -- sorry,
--     },

--     have H2 : abs(α - ↑a/↑b) = abs((f_ℝ.eval (↑a/↑b)) / (Df_ℝ.eval x0)),
--     {
--       norm_num [hx0r], 
--       rw [div_div_cancel'], have : ↑a / ↑b - α = - (α - ↑a / ↑b), linarith, rw [this, abs_neg],
--       by_contra absurd, simp at absurd,
--       have H := polynomial.mem_roots _, rw polynomial.is_root at H,
--       replace H := H.2 absurd, rw roots_def at H, exact hab2 H,
--       exact hfℝ_nonzero,
--     },

--     have ineq' : polynomial.eval (↑a / ↑b) (polynomial.map ℤembℝ f) ≠ 0,
--     {
--       rw <-roots_def at hab2, intro rid, rw [hfℝ, <-polynomial.is_root, <-polynomial.mem_roots] at rid,
--       exact hab2 rid, exact hfℝ_nonzero,
--     },

--     have ineq : abs (α - ↑a / ↑b) ≥ 1/(M*b^(f.nat_degree)),
--     {
--       rw [H2, abs_div],
--       have ineq := abs_f_at_p_div_q_ge_1_div_q_pow_n f f_deg a b hb.1 ineq',
--       rw [<-hfℝ],
--       -- have ineq2 : abs (polynomial.eval (↑a / ↑b) (polynomial.map ℤembℝ f)) / abs (polynomial.eval x0 Df_ℝ) > 1 / ↑b ^ f.nat_degree / abs (polynomial.eval x0 Df_ℝ),
--       -- type_check @div_le_iff ℝ _ (abs (polynomial.eval (↑a / ↑b) (polynomial.map ℤembℝ f))) (abs (polynomial.eval x0 Df_ℝ)),
      
--       have ineq2 : abs (polynomial.eval x0 Df_ℝ) ≤ M,
--       {
--         have H := hM x0 _, exact H,
--         have h1 := hx0.1,
--         have h2 := @set.Ioo_subset_Icc_self ℝ _ (α-1) (α+1),
--         have h3 := (@set.Ioo_subset_Ioo_iff ℝ _ _ (α-1) _ (α+1) _ hab3).2 _,
--         have h4 : set.Ioo α (↑a / ↑b) ⊆ set.Icc (α-1) (α+1), exact set.subset.trans h3 h2,
--         exact set.mem_of_subset_of_mem h4 h1, split,
--         rw set.mem_Icc at hab0, linarith,
--         exact (set.mem_Icc.1 hab0).2,
--         -- sorry,
--       },
      
--       have ineq3 := small_things.a_ge_b_a_div_c_ge_b_div_c _ _ (abs (polynomial.eval x0 Df_ℝ)) ineq _ _,
--       suffices ineq4 : 1 / ↑b ^ f.nat_degree / abs (polynomial.eval x0 Df_ℝ) ≥ 1 / (M * ↑b ^ f.nat_degree),
--       {
--         have ineq : abs (polynomial.eval (↑a / ↑b) (polynomial.map ℤembℝ f)) / abs (polynomial.eval x0 Df_ℝ) ≥ 1 / (M * ↑b ^ f.nat_degree),
--         linarith,
--         exact ineq,
--       },
--       rw [div_div_eq_div_mul] at ineq3,
--       have ineq4 : 1 / (↑b ^ f.nat_degree * abs (polynomial.eval x0 Df_ℝ)) ≥ 1 / (M * ↑b ^ f.nat_degree),
--       {
--         rw [ge_iff_le, one_div_le_one_div], conv_rhs {rw mul_comm}, 
--         have ineq := ((@mul_le_mul_left ℝ _ (abs (polynomial.eval x0 Df_ℝ)) M (↑b ^ f.nat_degree)) _).2 ineq2, exact ineq,
--         replace ineq := pow_pos hb.1 f.nat_degree, norm_cast, exact ineq, have ineq' : (b:ℝ) ^ f.nat_degree > 0, norm_cast,
--         exact pow_pos hb.1 f.nat_degree, exact (mul_pos M_pos ineq'),
--         apply mul_pos, norm_cast, exact pow_pos hb.1 f.nat_degree, rw abs_pos_iff, exact Df_x0_nonzero,
--       },
--       rw div_div_eq_div_mul, exact ineq4, have ineq5 := @div_nonneg ℝ _ 1 (↑b ^ f.nat_degree) _ _, exact ineq5, norm_cast,
--       exact bot_le, norm_cast, exact pow_pos hb.1 f.nat_degree, rw [gt_iff_lt, abs_pos_iff], exact Df_x0_nonzero,
--     },

--     have ineq2 : 1/(M*b^(f.nat_degree)) > A / (b^f.nat_degree),
--     {
--       have ineq : A < B, rw [<-hA], exact @half_lt_self ℝ _ B B_pos,
--       have ineq2 : B ≤ 1/M, rw [<-hB], have H := finset.min'_le distances' hnon_empty (1/M) _, exact H,
--       rw [<-hdistances', finset.mem_insert], left, refl,
--       have ineq3 : A < 1/M, linarith,
--       rw [<-div_div_eq_div_mul], have ineq' := (@div_lt_div_right ℝ _ A (1/M) (↑b ^ f.nat_degree) _).2 ineq3,
--       rw <-gt_iff_lt at ineq', exact ineq', norm_cast, exact pow_pos hb.1 f.nat_degree,
--     },
--     -- hb21 : abs (α - ↑a / ↑b) ≤ A,
--     have ineq3 : abs (α - a / b) > A / b ^ f.nat_degree,
--     {
--       linarith,
--     },
--     have ineq4 : abs (α - a / b) > abs (α - a / b), {linarith}, linarith,


--     -- continuity
--     {
--       exact @polynomial.continuous_on ℝ _ (set.Icc α (↑a / ↑b)) f_ℝ,
--     },

--     -- differentiable
--     {
--       exact @polynomial.differentiable_on ℝ _ (set.Ioo α (↑a / ↑b)) f_ℝ,
--     },
--   },
-- done
-- end



lemma liouville_numbers_irrational: ∀ (x : real), (liouville_number x) -> irrational x :=
begin
  intros x li_x a b hb rid, replace rid : x = ↑a / ↑b, linarith,
  rw liouville_number at li_x,
  generalize hn : b.nat_abs + 1 = n,
  have b_ineq : 2 ^ (n-1) > b,
  {
    rw <-hn, simp,
    have triv : b = b.nat_abs, rw <-int.abs_eq_nat_abs, rw abs_of_pos, assumption,rw triv, simp,
    have H := @nat.lt_pow_self 2 _ b.nat_abs,  norm_cast, exact H, exact lt_add_one 1,
  },
  choose p hp using li_x n,
  choose q hq using hp, rw rid at hq,
  have q_pos : q > 0, linarith,
  rw div_sub_div at hq, swap, norm_cast, linarith, swap, norm_cast, have hq1 := hq.1, linarith,
  rw abs_div at hq,
  
  by_cases (abs ((a:ℝ) * (q:ℝ) - (b:ℝ) * (p:ℝ)) = 0),
  {
    -- aq = bp,
    rw h at hq, simp at hq, have hq1 := hq.1, have hq2 := hq.2, have hq21 := hq2.1, have hq22 := hq2.2, linarith,
  },
  {
    -- |a q - b p| ≠ 0,
    -- then |aq-bp| ≥ 1
    -- type_check @abs ℤ _,
    have ineq : ((@abs ℤ _ (a * q - b * p)):ℝ) = abs ((a:ℝ) * (q:ℝ) - (b:ℝ) * (p:ℝ)), norm_cast,
    have ineq2: (abs (a * q - b * p)) ≠ 0, by_contra rid, simp at rid, rw rid at ineq, simp at ineq, exact h (eq.symm ineq),
    have ineq2':= abs_pos_iff.2 ineq2, rw [abs_abs] at ineq2',
    replace ineq2' : 1 ≤ abs (a * q - b * p), linarith,
    have ineq3 : 1 ≤ @abs ℝ _ (a * q - b * p), norm_cast, exact ineq2',

    have eq : abs (↑b * ↑q) = (b:ℝ)*(q:ℝ), rw abs_of_pos, have eq' := mul_pos hb q_pos, norm_cast, exact eq',
    rw eq at hq,
    have ineq4 : 1 / (b * q : ℝ) ≤ (@abs ℝ _ (a * q - b * p)) / (b * q), 
    {
      rw div_le_div_iff, simp, have H := (@le_mul_iff_one_le_left ℝ _ _ (b * q) _).2 ineq3, exact H,
      norm_cast, have eq' := mul_pos hb q_pos, exact eq', norm_cast, have eq' := mul_pos hb q_pos, exact eq', norm_cast, have eq' := mul_pos hb q_pos, exact eq',
    },
    have b_ineq' := @mul_lt_mul ℤ _ b q (2^(n-1)) q b_ineq _ _ _,
    have b_ineq'' : (b * q : ℝ) < (2:ℝ) ^ (n-1) * (q : ℝ), norm_cast, simp, exact b_ineq',
    
    have q_ineq1 : q ≥ 2, linarith,
    have q_ineq2 := @pow_le_pow_of_le_left ℤ _ 2 q _ _ (n-1),
    have q_ineq3 : 2 ^ (n - 1) * q ≤ q ^ (n - 1) * q, rw (mul_le_mul_right _), assumption, linarith, 
    have triv : q ^ (n - 1) * q = q ^ n, rw <-hn, simp, rw pow_add, simp, rw triv at q_ineq3,

    have b_ineq2 : b * q < q ^ n, linarith,
    have rid' := (@one_div_lt_one_div ℝ _ (q^n) (b*q) _ _).2 _,
    have rid'' : @abs ℝ _ (a * q - b * p) / (b * q : ℝ) > 1 / q ^ n, linarith,
    have hq1 := hq.1, have hq2 := hq.2, have hq21 := hq2.1, have hq22 := hq2.2,
    linarith,

    -- other less important steps
    norm_cast, apply pow_pos, linarith,
    norm_cast, apply mul_pos, linarith, linarith,
    norm_cast, assumption,
    linarith,
    assumption,
    linarith,
    linarith,
    apply pow_nonneg, linarith,
  },
  done
  -- sorry,
end



theorem liouville_numbers_transcendental : ∀ x : real, liouville_number x -> ¬(is_algebraic ℤ x) := 
begin
  intros x li_x,
  have irr_x : irrational x, exact liouville_numbers_irrational x li_x,
  intros rid, rw is_algebraic at rid,
  choose f hf using rid,
  have f_deg : f.nat_degree > 1,
  {
    by_contra rid, simp at rid, replace rid := lt_or_eq_of_le rid, cases rid,
    {
      replace rid : f.nat_degree = 0, linarith, rw polynomial.nat_degree_eq_zero_iff_degree_le_zero at rid, rw polynomial.degree_le_zero_iff at rid,
      rw rid at hf, simp at hf, have hf1 := hf.1, have hf2 := hf.2,rw hf2 at hf1, simp at hf1, exact hf1,
    },
    {
      have f_eq : f = polynomial.C (f.coeff 0) + (polynomial.C (f.coeff 1)) * polynomial.X,
      {
        ext, by_cases (n ≤ 1),
        {
          replace h := lt_or_eq_of_le h, cases h,
          {
            replace h : n = 0, linarith, rw h, simp,
          },
          {
            rw h, simp, rw polynomial.coeff_C, split_ifs, exfalso, linarith, simp,
          },
        },
        {
          simp at h,simp, have deg : f.nat_degree < n, linarith,
          have z := polynomial.coeff_eq_zero_of_nat_degree_lt deg, rw z, rw polynomial.coeff_X,
          split_ifs, exfalso, linarith, simp, rw polynomial.coeff_C,
          split_ifs, exfalso, linarith, refl,
        }
      },

      rw f_eq at hf, simp at hf, rw irrational at irr_x,
      by_cases ((f.coeff 1) > 0),
      {
        replace irr_x := irr_x (-(f.coeff 0)) (f.coeff 1) h, simp at irr_x, rw neg_div at irr_x, rw sub_neg_eq_add at irr_x, rw add_comm at irr_x,
        suffices suff : ↑(f.coeff 0) / ↑(f.coeff 1) + x = 0, exact irr_x suff,
        rw add_eq_zero_iff_eq_neg, rw div_eq_iff, have triv : -x * ↑(f.coeff 1) = - (x * (f.coeff 1)), exact norm_num.mul_neg_pos x ↑(polynomial.coeff f 1) (x * ↑(polynomial.coeff f 1)) rfl,
        rw triv, rw <-add_eq_zero_iff_eq_neg, rw mul_comm, exact hf.2,
        intro rid',norm_cast at rid', rw <-rid at rid', rw <-polynomial.leading_coeff at rid',
        rw polynomial.leading_coeff_eq_zero at rid', rw polynomial.ext_iff at rid', simp at rid', replace rid' := rid' 1, linarith,
      },
      {
        simp at h, replace h := lt_or_eq_of_le h, cases h,
        {

         replace irr_x := irr_x (f.coeff 0) (-(f.coeff 1)) _, simp at irr_x, rw div_neg at irr_x, rw sub_neg_eq_add at irr_x, rw add_comm at irr_x,
          suffices suff : ↑(f.coeff 0) / ↑(f.coeff 1) + x = 0, exact irr_x suff,
          rw add_eq_zero_iff_eq_neg, rw div_eq_iff, have triv : -x * ↑(f.coeff 1) = - (x * (f.coeff 1)), exact norm_num.mul_neg_pos x ↑(polynomial.coeff f 1) (x * ↑(polynomial.coeff f 1)) rfl,
          rw triv, rw <-add_eq_zero_iff_eq_neg, rw mul_comm, exact hf.2,
          intro rid',norm_cast at rid', rw <-rid at rid', rw <-polynomial.leading_coeff at rid',
          rw polynomial.leading_coeff_eq_zero at rid', rw polynomial.ext_iff at rid', simp at rid', replace rid' := rid' 1, linarith, 
          linarith,
        },
        rw <-rid at h,
        rw <-polynomial.leading_coeff at h,
          rw polynomial.leading_coeff_eq_zero at h, rw h at rid, simp at rid, exact rid,
      }
    },

  },
  have about_root : f_eval_on_ℝ f x = 0,
  {
    rw f_eval_on_ℝ, have H := hf.2, rw [polynomial.aeval_def] at H,
    rw [polynomial.eval, polynomial.eval₂_map], rw [polynomial.eval₂, finsupp.sum] at H ⊢, rw [<-H, sum_eq], 
    intros m hm, simp,
  },

  choose A hA using about_irrational_root x irr_x f f_deg about_root,
  have A_pos := hA.1,
  have exists_r := small_things.pow_big_enough A A_pos,
  choose r hr using exists_r,
  have hr' : 1/(2^r) ≤ A, rw [div_le_iff, mul_comm, <-div_le_iff], exact hr, exact A_pos, apply (pow_pos _), exact two_pos,
  generalize hm : r + f.nat_degree = m, rw liouville_number at li_x,
  replace li_x := li_x m,
  choose a ha using li_x,
  choose b hb using ha,

  have ineq := hb.2.2, rw <-hm at ineq, rw pow_add at ineq,
  have eq1 := div_mul_eq_div_mul_one_div' 1 ((b:ℝ) ^ r) ((b:ℝ)^f.nat_degree), rw eq1 at ineq,
  -- since b > 1, 1/b^r ≤ 1/2^r
  have ineq2 : 1/((b:ℝ)^r) ≤ 1/((2:ℝ)^r),
  {
    apply (@one_div_le_one_div ℝ _ ((b:ℝ)^r) ((2:ℝ)^r) _ _).2,
    suffices suff : 2 ^ r ≤ b^r,  norm_cast, norm_num, exact suff,
    have ineq' := @pow_le_pow_of_le_left ℝ _ 2 b _ _ r, norm_cast at ineq', norm_num at ineq', exact ineq',
    linarith, norm_cast, linarith, norm_cast, apply pow_pos, linarith, apply pow_pos, linarith,
  },
  have ineq3 : 1 / ↑b ^ r ≤ A, exact le_trans ineq2 hr',
  have ineq4 : 1 / ↑b ^ r * (1 / ↑b ^ f.nat_degree) ≤ A * (1 / ↑b ^ f.nat_degree),
  {
    have H := (@mul_le_mul_right ℝ _ (1 / ↑b ^ r) A (1 / ↑b ^ f.nat_degree) _).2 ineq3, exact H,
    apply div_pos, linarith, norm_cast, apply pow_pos, linarith,
  },
  conv_rhs at ineq4 {
    rw <-mul_div_assoc, rw mul_one
  },
  have ineq5 :  abs (x - ↑a / ↑b) < A / ↑b ^ f.nat_degree, linarith,
  have rid := hA.2 a b _, linarith, linarith,
done
end


-- ## define an example of Liouville number Σᵢ 1/2^(i!)

-- function n -> 1/10^n! 
def ten_pow_n_fact_inverse (n : nat) : real := ((1:ℝ)/(10:ℝ))^n.fact
-- function n -> 1/2^n
def ten_pow_n_inverse (n : nat) : real := ((1:ℝ)/(10:ℝ))^n

lemma ten_pow_n_fact_inverse_ge_0 (n : nat) : ten_pow_n_fact_inverse n ≥ 0 :=
begin
    unfold ten_pow_n_fact_inverse,
    simp, have h := le_of_lt (@pow_pos _ _ (10:real) _ n.fact),
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

lemma useless_elsewhere2 : 10 ≠ 0 := by norm_num

lemma ten_pow_n_fact_inverse_le_ten_pow_n_inverse (n : nat) : ten_pow_n_fact_inverse n ≤ ten_pow_n_inverse n :=
begin
  unfold ten_pow_n_fact_inverse,
  unfold ten_pow_n_inverse, simp,
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

-- Σᵢ 1/10ⁱ exists
theorem summable_ten_pow_n_inverse : summable ten_pow_n_inverse :=
begin
  have H := @summable_geometric_of_abs_lt_1 (1/10:ℝ) _, have triv : ten_pow_n_inverse = (λ (n : ℕ), (1 / 10) ^ n), exact rfl, rw triv, exact H,
  rw abs_of_pos, linarith, linarith,
end

-- Hence Σᵢ 1/2^i! exists by comparison test
theorem summable_ten_pow_n_fact_inverse : summable ten_pow_n_fact_inverse :=
begin
  exact @summable_of_nonneg_of_le _ ten_pow_n_inverse ten_pow_n_fact_inverse ten_pow_n_fact_inverse_ge_0 ten_pow_n_fact_inverse_le_ten_pow_n_inverse summable_ten_pow_n_inverse,
end

-- define α to be Σᵢ 1/2^i!
def α := ∑' n, ten_pow_n_fact_inverse n


-- first k term
def α_k (k : ℕ) := ∑ i in finset.range (k+1), ten_pow_n_fact_inverse i

theorem α_k_rat (k:ℕ) : ∃ (p : ℕ), α_k k = (p:ℝ) / ((10:ℝ) ^ k.fact) :=
begin
  induction k with k IH, rw α_k, simp, rw ten_pow_n_fact_inverse, rw div_pow, rw one_pow, rw nat.fact_zero, rw pow_one,
  use 1, norm_cast,
  
  choose pk hk using IH,
  rw α_k at hk ⊢,
  generalize hm : 10^((k+1).fact - k.fact) = m,
  have eqm : 10^k.fact * m = 10^(k+1).fact,
  {
    rw <-hm, rw <-nat.pow_add, rw nat.add_sub_cancel', simp, rw le_mul_iff_one_le_left, exact inf_eq_left.mp rfl, exact nat.fact_pos k,
  },
  have eqm' : (10:ℝ)^k.fact * m = (10:ℝ)^(k+1).fact,
  {
    norm_cast, exact eqm,
  },
  generalize hp : pk * m + 1 = p,
  use p, rw finset.sum_range_succ, rw hk,

  rw [ten_pow_n_fact_inverse, div_pow], rw one_pow, rw nat.succ_eq_add_one,
  rw <-eqm', rw <-hp, conv_rhs {simp, rw <-div_add_div_same, simp}, rw mul_div_mul_right, simp, exact add_comm (10 ^ nat.fact k * ↑m)⁻¹ (↑pk / 10 ^ nat.fact k),
  
  intro rid, rw <-hm at rid, norm_cast at rid, have eq := @nat.pow_pos 10 _ ((k + 1).fact - k.fact), linarith, linarith,
end

-- rest term
def α_k_rest_summable (k : ℕ) := (@summable_nat_add_iff ℝ _ _ _ ten_pow_n_fact_inverse (k+1)).2 summable_ten_pow_n_fact_inverse
def α_k_rest (k : ℕ) := ∑' n, ten_pow_n_fact_inverse (n + (k+1))

private lemma sum_ge_term (f : ℕ -> ℝ) (hf : ∀ x:ℕ, f x > 0) (hf' : summable f): (∑' i, f i)  ≥ f 0 :=
begin
  rw <-(@tsum_ite_eq ℝ ℕ _ _ _ 0 (f 0)),
  generalize hfunc : (λ b' : ℕ, ite (b' = 0) (f 0) 0) = fn, simp, apply tsum_le_tsum,

  intro n, rw <-hfunc, by_cases (n=0), simp, split_ifs, exact le_of_eq (congr_arg f (eq.symm h)),
  simp, split_ifs, exact le_of_lt (hf n),
  rw <-hfunc, simp, swap, simp, assumption, rw summable, use (f 0), 
  have H := has_sum_ite_eq 0 (f 0), exact H,
end

theorem α_k_rest_pos (k : ℕ) : α_k_rest k > 0 :=
begin
  rw α_k_rest,
  generalize hfunc : (λ n:ℕ, ten_pow_n_fact_inverse (n + (k + 1))) = fn,
  have ineq1 := sum_ge_term fn _ _,
  have ineq2 : fn 0 > 0,
  {
    rw <-hfunc, simp, rw ten_pow_n_fact_inverse, rw div_pow, apply div_pos, simp, exact zero_lt_one, apply pow_pos, linarith,
  },
  exact gt_of_ge_of_gt ineq1 ineq2,

  intro n, rw <-hfunc, simp, rw ten_pow_n_fact_inverse, rw div_pow, apply div_pos, simp, exact zero_lt_one, apply pow_pos, linarith,
  rw <-hfunc, exact (@summable_nat_add_iff ℝ _ _ _ ten_pow_n_fact_inverse (k+1)).2 summable_ten_pow_n_fact_inverse,

end

theorem α_truncate_wd (k : ℕ) : α = α_k k + α_k_rest k :=
begin
  rw α, rw α_k_rest, rw α_k,
  have eq1 := @sum_add_tsum_nat_add ℝ _ _ _ _ ten_pow_n_fact_inverse (k+1) _,
  rw eq1, exact summable_ten_pow_n_fact_inverse,
end

private lemma useless3' (n: ℕ) : n.fact ≥ 1 :=
begin
  have h : n.fact > 0, exact nat.fact_pos n, exact h
end

private lemma useless3 (n : ℕ) : 2^(n.fact) > 1 :=
begin
  induction n with n h,
  simp, simp, rw nat.pow_mul, 
  have h' := @nat.lt_pow_self (2 ^ n.succ) _ n.fact,
  have ineq := useless3' n, have ineq2 : 1 < (2 ^ n.succ) ^ n.fact, exact gt_of_gt_of_ge h' ineq, exact ineq2, exact nat.one_lt_pow' n 0
  
end

-- Then α is a Liouville number hence a transcendental number.
theorem liouville_α : liouville_number α := 
begin
  intro n,

  have lemma1 := α_k_rat n,
  choose p hp using lemma1,
  use p, use 2^(n.fact),
  have lemma2 := α_truncate_wd n,
  split,
  {
    induction n with n IH, 
    simp, have ineq := useless3 n.succ, norm_cast at ineq ⊢, exact ineq,
  },
  {
    split,
    {
      rw abs_pos_iff, intro rid, simp at rid, rw sub_eq_zero at rid, rw <-hp at rid, rw rid at lemma2,
      have eq := (@add_left_eq_self ℝ _ (α_k_rest n) (α_k n)).1 _, have α_k_rest_pos := α_k_rest_pos n, linarith,
      conv_rhs {rw lemma2, rw add_comm},
    },
    {
      conv_lhs {simp [hp], rw sub_eq_add_neg, rw <-hp, rw <-sub_eq_add_neg, simp [lemma2]},
      have triv : abs (α_k_rest n) = α_k_rest n,
      {
        rw abs_of_pos, exact α_k_rest_pos n,
      },
      rw triv,
    }
  }
  -- generalize hα_fin : α_k n = αfin,
  -- use αfin.num, use αfin.denom,
  -- split, norm_cast, type_check αfin.3,
end

theorem transcendental_α : transcendental α := liouville_numbers_transcendental α liouville_α