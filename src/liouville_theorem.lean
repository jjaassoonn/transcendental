import data.rat.basic
import data.real.basic
import ring_theory.algebraic
import field_theory.minimal_polynomial
import tactic.linarith
import tactic
import topology.metric_space.basic
import topology.basic
import topology.algebra.polynomial
import analysis.normed_space.basic analysis.specific_limits
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


lemma about_irrational_root (α : real) (hα : irrational α) (f : polynomial ℤ) 
  (f_nonzero : f ≠ 0) (α_root : f_eval_on_ℝ f α = 0) :
  ∃ A : real, ∀ a b : int, b > 0 -> abs(α - a / b) > (A / b ^ (f.nat_degree)) :=
begin
  generalize hfℝ: f.map ℤembℝ = f_ℝ,
   generalize hDf: f_ℝ.derivative = Df_ℝ,
  have H := compact.exists_forall_ge (@compact_Icc (α-1) (α+1)) _ (abs_f_eval_around_α_continuous Df_ℝ α),
  choose x0 hx0 using H,
  generalize M_def: abs (Df_ℝ.eval x0) = M,
  have hM := hx0.2, rw M_def at hM,
  have M_non_zero : M ≠ 0,
  {
    by_contra absurd,
    simp at absurd, rw absurd at hM,
    replace hM : ∀ (y : ℝ), y ∈ set.Icc (α - 1) (α + 1) → (polynomial.eval y Df_ℝ) = 0,
    {
      intros y hy,
      have H := hM y hy, simp at H, rw H,
    },
    replace hM : Df_ℝ = 0,
    {
      exact f_zero_on_interval_f_zero Df_ℝ hM,
    },
    rename hM Df_ℝ_zero,
    have f_ℝ_0 : f_ℝ.nat_degree = 0,
    {
      have H := small_things.zero_deriv_imp_const_poly_ℝ f_ℝ _, exact H,
      rw [<-hDf] at Df_ℝ_zero, assumption,
    },
    replace f_ℝ_0 := small_things.degree_0_constant f_ℝ f_ℝ_0,
    choose c hc using f_ℝ_0,
    -- f = c constant
    -- c is nonzero
    by_cases absurd2 : (c = 0),
    -- if c is zero contradiction to f_nonzero
    {
      rw absurd2 at hc,
      have f_zero : f = 0,
      {
        ext,
        have f_ℝ_n : f_ℝ.coeff n = 0, 
        have H := @polynomial.coeff_map _ _ _ f _ ℤembℝ n,
        rw [hfℝ, hc] at H, simp at H, rw [<-hfℝ, @polynomial.coeff_map _ _ _ f _ ℤembℝ n], simp [H], simp,

      }
    }
  },
  generalize roots_def :  f_ℝ.roots = f_roots,
  generalize roots_distance_to_α : f_roots.image (λ x, abs (α - x)) = distances,
  generalize hdistances' : insert (1/M) (insert (1:ℝ) distances) = distances',
  have hnon_empty: distances'.nonempty,
  {
    rw <-hdistances',
    rw [finset.nonempty], use (1/M), simp,
  },
  -- generalize hA : distances.min = A',
  -- have A_is_some : ∃ A ∈ ℝ, A' = @option.some ℝ A,
  generalize hA : finset.min' distances' hnon_empty = A,
  have allpos : ∀ x : ℝ, x ∈ distances' -> x > 0,
  {
    intros x hx, rw [<-hdistances', finset.mem_insert, finset.mem_insert] at hx,
    cases hx,
    {
      -- 1 / M
      rw hx, simp,
    }
  },
  have A_pos : A > 0,
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
    --div_le_self

  }

  -- type_check compact_Icc

  -- -- we can assume f has leading coeff > 0
  -- by_cases ((f.coeff (f.nat_degree) > 0) ∧ gcd_int.gcd_of_list (list_coeff f) = 1), 
  -- -- if f has positive leading term and coeffs are coprime the previous lemma will do
  -- exact about_irrational_root_f_leading_term_pos_all_coeffs_coprime α hα f f_nonzero h.1 h.2 α_root,

  -- -- if f has negative leading term, then multiply -1
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

lemma neg_f_f_have_same_nat_deg (f : polynomial ℤ) (n : ℕ) : f.nat_degree = (-f).nat_degree :=
begin
  rw [polynomial.nat_degree, polynomial.nat_degree],
end


#reduce (1: int) / (2 : int)

lemma about_irrational_root_f_leading_term_pos_all_coeffs_coprime_trivial_subcase
  (α : real) (hα : irrational α) (f : polynomial ℤ) 
  (f_nonzero : f ≠ 0)
  (f_leading_term_pos : f.coeff (f.nat_degree) > 0)
  (f_coeffs_coprime : gcd_int.gcd_of_list (list_coeff f) = 1)
  (α_root : (f.map ℤembℝ).eval α = 0) :
  ∀ a b : ℤ, b > 0 -> abs(α - a / b) ≥ 1 -> abs(α - a / b) > (1 / b ^ (f.nat_degree)) := 
begin
  intros a b hb h,
  sorry
end

lemma about_irrational_root_f_leading_term_pos_all_coeffs_coprime
  (α : real) (hα : irrational α) (f : polynomial ℤ) 
  (f_nonzero : f ≠ 0)
  (f_leading_term_pos : f.coeff (f.nat_degree) > 0)
  (f_coeffs_coprime : gcd_int.gcd_of_list (list_coeff f) = 1)
  (α_root : (f.map ℤembℝ).eval α = 0) :
  ∃ A : real, ∀ a b : ℤ, b > 0 -> abs(α - a / b) > (A / b ^ (f.nat_degree)) := 

begin

end

#check rat.of_int

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
        simp [nat.succ_mul, nat.mul_succ, nat.succ_eq_add_one] at hm ⊢, linarith,
    },
    exact H' n,
end

lemma useless_elsewhere2 : 2 ≠ 0 := by norm_num

lemma two_pow_n_fact_inverse_le_two_pow_n_inverse (n : nat) : two_pow_n_fact_inverse n ≤ two_pow_n_inverse n :=
begin
  unfold two_pow_n_fact_inverse,
  unfold two_pow_n_inverse,
  have h := @pow_le_pow_of_le_one _ _ (2:real)⁻¹ _ _ n n.fact _,
  norm_cast at h ⊢, simp, rw pow_inv, rw pow_inv, exact h, norm_num, norm_num, norm_num, norm_num,
  exact useless_elsewhere n,
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

