import data.rat.basic
import data.real.basic
import ring_theory.algebraic
import field_theory.minimal_polynomial
import tactic.linarith
import tactic
import topology.metric_space.basic
import analysis.normed_space.basic analysis.specific_limits

noncomputable theory
local attribute [instance] classical.prop_decidable

def transcendental (x : real) := ¬(is_algebraic rat x)

def liouville_number (x : real) := ∀ n : nat, ∃ a b : int, b ≥ 1 ∧ 0 < abs(x - a / b) ∧ abs(x - a / b) < 1/b^n


def irrational (x : real) := ∀ a b : int, b > 0 -> x - a / b ≠ 0

#check metric.compact_iff_closed_bounded

example (a : real) : compact $ set.Icc (a-1) (a+1) :=
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

#check rat.of_int
lemma about_irrational_root (α : real) (hα : irrational α) (f : polynomial ℤ) 
  (f_nonzero : f ≠ 0) (α_root : (polynomial.map (real.of_rat ∘ rat.of_int) f).eval α = 0) :
  ∃ A : real, ∀ a b : int, b > 0 -> abs(α - a / b) > (A / b ^ (f.nat_degree)) :=
begin
  generalize hDf: f.derivative = Df,
  
end

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

