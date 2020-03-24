import data.rat.basic
import data.real.basic
import ring_theory.algebraic
import field_theory.minimal_polynomial
import tactic.linarith
import tactic
import analysis.normed_space.basic analysis.specific_limits

noncomputable theory
local attribute [instance] classical.prop_decidable

def transcendental (x : real) := ¬(is_algebraic rat x)

def liouville_number (x : real) := ∀ n : nat, ∃ a b : int, b ≥ 1 ∧ 0 < abs(x - a / b) ∧ abs(x - a / b) < 1/b^n


-- This is should be the hardest part

theorem liouville_numbers_transcendental : ∀ x : real, liouville_number x -> ¬(is_algebraic rat x) := sorry

def two_pow_n_fact_inverse (n : nat) : real := (1/2)^n.fact
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

theorem summable_two_pow_n_inverse : summable two_pow_n_inverse :=
begin
  exact summable_geometric_two,
end

theorem summable_two_pow_n_fact_inverse : summable two_pow_n_fact_inverse :=
begin
  exact @summable_of_nonneg_of_le _ two_pow_n_inverse two_pow_n_fact_inverse two_pow_n_fact_inverse_ge_0 two_pow_n_fact_inverse_le_two_pow_n_inverse summable_two_pow_n_inverse,
end

def α := classical.some summable_two_pow_n_fact_inverse

theorem liouville_α : liouville_number α :=
begin
  intro n,
  sorry
end

theorem transcendental_α : transcendental α := liouville_numbers_transcendental α liouville_α

