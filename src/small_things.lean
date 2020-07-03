import data.rat.basic
import data.real.basic
import data.finset
import data.int.gcd
import algebra.gcd_domain
import data.finsupp algebra.big_operators
import data.polynomial
import tactic

noncomputable theory

namespace small_things

def ℤembℝ : ℤ →+* ℝ :=
{ to_fun :=real.of_rat ∘ rat.of_int,
  map_one' := by norm_num,
  map_zero' := by norm_num,
  map_add' := λ m n, by norm_num,
  map_mul' := λ m n, by norm_num}

theorem ℤembℝ_inj : function.injective ℤembℝ := λ a b h, by {simp only [ring_hom.eq_int_cast, int.cast_inj] at h, exact h,}
theorem ℤembℝ_zero : ℤembℝ 0 = 0 := by exact ℤembℝ.map_zero

-- compute list of coeff of a polynomial
def list_coeff (f : polynomial ℤ) : (finset ℤ) := f.support.image f.to_fun

lemma coeff_in_list_coeff (f : polynomial ℤ)  (n ∈ f.support): (f.coeff n) ∈ (list_coeff f) :=
begin
    rw [list_coeff, finset.mem_image], use n,
    split, assumption, exact rfl,
end

lemma not_in_support_iff_coeff_zero {α : Type} [_inst_ : comm_semiring α] (f : polynomial α) (n : ℕ): (f.coeff n) = 0 ↔ n ∉ f.support :=
begin
    split, exact finsupp.not_mem_support_iff.mpr, exact finsupp.not_mem_support_iff.mp,
end


-- f = 0 on an interval then f is zero (polynomial ℝ)

def function_ℕ_Icc (a : ℝ) : ℕ -> set.Icc (a-1) (a+1) := λ n,
⟨(n+1)⁻¹ + a, 
 ⟨calc a - 1 ≤ a : by linarith
      ...    ≤ a + (n+1)⁻¹ : begin norm_num, norm_cast, norm_num, end
      ...    ≤ (n+1)⁻¹ + a : by linarith,
    begin
        have ineq1 : (n+1:ℝ)⁻¹ ≤ 1,
        have ineq2 := (@inv_le _ _ (n+1:ℝ) 1 _ _).2, simp only [forall_prop_of_true, inv_one', le_add_iff_nonneg_left, nat.cast_nonneg] at ineq2, exact ineq2,
        exact nat.cast_add_one_pos n, exact zero_lt_one, linarith,
    end⟩⟩

theorem function_ℕ_Icc_inj (a : ℝ) : function.injective $ function_ℕ_Icc a :=
begin
    intros m n hmn,
    rw [function_ℕ_Icc] at hmn, simp only [add_left_inj, inv_inj'', subtype.mk_eq_mk, nat.cast_inj] at hmn, exact hmn,
end

theorem inf_set_cannot_be_subset_of_fin_set {a : Type} {inst : infinite a} (S : set a) (T : set a) (hS : infinite S) (hT : set.finite T) : ¬ (S.subset T) :=
begin
    by_contra absurd,
    generalize hf : set.inclusion absurd = f,
    have absurd2 := @not_injective_infinite_fintype ↥S _ _ (set.finite.fintype hT) f,
    rw <-hf at absurd2,
    have contra := set.inclusion_injective absurd, simpa,
end

theorem f_zero_on_interval_f_zero {a : ℝ} (f : polynomial ℝ) (f_zero: ∀ x : ℝ, x ∈ (set.Icc (a-1) (a+1)) -> f.eval x = 0) : f = 0 :=
begin
    by_contra absurd,
    choose roots hroots using polynomial.exists_finset_roots absurd,
    have absurd2 : (set.Icc (a-1) (a+1)).subset ↑roots,
    {
        rw set.subset, intros a ha, apply (hroots.2 a).2,
        simp only [polynomial.is_root.def], exact f_zero a ha,
    },
    have inf : infinite (set.Icc (a-1) (a+1)),
    {
        exact infinite.of_injective (function_ℕ_Icc a) (function_ℕ_Icc_inj a),
    },

    have inf2 := @infinite.of_injective _ _ inf (set.inclusion absurd2) (set.inclusion_injective absurd2),
    have absurd3 := inf_set_cannot_be_subset_of_fin_set (set.Icc (a-1) (a+1)) (↑roots) inf _,
    exact absurd (false.rec (f = 0) (absurd3 absurd2)),
    {
        apply infinite.of_injective (λ n : ℕ, (n : ℝ)),
        intros a b hab, simp only [nat.cast_inj] at hab, assumption,
    },
    exact finset.finite_to_set roots,
end

theorem zero_deriv_imp_const_poly_ℝ (f : polynomial ℝ) (h : f.derivative = 0) : f.nat_degree = 0 :=
begin
    by_cases hf : (f = 0), exact (congr_arg polynomial.nat_degree hf).trans rfl,

    rw polynomial.nat_degree_eq_zero_iff_degree_le_zero,
    by_contradiction absurd, simp only [not_le] at absurd,
    generalize hm : f.nat_degree - 1 = m,
    have f_nat_degree_pos : f.nat_degree > 0,
    {
        have H := polynomial.degree_eq_nat_degree hf,
        have ineq := @polynomial.degree_le_nat_degree _ _ f,
        have ineq2 := lt_of_lt_of_le absurd ineq, exact with_bot.coe_lt_coe.mp ineq2,
    },
    
    rw polynomial.ext_iff at h,
    rename_var n m at h, simp only [polynomial.coeff_zero] at h,
    replace h := h m,
    have H2 := polynomial.coeff_derivative f m, rw h at H2,
    simp only [zero_eq_mul] at H2, cases H2,
    {
        have hm : m + 1 = f.nat_degree,
        rw [<-hm],
        exact nat.sub_add_cancel f_nat_degree_pos,
        have H := (polynomial.coeff_derivative f m), rw h at H, simp only [zero_eq_mul] at H,
        cases H, rw hm at H,
        have H2 := @polynomial.leading_coeff_eq_zero _ _ f,
        rw [polynomial.leading_coeff] at H2,
        exact hf (H2.1 H),
        have ineq := nat.cast_add_one_pos m,
        rw H at ineq, linarith,
    },
    {
        have ineq := nat.cast_add_one_pos m, rw H2 at ineq, linarith,
    },
    done
end

theorem degree_0_constant {α : Type} {inst : comm_semiring α} (f : polynomial α) (hf : f.nat_degree = 0) :
    ∃ a : α, f = (polynomial.C a) :=

begin
    classical,
    by_cases (f = 0), use 0, rw h, ext, simp only [polynomial.C_0],
    use f.coeff 0, ext, induction n with n hn,
    simp only [polynomial.coeff_C_zero], have ineq : n.succ > f.nat_degree,
    { 
        suffices : n.succ > 0, rwa hf, exact nat.succ_pos n,
    },
    have zero1 : f.coeff n.succ = 0 := polynomial.coeff_eq_zero_of_nat_degree_lt ineq, rw zero1,
    have zero2 : (polynomial.C (f.coeff 0)).nat_degree = 0 := polynomial.nat_degree_C (f.coeff 0),
    have zero3 : (polynomial.C (f.coeff 0)).coeff n.succ = 0 := polynomial.coeff_eq_zero_of_nat_degree_lt _,
    rw zero3, rw zero2, exact nat.succ_pos n,
end

-- power manipulation
@[simp] theorem triv (r : ℝ) (hr : r ≠ 0) (n : ℕ) : r ^ n = r ^ (n : ℤ) := by norm_num

-- inequality
lemma a_ge_b_a_div_c_ge_b_div_c (a b c : ℝ) (hab : a ≥ b) (b_nonneg : b ≥ 0) (hc : c > 0) : a / c ≥ b / c :=
begin
    apply div_le_div; linarith,
end

-- archmedian-like
theorem pow_big_enough (A : ℝ) (A_pos : A > 0) : ∃ r : nat, 1/A ≤ 2 ^ r :=
begin
    have H := @pow_unbounded_of_one_lt ℝ _ _ (1/A) 2 _,
    choose n hn using H,
    use n, exact le_of_lt hn, exact lt_add_one 1,
end

end small_things
