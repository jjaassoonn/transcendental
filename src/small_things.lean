import data.rat.basic
import data.real.basic
import data.finset
import data.int.gcd
import algebra.gcd_domain
import data.polynomial
import tactic

noncomputable theory

namespace small_things

def ℤembℝ : ℤ →+* ℝ :=
begin
  constructor, swap 5, exact real.of_rat ∘ rat.of_int, norm_num,
  {
    intros m n, simp,
  },
  {
    norm_num,
  },
  intros m n, norm_num,
end


-- compute list of coeff of a polynomial
def list_coeff (f : polynomial ℤ) : (finset ℤ) := f.support.image f.to_fun

lemma coeff_in_list_coeff (f : polynomial ℤ)  (n ∈ f.support): (f.coeff n) ∈ (list_coeff f) :=
begin
    rw [list_coeff, finset.mem_image], use n,
    split, assumption, exact rfl
end

lemma not_in_support_iff_coeff_zero {α : Type} [_inst_ : comm_semiring α] (f : polynomial α) (n : ℕ): (f.coeff n) = 0 ↔ n ∉ f.support :=
begin
    split, exact finsupp.not_mem_support_iff.mpr, exact finsupp.not_mem_support_iff.mp,
end


-- f = 0 on an interval then f is zero (polynomial ℝ)

def function_ℕ_Icc (a : ℝ) : ℕ -> set.Icc (a-1) (a+1) :=
begin
    intro n,
    constructor, swap 2,
    exact (n+1)⁻¹ + a,
    split, 
    {   --type_check @le_add_right _ _ (a:ℝ),
        exact calc a - 1 ≤ a : by linarith
                  ...    ≤ a + (n+1)⁻¹ : begin norm_num, norm_cast, norm_num, end
                  ...    ≤ (n+1)⁻¹ + a : by linarith,
    },
    {
        have ineq1 : (n+1:ℝ)⁻¹ ≤ 1,
        have ineq2 := (@inv_le _ _ (n+1:ℝ) 1 _ _).2, simp at ineq2, exact ineq2,
        exact nat.cast_add_one_pos n, exact zero_lt_one, linarith,
    },
end

theorem function_ℕ_Icc_inj (a : ℝ) : function.injective $ function_ℕ_Icc a :=
begin
    intros m n hmn,
    rw [function_ℕ_Icc] at hmn, simp at hmn, exact hmn,
end

-- instance asd {a: Type} (S : set a) (hs :infinite S)

theorem inf_set_cannot_be_subset_of_fin_set {a : Type} {inst : infinite a} (S : set a) (T : set a) (hS : infinite S) (hT : set.finite T) : ¬ (S.subset T) :=
begin
    by_contra absurd,
    generalize hf : set.inclusion absurd = f,
    type_check set.finite.fintype hT,
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
        simp, exact f_zero a ha,
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
        intros a b hab, simp at hab, assumption,
    },
    exact finset.finite_to_set roots,
end

theorem zero_deriv_imp_const_poly_ℝ (f : polynomial ℝ) (h : f.derivative = 0) : f.nat_degree = 0 :=
begin
    by_cases hf : (f = 0), exact (congr_arg polynomial.nat_degree hf).trans rfl,

    rw polynomial.nat_degree_eq_zero_iff_degree_le_zero,
    by_contradiction absurd, simp at absurd,
    generalize hm : f.nat_degree - 1 = m,
    have f_nat_degree_pos : f.nat_degree > 0,
    {
        have H := polynomial.degree_eq_nat_degree hf,
        have ineq := @polynomial.degree_le_nat_degree _ _ f,
        have ineq2 := lt_of_lt_of_le absurd ineq, exact with_bot.coe_lt_coe.mp ineq2,
    },
    
    -- type_check f.coeff f.nat_degree

    rw polynomial.ext_iff at h,
    rename_var n m at h, simp at h,
    replace h := h m,
    have H2 := polynomial.coeff_derivative f m, rw h at H2,
    simp at H2, cases H2,
    {
        have hm : m + 1 = f.nat_degree,
        rw [<-hm],
        exact nat.sub_add_cancel f_nat_degree_pos,
        have H := (polynomial.coeff_derivative f m), rw h at H, simp at H,
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
    by_cases (f = 0), use 0, rw h, ext, simp,
    use f.coeff 0, ext, induction n with n hn,
    simp, have ineq : n.succ > f.nat_degree,
    { 
        suffices : n.succ > 0, rwa hf, exact nat.succ_pos n,
    },
    have zero1 : f.coeff n.succ = 0 := polynomial.coeff_eq_zero_of_nat_degree_lt ineq,
    rw zero1,
    have zero2 : (polynomial.C (f.coeff 0)).nat_degree = 0 := polynomial.nat_degree_C (f.coeff 0),
    have zero3 : (polynomial.C (f.coeff 0)).coeff n.succ = 0 := polynomial.coeff_eq_zero_of_nat_degree_lt _,
    rw zero3, rw zero2, exact nat.succ_pos n,
end


-- -- prove using induction on polynomial
-- theorem induction_on_degree {a : Type} {inst : comm_semiring a} (M : polynomial a -> Prop)
--     (deg_0 : ∀ p : polynomial a, (p.degree = 0) -> M p)
--     (inductive_hyp : ∀ n : ℕ, (∀ p : polynomial a, (p.degree ≤ n) -> M p) -> (∀ q : polynomial a, (q.degree = n.succ) -> M q)) :
--     ∀ f : polynomial a, M f :=

-- begin
--     classical,
--     -- let S be all polynomials not satisfying M,
--     generalize hS : {f : polynomial a | ¬ M f} = S,
--     suffices : S = ∅,
--     {
--         intro f, by_contra absurd, have rid : f ∈ S,
--         rw <-hS, simp, exact absurd, rw this at rid, simpa,
--     },
--     by_contra rid,
--     generalize hS_deg : S.image (λ f : polynomial a, f.degree) = S_deg,
--     -- then S_deg is non_empty
--     have S_deg_nonempty : S_deg ≠ ∅, rw [<-hS_deg],
--     {   
--         by_contra rid', simp at rid', exact rid rid',
--     },
--     replace S_deg_nonempty : S_deg.nonempty, exact set.nmem_singleton_empty.mp S_deg_nonempty,
--     -- then S_deg has min element
--     -- have H := @with_bot.well_founded_lt (with_bot ℕ) _ (<),
--     choose m hm using (@well_founded.has_min (with_bot ℕ) (<) (with_bot.well_founded_lt nat.lt_wf) S_deg S_deg_nonempty),
--     have hm1 := hm.1, have hm2 := hm.2,
--     rw [<-hS_deg, set.mem_image] at hm1,
--     choose f hf using hm1,
--     have M_g : ∀ g : polynomial a, (g.degree) < m -> M g, {
--         by_contra rid, simp at rid,
--         choose g hg using rid,
--         have rid' : g.degree ∈ S_deg, rw [<-hS_deg, set.mem_image],
--         use g, simp, rw [<-hS], simp, exact hg.2,
--         replace rid' := hm2 g.degree rid',
--         exact rid' hg.1,
--     },


-- end



namespace gcd_int

theorem int_gcd_nat_gcd (m n : ℤ) : m.gcd n = nat.gcd (m.nat_abs) (n.nat_abs) :=
begin
    rw int.gcd,
end

-- compute gcd(z1, z2) as an element in ℤ
def gcd_int_int_int (z1 z2 : ℤ) : ℤ := int.of_nat $ int.gcd z1 z2


-- gcd(z1,z2) = gcd(z2,z2)
-- gcd(gcd(z1,z2),z3) = gcd(z1, gcd(z2,z3))
instance gcd_int_int_int_comm' : is_commutative ℤ gcd_int_int_int := 
begin
    exact gcd_domain.gcd.is_commutative,
end

theorem gcd_int_int_int_comm (m n : ℤ) : gcd_int_int_int m n = gcd_int_int_int n m :=
begin
    exact gcd_comm m n
end

instance gcd_int_int_int_asso' : is_associative ℤ gcd_int_int_int :=
begin
    exact gcd_domain.gcd.is_associative,
end

theorem gcd_int_int_int_assoc (z1 z2 z3 : ℤ) : gcd_int_int_int (gcd_int_int_int z1 z2) z3 = gcd_int_int_int z1 (gcd_int_int_int z2 z3) :=
begin
    exact gcd_assoc z1 z2 z3
end

#reduce gcd_int_int_int 0 (-5)
#reduce @abs ℤ _ (-1)
@[simp] theorem gcd_int_int_int_0_n (n : ℤ) : gcd_int_int_int 0 n = abs n :=
begin
    rw [gcd_int_int_int, int.gcd_zero_left], simp, rw int.abs_eq_nat_abs,
end


@[simp] theorem gcd_int_int_int_abs_n_n (n : ℤ) : gcd_int_int_int (abs n) n = (abs n) :=
begin
    rw [gcd_int_int_int, int.gcd_eq_left, int.abs_eq_nat_abs], exact rfl, 
    apply int.dvd_of_mod_eq_zero, rw [int.mod_abs], exact int.mod_self,
end

#reduce gcd_int_int_int (gcd_int_int_int (-3: int) 6) (-3 : int)
-- set_option trace.simplify true
@[simp] theorem gcd_int_int_int_idem (m n : ℤ) :
    gcd_int_int_int (gcd_int_int_int m n) n = gcd_int_int_int m n :=
begin
    by_cases (m = 0); rename h hm; by_cases (n = 0); rename h hn,
    rwa [hm, hn], exact rfl, rw hm, simp,
    rw [hn, gcd_int_int_int_comm, gcd_int_int_int_0_n, gcd_int_int_int_comm, gcd_int_int_int_0_n], exact abs_abs m, 
    rw [gcd_int_int_int, gcd_int_int_int],
    suffices h : (int.of_nat (m.gcd n)).gcd n = (m.gcd n), exact congr_arg int.of_nat h,
    rw [int_gcd_nat_gcd, int_gcd_nat_gcd], simp,
end

def gcd_of_list (S : finset ℤ) : ℤ := finset.fold gcd_int_int_int 1 id S

private theorem gcd_of_insert_a_S_1 (S : finset ℤ) (a : ℤ) (h : a ∉ S) : 
    gcd_of_list (insert a S) = gcd_int_int_int (gcd_of_list S) a :=
begin
    rw [gcd_of_list, finset.fold_insert, <-gcd_of_list], exact gcd_comm (id a) (gcd_of_list S), exact h,
end

-- set_option trace.simplify true
private theorem gcd_of_insert_a_S_2 (S : finset ℤ): ∀ a ∈ S, 
    gcd_of_list S = gcd_int_int_int (gcd_of_list S) a :=
begin
    apply finset.induction_on S,
    {
        intros a h, simp at h, exfalso, exact h,
    },
    {
        intros a S ha ih t ht, rename_var a b at ih, rw finset.mem_insert at ht,
        cases ht,
        {
            rw [ht, gcd_of_insert_a_S_1, gcd_int_int_int_idem], exact ha,

        },
        {
            have Ht := ih t ht,
            rw [gcd_of_list, finset.fold_insert, <-gcd_of_list], simp, 
            conv_rhs {
                rw [(gcd_int_int_int_assoc), Ht, gcd_int_int_int_idem, <-Ht],
            }, exact ha,
        }
    }
end

@[simp] theorem gcd_of_insert_a_S (S : finset ℤ) (a : ℤ) : gcd_of_list (insert a S) = gcd_int_int_int (gcd_of_list S) a :=
begin
    by_cases (a ∉ S), exact gcd_of_insert_a_S_1 S a h, simp at h,
    rw [finset.insert_eq_of_mem],
    exact gcd_of_insert_a_S_2 S a h, assumption,
end

#reduce gcd_of_list ∅
theorem gcd_of_list_dvd_mem_of_list (S : finset ℤ) : ∀ (s ∈ S), gcd_of_list S ∣ s :=
begin
    apply finset.induction_on S,
    {
        intros s hs, exact false.rec (gcd_of_list ∅ ∣ s) hs,
    },
    {
        intros t T ht ih s hs, rename_var s t at ih,
        rw finset.mem_insert at hs,
        cases hs,
        {
            rw [hs, gcd_of_list, finset.fold_insert, <-gcd_of_list, id], exact int.gcd_dvd_left t (gcd_of_list T),
            assumption,
        },
        {
            have Hs := ih s hs,
            rw [gcd_of_list, finset.fold_insert, <-gcd_of_list, id],
            have H : gcd_int_int_int t (gcd_of_list T) ∣ (gcd_of_list T),
            exact int.gcd_dvd_right t (gcd_of_list T), exact dvd.trans H (ih s hs), assumption,
        }
    }
end

theorem gcd_of_list_non_zero (S : finset ℤ) : gcd_of_list S ≠ 0 :=
begin
    apply finset.induction_on S,
    exact ne_of_gt trivial,
    intros s T hs ih,
    rw [gcd_of_list, finset.fold_insert, id, <-gcd_of_list], 
    intro absurd, rw [gcd_int_int_int, <-int.of_nat_zero] at absurd,
    replace absurd := (@int.of_nat_inj (s.gcd (gcd_of_list T)) 0) absurd,
    rw [int.gcd_eq_zero_iff] at absurd, exact ih absurd.2, assumption,
end
end gcd_int

end small_things