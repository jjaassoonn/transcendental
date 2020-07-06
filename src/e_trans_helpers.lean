import ring_theory.algebraic
import algebra.big_operators
import measure_theory.set_integral
import analysis.special_functions.exp_log
import small_things

noncomputable theory
open_locale classical
open small_things
open_locale big_operators

theorem same_sum {s : finset ℕ} (f g : ℕ -> ℝ) (h : ∀ i ∈ s, f i = g i) : (∑ i in s, f i) = ∑ i in s, g i :=
begin
exact finset.sum_congr rfl h,
end


-- derivative n times
def deriv_n (f : polynomial ℤ) (n : ℕ) : polynomial ℤ := polynomial.derivative ^[n] f

lemma deriv_zero (f : polynomial ℤ) : deriv_n f 0 = f :=
begin
    rw deriv_n, simp only [id.def, function.iterate_zero],
end

lemma deriv_succ (f : polynomial ℤ) (n : ℕ) : (deriv_n f n).derivative = (deriv_n f (n+1)) :=
begin
    rw deriv_n, rw deriv_n, rw function.iterate_succ',
end

lemma deriv_zero_p (n : ℕ) : deriv_n 0 n = 0 :=
begin
    induction n with n hn; simp only [deriv_n, id.def, function.iterate_zero], rw <-deriv_n, assumption,
end


lemma deriv_n_coeff (f : polynomial ℤ) (k : ℕ) : ∀ n : ℕ, (deriv_n f k).coeff n = (∏ i in finset.range k, (n+k-i)) * (f.coeff (n+k)) :=
begin
    induction k with k ih, simp only [add_zero, nat.nat_zero_eq_zero, one_mul, finset.range_zero, finset.prod_empty], rw deriv_n, simp only [forall_const, id.def, eq_self_iff_true, function.iterate_zero], intro m,
    rw deriv_n, rw function.iterate_succ', simp only [function.comp_app, int.coe_nat_succ], rw <-deriv_n, rw polynomial.coeff_derivative, rw ih (m+1),
    rw finset.prod_range_succ, simp only [int.coe_nat_succ, int.nat_cast_eq_coe_nat], 
    have triv : (∏ (x : ℕ) in finset.range k, ((m:ℤ) + 1 + ↑k - ↑x)) = ∏ (x : ℕ) in finset.range k, (↑m + (↑k + 1) - ↑x),
    {
        apply congr_arg, ext, simp only [sub_left_inj], ring,
    }, rw triv,
    replace triv : (m + 1 : ℤ) = (m + (k+1) - k:ℤ),
    {
        rw add_sub_assoc, simp only [add_sub_cancel'],
    }, rw triv,
    replace triv : f.coeff (m + 1 + k) = f.coeff (m + k.succ),
    {
        rw nat.succ_eq_add_one, ring,
    },
    rw triv, ring,
end

lemma deriv_n_add (p q :polynomial ℤ) (n : ℕ) : (deriv_n (p+q) n) = (deriv_n p n) + (deriv_n q n) :=
begin
    induction n with n ih, rw[deriv_n, deriv_n, deriv_n], simp only [id.def, function.iterate_zero],
    rw [deriv_n, deriv_n, deriv_n, function.iterate_succ'], simp only [function.comp_app], rw [<-deriv_n,<-deriv_n,<-deriv_n, ih], simp only [polynomial.derivative_add], 
end

private lemma deriv_too_much (a : ℤ) : (deriv_n (polynomial.C a) ((polynomial.C a).nat_degree + 1)) = 0 :=
begin
    rw deriv_n, dsimp, rw polynomial.derivative_C, simp only [ring_hom.eq_int_cast, id.def, polynomial.nat_degree_int_cast, function.iterate_zero],
end

theorem deriv_too_much (f : polynomial ℤ): (deriv_n f (f.nat_degree + 1)) = 0 :=
begin
    ext, rw deriv_n_coeff, simp only [int.coe_nat_succ, polynomial.coeff_zero, mul_eq_zero], right,
    apply polynomial.coeff_eq_zero_of_nat_degree_lt, linarith,
end

def I (f : polynomial ℤ) (t : ℝ) (ht : t ≥ 0) : ℝ := 
    t.exp * (∑ i in finset.range f.nat_degree.succ, (f_eval_on_ℝ (deriv_n f i) 0)) - (∑ i in finset.range f.nat_degree.succ, (f_eval_on_ℝ (deriv_n f i) t))

def II (f : polynomial ℤ) (t : ℝ) (ht : t ≥ 0) : ℝ := ∫ x in set.Icc 0 t, real.exp(t - x) * (f_eval_on_ℝ f x)

theorem II_0 (t : ℝ) (ht : t ≥ 0) : II 0 t ht = 0 :=
begin
    -- have triv : 0 = (∫ x in set.Icc (0:real) t, (0:ℝ)),
    rw II, unfold f_eval_on_ℝ, simp only [set.indicator_zero, measure_theory.integral_zero, mul_zero, polynomial.eval_zero, polynomial.map_zero],
end

--- I should assume they are "nice".
axiom ftc (f: ℝ -> ℝ) (a b : ℝ) (h : b ≥ a) :  (∫ x in set.Icc a b, (deriv f) x) = f b - f a
axiom integrate_by_part (f g : ℝ -> ℝ) (a b : ℝ) (h : b ≥ a) :
    (∫ x in set.Icc a b, (f x)*(deriv g x)) = (f b) * (g b) - (f a) * (g a) - (∫ x in set.Icc a b, (deriv f x) * (g x))
axiom integral_le_integral' (f g : ℝ -> ℝ) (a b : ℝ) (h : b ≥ a) (hf : ∀ x ∈ set.Icc a b, f x ≤ g x ∧ 0 ≤ f x) : (∫ x in set.Icc a b, f x) ≤ (∫ x in set.Icc a b, g x)


theorem integral_neg' {S : set ℝ} (f : ℝ -> ℝ) : (∫ x in S, -f x) = - ∫ x in S, f x :=
begin
    exact integral_on_neg S (λ (a : ℝ), f a),
end

theorem integral_constant (a b : ℝ) (h : b ≥ a) (c : ℝ): (∫ x in set.Icc a b, c) = (b - a) * c :=
begin
    have eq1 : (∫ x in set.Icc a b, c) = (∫ x in set.Icc a b, (deriv (λ y, c * y)) x),
    {
        apply congr_arg, apply congr_arg, ext, simp only [differentiable_at_const, mul_one, deriv_mul, differentiable_at_id', zero_mul, deriv_id'', deriv_const', zero_add],
    },
    rw eq1,
    rw (ftc (λ (y : ℝ), c * y) a b h), simp only [], ring,
end

theorem integral_le_max_times_length (f : ℝ -> ℝ) (a b : ℝ) (h : b ≥ a) (c : ℝ) 
    (f_nonneg : ∀ x ∈ set.Icc a b, f x ≥ 0) (c_max : ∀ x ∈ set.Icc a b, f x ≤ c) : 
    (∫ x in set.Icc a b, f x) ≤ (b - a) * c :=
begin
    have ineq1 : (∫ x in set.Icc a b, f x) ≤ (∫ x in set.Icc a b, c),
    {
        apply integral_le_integral', exact h, intros x hx, exact ⟨c_max x hx, f_nonneg x hx⟩,
    },
    rw integral_constant at ineq1, assumption, assumption,
end

-- axiom deriv_derivative

theorem deriv_exp_t_x (t : ℝ) : deriv (λ x, real.exp (t-x)) = -(λ x, real.exp (t-x)) :=
begin
    have triv : (λ x, real.exp (t-x)) = real.exp ∘ (λ x, t - x),
    {
        ext, simp only [],
    },
    ext,
    rw triv,
    have eq := @deriv.scomp ℝ _ ℝ _ _ real.exp x (λ x, t - x) _ _,
    rw eq, rw deriv_exp, simp only [neg_mul_eq_neg_mul_symm, differentiable_at_const, mul_one, algebra.id.smul_eq_mul, one_mul, zero_sub, deriv_sub,
 differentiable_at_id', pi.neg_apply, deriv_id'', deriv_const'],
    {
        simp only [differentiable_at_id'],
    },
    {
        simp only [differentiable_at_id', differentiable_at.exp],
    },
    apply differentiable_at.const_sub,
    exact differentiable_at_id,
end

theorem deriv_exp_t_x' (t : ℝ) : (deriv (λ x, - (real.exp (t-x)))) = (λ x, real.exp (t-x)) := 
begin
 simp only [deriv_exp_t_x, deriv_neg', pi.neg_apply, neg_neg],
end


theorem same_integral {S : set ℝ} (f g : ℝ -> ℝ) : f = g -> (∫ x in S, f x) = ∫ x in S, g x :=
begin
 intro h,
 simp only [], exact congr_arg measure_theory.integral (congr_arg (set.indicator S) h)
end

theorem same_integral' (f g : ℝ -> ℝ) : f = g -> (∫ x, f x) = ∫ x, g x :=
begin
 intro h,
 exact congr_arg measure_theory.integral h
end

theorem same_deriv (f g : ℝ -> ℝ) (x : ℝ) : f = g -> deriv f x = deriv g x :=
begin
    intro h, exact congr_fun (congr_arg deriv h) x,
end

theorem II_integrate_by_part (f : polynomial ℤ) (t : ℝ) (ht : t ≥ 0) : 
    (II f t ht) = (real.exp t) * (f_eval_on_ℝ f 0) - (f_eval_on_ℝ f t) + (II f.derivative t ht) :=
begin
    rw II, -- have eq := (deriv_exp_t_x' t),
    have eq : (∫ x in set.Icc 0 t, (t - x).exp * f_eval_on_ℝ f x) = (∫ x in set.Icc 0 t, f_eval_on_ℝ f x * (deriv (λ x, - (real.exp (t-x))) x)),
    {
        apply same_integral, ext, simp only [deriv_exp_t_x'], ring,
    },
    rw eq,
    replace eq := integrate_by_part (f_eval_on_ℝ f) (λ (x : ℝ), -(t - x).exp) 0 t ht,
    rw eq, simp only [mul_one, neg_sub_neg, real.exp_zero, sub_zero, mul_neg_eq_neg_mul_symm, sub_self],
    replace eq : (∫ x in set.Icc 0 t, -(deriv (f_eval_on_ℝ f) x * (t - x).exp)) = ∫ x in set.Icc 0 t, -((λ x, (deriv (f_eval_on_ℝ f) x * (t - x).exp)) x),
    {
        apply same_integral, ext, simp only [],
    }, 
    rw eq, rw integral_neg', simp only [sub_neg_eq_add], rw II,
    replace eq : (∫ (x : ℝ) in set.Icc 0 t, (t - x).exp * f_eval_on_ℝ f.derivative x) = ∫ (x : ℝ) in set.Icc 0 t, deriv (f_eval_on_ℝ f) x * (t - x).exp,
    {
        apply same_integral, ext, ring, rw f_eval_on_ℝ,
        have triv : (polynomial.map ℤembℝ f.derivative) = (polynomial.map ℤembℝ f).derivative,
        {
            ext, rw polynomial.coeff_derivative, rw polynomial.coeff_map, rw polynomial.coeff_derivative, rw polynomial.coeff_map,
            simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, int.cast_mul, int.cast_one, int.nat_cast_eq_coe_nat],
        },
        rw triv, rw <-polynomial.deriv,replace triv : deriv (λ (x : ℝ), polynomial.eval x (polynomial.map ℤembℝ f)) x = deriv (f_eval_on_ℝ f) x,
        {
            apply same_deriv, ext, rw f_eval_on_ℝ,
        },
        rw triv, ring,
    }, rw eq, ring,
end

theorem II_integrate_by_part_m (f : polynomial ℤ) (t : ℝ) (ht : t ≥ 0) (m : ℕ) :
    II f t ht = t.exp * (∑ i in finset.range (m+1), (f_eval_on_ℝ (deriv_n f i) 0)) - (∑ i in finset.range (m+1), f_eval_on_ℝ (deriv_n f i) t) + (II (deriv_n f (m+1)) t ht) :=
begin
    induction m with m ih,
    rw deriv_n, simp only [function.iterate_one, finset.sum_singleton, finset.range_one], rw II_integrate_by_part, rw deriv_n, simp only [id.def, function.iterate_zero],

    rw ih,
    have triv : m.succ + 1 = (m+1).succ := by ring, rw triv, generalize hM : m + 1 = M,
    rw II_integrate_by_part,
    replace triv : t.exp * ∑ (i : ℕ) in finset.range M, f_eval_on_ℝ (deriv_n f i) 0 -
        ∑ (i : ℕ) in finset.range M, f_eval_on_ℝ (deriv_n f i) t +
      (t.exp * f_eval_on_ℝ (deriv_n f M) 0 - f_eval_on_ℝ (deriv_n f M) t + II (deriv_n f M).derivative t ht)
      = t.exp * ((∑ (i : ℕ) in finset.range M, f_eval_on_ℝ (deriv_n f i) 0) + (f_eval_on_ℝ (deriv_n f M) 0))
      - ((∑ (i : ℕ) in finset.range M, f_eval_on_ℝ (deriv_n f i) t) + f_eval_on_ℝ (deriv_n f M) t) + II (deriv_n f M).derivative t ht,
    {
        ring,
    },
    rw triv,
    replace triv : ∑ (i : ℕ) in finset.range M, f_eval_on_ℝ (deriv_n f i) 0 + f_eval_on_ℝ (deriv_n f M) 0 = ∑ (i : ℕ) in finset.range M.succ, f_eval_on_ℝ (deriv_n f i) 0,
    {
        rw finset.sum_range_succ, ring,
    },
    rw triv,
    replace triv : (∑ (i : ℕ) in finset.range M, f_eval_on_ℝ (deriv_n f i) t + f_eval_on_ℝ (deriv_n f M) t) = (∑ (i : ℕ) in finset.range M.succ, f_eval_on_ℝ (deriv_n f i) t),
    {
        rw finset.sum_range_succ, ring,
    },
    rw triv,
    replace triv : (deriv_n f M).derivative= (deriv_n f M.succ),
    {
        conv_rhs {rw deriv_n}, rw function.iterate_succ', replace triv : (polynomial.derivative ∘ (polynomial.derivative^[M])) f = (polynomial.derivative (polynomial.derivative^[M] f)) := rfl,
        rw triv, rw <-deriv_n,
    },
    rw triv,
end


theorem II_eq_I (f : polynomial ℤ) (t : ℝ) (ht : t ≥ 0) : II f t ht = I f t ht :=
begin
    have II_integrate_by_part_m := II_integrate_by_part_m f t ht f.nat_degree,
    have triv := deriv_too_much f, rw triv at II_integrate_by_part_m, rw II_0 at II_integrate_by_part_m, simp only [add_zero] at II_integrate_by_part_m,
    rw I, assumption,
end

private lemma norm_indicator {a b : ℝ} {h : a ≤ b} (f : ℝ -> ℝ) (x : ℝ) : ∥ set.indicator (set.Icc a b) f x ∥ = (set.indicator (set.Icc a b) (λ y, ∥ f y ∥)) x :=
begin
    conv_rhs {rw [set.indicator_apply],}, split_ifs,
    rw set.indicator_apply, simp only [h_1, if_true],
    rw set.indicator_apply, simp only [h_1, norm_zero, if_false],
end

theorem abs_II_le1 (f : polynomial ℤ) (t : ℝ) (ht : t ≥ 0) : abs (II f t ht) ≤ ∫ x in set.Icc 0 t, abs ((t-x).exp * (f_eval_on_ℝ f x)) :=
begin
    have triv : (∫ x in set.Icc 0 t, abs ((t-x).exp * (f_eval_on_ℝ f x))) = ∫ x in set.Icc 0 t, ∥(t-x).exp * (f_eval_on_ℝ f x)∥,
    {
        apply same_integral, ext, exact rfl,
    }, rw triv,

    replace triv : abs (II f t ht) = ∥ (∫ (x : ℝ) in set.Icc 0 t, (t - x).exp * f_eval_on_ℝ f x) ∥,
    {
        exact rfl,
    }, rw triv,
    have ineq := @measure_theory.norm_integral_le_integral_norm ℝ _ ℝ _ _ _ _ _ _  (set.indicator (set.Icc 0 t) (λ x, (t - x).exp * f_eval_on_ℝ f x)),
    simp only [] at ineq,

    replace triv : (∫ (a : ℝ), ∥(set.Icc 0 t).indicator (λ (x : ℝ), (t - x).exp * f_eval_on_ℝ f x) a∥) =
                   ∫ (a : ℝ), (set.Icc 0 t).indicator (λ (x : ℝ), ∥ (t - x).exp * f_eval_on_ℝ f x ∥) a,
    {
        apply same_integral', ext, rw norm_indicator, exact ht,
    }, rw triv at ineq, exact ineq,

end

def f_bar (f : polynomial ℤ) : polynomial ℤ :=
begin
    constructor, swap 2, exact f.1, swap 2, intro n, exact abs (f.coeff n), intro n,
    split,
    {
        intro hn, simp only [abs_eq_zero, ne.def], have h := (f.3 n).1 hn, simp only [ne.def] at h, assumption,
    },
    {
        intro hn, simp only [abs_eq_zero, ne.def] at hn, apply (f.3 n).2, simpa only [],
    },
end

theorem bar_coeff (f : polynomial ℤ) (n : ℕ) : (f_bar f).coeff n = abs (f.coeff n) :=
begin
    by_cases (n ∈ f.1), have triv : (f_bar f).coeff n = (f_bar f).to_fun n := rfl,
    rw triv, rw f_bar,

    exact rfl,
end

theorem bar_supp (f : polynomial ℤ) : (f_bar f).1 = f.1 :=
begin
    split,
end

theorem bar_same_deg (f : polynomial ℤ) : (f_bar f).nat_degree = f.nat_degree :=
begin
    apply polynomial.nat_degree_eq_of_degree_eq,
    rw polynomial.degree, rw polynomial.degree, rw bar_supp,
end


theorem f_bar_0 : f_bar 0 = 0 :=
begin
    ext, rw bar_coeff, simp only [abs_zero, polynomial.coeff_zero],
end

theorem f_bar_eq_0 (f : polynomial ℤ) : f_bar f = 0 -> f = 0 :=
begin
    intro h, rw polynomial.ext_iff at h, ext,
    have hn := h n, simp only [polynomial.coeff_zero] at hn, rw bar_coeff at hn, simp only [abs_eq_zero, polynomial.coeff_zero] at hn ⊢, assumption,
end

private lemma coeff_sum (f : ℕ -> polynomial ℤ) (m : ℕ) (s : finset ℕ) : (∑ i in s, (f i).coeff m) = (∑ i in s, f i).coeff m :=
begin
    apply finset.induction_on s, simp only [finset.sum_empty, polynomial.coeff_zero],
    intros a s ha, simp only [forall_prop_of_true, polynomial.finset_sum_coeff],
end

theorem f_bar_eq (f : polynomial ℤ) : f_bar f = ∑ i in finset.range f.nat_degree.succ, polynomial.C (abs (f.coeff i)) * polynomial.X^i :=
begin
    ext, rw bar_coeff, rw <-coeff_sum, 
    have eq1 : ∑ (i : ℕ) in finset.range f.nat_degree.succ, (polynomial.C (abs (f.coeff i)) * polynomial.X ^ i).coeff n =
               ∑ (i : ℕ) in finset.range f.nat_degree.succ, ite (n = i) (abs (f.coeff i)) 0 := finset.sum_congr rfl (λ _ _, by rw polynomial.coeff_C_mul_X),
    rw [eq1], rw finset.sum_ite_eq, split_ifs, refl, replace h : n ≥ f.nat_degree.succ, simp only [not_lt, finset.mem_range] at h, exact h, replace h : n > f.nat_degree, exact h,
    rw polynomial.coeff_eq_zero_of_nat_degree_lt h, exact rfl,
end

theorem coeff_f_bar_mul (f g : polynomial ℤ) (n : ℕ) : (f_bar (f*g)).coeff n = abs(∑ p in finset.nat.antidiagonal n, (f.coeff p.1)*(g.coeff p.2)) :=
begin
    rw bar_coeff (f*g) n, rw polynomial.coeff_mul,
end

theorem f_bar_ineq (f : polynomial ℤ) (t : ℝ) (ht : t ≥ 0) : ∀ x ∈ set.Icc 0 t, abs (f_eval_on_ℝ f x) ≤ f_eval_on_ℝ (f_bar f) t :=
begin
    intros x hx,
    have lhs : f_eval_on_ℝ f x = ∑ i in f.support, (f.coeff i : ℝ) * x ^ i,
    {
        rw [f_eval_on_ℝ, polynomial.eval_map, polynomial.eval₂, finsupp.sum],
        apply congr_arg, ext, norm_cast,
    },
    rw lhs,
    have ineq1 : abs (∑ (i : ℕ) in f.support, (f.coeff i:ℝ) * x ^ i) ≤ ∑ i in f.support, (abs (f.coeff i:ℝ) * (x ^ i)),
    {
        have ineq1' := @finset.abs_sum_le_sum_abs ℝ ℕ _ (λ i, (f.coeff i:ℝ) * (x ^ i)) f.support, simp only [] at ineq1',
        have eq1 : ∑ (x_1 : ℕ) in f.support, abs (↑(f.coeff x_1) * x ^ x_1) = ∑ (x_1 : ℕ) in f.support, abs (↑(f.coeff x_1)) * x ^ x_1,
        {
            apply congr_arg, ext, rw abs_mul,
            rw @abs_of_nonneg ℝ _ (x^x_1) _, apply pow_nonneg, exact (set.mem_Icc.1 hx).1,
        },
        rw eq1 at ineq1', exact ineq1',
    },

    have rhs : f_eval_on_ℝ (f_bar f) t = ∑ i in (f_bar f).support, abs (f.coeff i:ℝ) * t ^ i,
    {
        rw [f_eval_on_ℝ, polynomial.eval_map, polynomial.eval₂, finsupp.sum],
        apply congr_arg, ext, norm_cast,
    },
    rw rhs,

    have ineq2 : ∑ (i : ℕ) in f.support, abs ↑(f.coeff i) * x ^ i ≤  ∑ i in (f_bar f).support, abs (f.coeff i:ℝ) * t ^ i,
    {
        rw bar_supp, apply finset.sum_le_sum, intros n hn,
        suffices : x ^ n ≤ t ^ n,
        {
            apply mul_le_mul, exact le_refl (abs ↑(polynomial.coeff f n)), exact this, apply pow_nonneg, exact (set.mem_Icc.1 hx).1, exact abs_nonneg ↑(polynomial.coeff f n),
        },
        apply pow_le_pow_of_le_left, exact (set.mem_Icc.1 hx).1, exact (set.mem_Icc.1 hx).2,
    },
    exact le_trans ineq1 ineq2,
end

private lemma II_le2' (f : polynomial ℤ) (t : ℝ) (ht : t ≥ 0) : (∫ x in set.Icc 0 t, abs ((t-x).exp * (f_eval_on_ℝ f x))) ≤ t * t.exp * (f_eval_on_ℝ (f_bar f) t) :=
begin
    have ineq1 := integral_le_max_times_length (λ x, abs ((t - x).exp * f_eval_on_ℝ f x)) 0 t ht (t.exp * f_eval_on_ℝ (f_bar f) t) _ _,
    simp only [sub_zero] at ineq1, 
    have triv : t * (t.exp * f_eval_on_ℝ (f_bar f) t) = t * t.exp * f_eval_on_ℝ (f_bar f) t := by ring,
    rw triv at ineq1, assumption,

    {
        intros x hx, simp only [ge_iff_le], exact abs_nonneg ((t - x).exp * f_eval_on_ℝ f x),
    },

    {
        intros x hx, simp only [], rw abs_mul,
        have triv : abs (t - x).exp = (t-x).exp, {
            apply abs_of_pos, exact (t - x).exp_pos,
        },
        rw triv,
        have ineq1 := f_bar_ineq f t ht x hx,
        have ineq2 : (t - x).exp ≤ t.exp,
        {
            rw real.exp_le_exp, rw sub_le, simp only [sub_self], exact hx.1,
        },
        have ineq3 : (t - x).exp * abs (f_eval_on_ℝ f x) ≤ t.exp * abs (f_eval_on_ℝ f x),
        {
            apply mul_le_mul, assumption, exact le_refl (abs (f_eval_on_ℝ f x)), exact abs_nonneg (f_eval_on_ℝ f x),
            exact le_of_lt (real.exp_pos t),
        },
        have ineq4 : t.exp * abs (f_eval_on_ℝ f x) ≤ t.exp * f_eval_on_ℝ (f_bar f) t,
        {
            apply mul_le_mul, exact le_refl (real.exp t), assumption, exact abs_nonneg (f_eval_on_ℝ f x), exact le_of_lt (real.exp_pos t),
        },
        exact le_trans ineq3 ineq4,
    },
end

theorem abs_II_le2 (f : polynomial ℤ) (t : ℝ) (ht : t ≥ 0) : abs (II f t ht) ≤ t * t.exp * (f_eval_on_ℝ (f_bar f) t) :=
begin
    exact le_trans (abs_II_le1 f t ht) (II_le2' f t ht),
end

------ about differentiation

private lemma nat_sub_eq (n i : ℕ) (h : i + 1 ≤ n) : (n - (i + 1) + 1) = n - i :=
begin
    have triv : n - (i+1) = n - i - 1, exact rfl,
    rw triv, apply nat.sub_add_cancel, exact nat.le_sub_left_of_add_le h,
end

private lemma nat_choose_eq (n k : ℕ) : (n.choose (k+1)) + (n.choose k) = (n+1).choose (k+1) :=
begin
    exact add_comm (nat.choose n (k + 1)) (nat.choose n k),
end


theorem deriv_n_poly_prod (p q : polynomial ℤ) (n : ℕ) : deriv_n (p * q) n = ∑ k in finset.range n.succ, (polynomial.C (n.choose k:ℤ)) * (deriv_n p (n-k)) * (deriv_n q k) :=
begin
    induction n with n IH,
    simp only [deriv_zero, nat.choose_self, int.cast_coe_nat, ring_hom.eq_int_cast, one_mul, nat.cast_one, finset.sum_singleton,
 finset.range_one],

    {
        rw deriv_n, rw function.iterate_succ', dsimp, rw <-deriv_n,
        rw IH, simp only [polynomial.derivative_sum, polynomial.derivative_mul, zero_mul, polynomial.derivative_C, zero_add,
 polynomial.derivative_sum, polynomial.derivative_mul, zero_mul, polynomial.derivative_C, zero_add], rw finset.sum_add_distrib,
        conv_lhs {rw finset.sum_range_succ', rw finset.sum_range_succ, simp only [deriv_zero, nat.choose_self, one_mul, nat.choose_zero_right, int.coe_nat_zero, nat.sub_self, polynomial.C_1,
 int.coe_nat_succ, nat.sub_zero, zero_add]},
        have eq1 :
        ∑ (i : ℕ) in finset.range n,
          polynomial.C (n.choose (i + 1):ℤ) * (deriv_n p (n - (i + 1))).derivative * deriv_n q (i + 1) +
        (deriv_n p n).derivative * q +
        (p * (deriv_n q n).derivative +
         ∑ (x : ℕ) in finset.range n, polynomial.C (n.choose x:ℤ) * deriv_n p (n - x) * (deriv_n q x).derivative) = 
        (∑ (i : ℕ) in finset.range n,
          polynomial.C (n.choose (i + 1):ℤ) * (deriv_n p (n - (i + 1))).derivative * deriv_n q (i + 1)) +
        (∑ (x : ℕ) in finset.range n, polynomial.C (n.choose x:ℤ) * deriv_n p (n - x) * (deriv_n q x).derivative) +
        ((deriv_n p n).derivative * q + (p * (deriv_n q n).derivative)),
        {
            ring,
        },
        rw eq1,
        rw <-finset.sum_add_distrib,

        
        replace eq :
        (∑ (x : ℕ) in finset.range n,
        (polynomial.C (n.choose (x + 1):ℤ) * (deriv_n p (n - (x + 1))).derivative * deriv_n q (x + 1) +
           polynomial.C (n.choose x:ℤ) * deriv_n p (n - x) * (deriv_n q x).derivative)) =
        (∑ (x : ℕ) in finset.range n,
        (polynomial.C (n.choose (x + 1):ℤ) * (deriv_n p (n - x)) * deriv_n q (x + 1) +
           polynomial.C (n.choose x:ℤ) * deriv_n p (n - x) * (deriv_n q (x+1)))),
        {
            apply finset.sum_congr, exact rfl, intros i hi, simp only [deriv_succ, int.cast_coe_nat, ring_hom.eq_int_cast, add_left_inj], simp only [finset.mem_range] at hi,
            replace hi : i + 1 ≤ n,
            {
                exact hi,
            },
            rw nat_sub_eq, exact hi,
        }, rw eq,

        replace eq :
        (∑ (x : ℕ) in finset.range n,
        (polynomial.C (n.choose (x + 1):ℤ) * (deriv_n p (n - x)) * deriv_n q (x + 1) +
           polynomial.C (n.choose x:ℤ) * deriv_n p (n - x) * (deriv_n q (x+1)))) =
        (∑ (x : ℕ) in finset.range n,
        ((polynomial.C (n.choose (x + 1):ℤ) + polynomial.C (n.choose x:ℤ)) * (deriv_n p (n - x)) * deriv_n q (x + 1))),
        {
            apply congr_arg, rw function.funext_iff, intro i, ring,
        }, rw eq,

        replace eq :
        (∑ (x : ℕ) in finset.range n,
        ((polynomial.C (n.choose (x + 1):ℤ) + polynomial.C (n.choose x:ℤ)) * (deriv_n p (n - x)) * deriv_n q (x + 1))) =
        (∑ (x : ℕ) in finset.range n,
        ((polynomial.C (n.choose (x + 1) + (n.choose x):ℤ)) * (deriv_n p (n - x)) * deriv_n q (x + 1))),
        {
            apply congr_arg, rw function.funext_iff, intro i, simp only [int.cast_add, ring_hom.eq_int_cast],
        }, rw eq,

        replace eq :
        (∑ (x : ℕ) in finset.range n,
        ((polynomial.C (n.choose (x + 1) + (n.choose x):ℤ)) * (deriv_n p (n - x)) * deriv_n q (x + 1))) =
        (∑ (x : ℕ) in finset.range n,
        ((polynomial.C ((n+1).choose (x + 1):ℤ)) * (deriv_n p (n - x)) * deriv_n q (x + 1))),
        {
            apply congr_arg, rw function.funext_iff, intro i, rw <-nat_choose_eq, simp only [int.coe_nat_add],
        }, rw eq,

        conv_rhs {rw finset.sum_range_succ', rw finset.sum_range_succ}, simp only [deriv_succ, deriv_zero, nat.succ_eq_add_one, nat.choose_self, int.cast_coe_nat, ring_hom.eq_int_cast, one_mul,
 nat.succ_sub_succ_eq_sub, nat.choose_zero_right, int.coe_nat_zero, nat.sub_self, int.cast_one, int.coe_nat_succ,
 nat.sub_zero, zero_add], ring,
    }
end


theorem poly_pow_deriv (f : polynomial ℤ) (n : ℕ) (hn : n > 0) : (f ^ n).derivative = (polynomial.C (n:ℤ)) * (f ^ (n-1)) * f.derivative :=
begin
    induction n with n IH, simp only [polynomial.derivative_one, int.coe_nat_zero, zero_mul, polynomial.C_0, pow_zero],
    {
        cases n, simp only [ring_hom.eq_int_cast, one_mul, int.coe_nat_zero, int.cast_one, int.coe_nat_succ, pow_one, zero_add, pow_zero],
        replace IH := IH _,
        rw nat.succ_eq_add_one, rw pow_add, simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, polynomial.derivative_mul, int.cast_one, nat.succ_add_sub_one,
 int.coe_nat_succ, pow_one], rw IH, simp only [nat.succ_sub_succ_eq_sub, polynomial.C_add, polynomial.C_1, int.coe_nat_succ, nat.sub_zero, nat.succ_sub_succ_eq_sub,
 int.coe_nat_succ, nat.sub_zero],
        have eq1 : (polynomial.C ↑n + 1) * f ^ n * f.derivative * f = (polynomial.C ↑n + 1) * f ^ (n+1) * f.derivative,
        {
            rw pow_add, simp only [int.cast_coe_nat, ring_hom.eq_int_cast, pow_one], ring,
        } ,
        rw eq1, rw nat.succ_eq_add_one, repeat {rw add_mul}, simp only [int.cast_coe_nat, ring_hom.eq_int_cast, one_mul], exact nat.succ_pos n,
    }
end
