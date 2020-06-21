import data.real.basic
import data.complex.exponential
import ring_theory.algebraic
import e_trans_helpers

noncomputable theory
local attribute [instance] classical.prop_decidable

open small_things

open_locale big_operators

def e : ℝ := real.exp 1

section e

private lemma nonneg_nat (i : ℕ) : (i : ℝ) ≥ 0 :=
begin
  norm_cast, exact bot_le,
end

theorem prod_deg (s : ℕ) (f : ℕ -> polynomial ℤ) (hf : ∀ i ∈ finset.range s, f i ≠ 0) : (∏ i in finset.range s, f i).nat_degree = ∑ i in finset.range s, (f i).nat_degree :=
begin
  induction s with s ih,
  simp,

  rw finset.sum_range_succ, rw finset.prod_range_succ,
  have triv : (∀ (i : ℕ), i ∈ finset.range s → f i ≠ 0),
  {
    intros i hi, apply hf, simp at hi ⊢, exact nat.lt.step hi,
  },
  replace ih := ih triv, rw <-ih, apply polynomial.nat_degree_mul_eq,
  apply hf, simp,
  intro rid, rw [finset.prod_eq_zero_iff] at rid,
  choose a ha using rid,
  refine hf a _ ha.2, simp at ha ⊢, exact nat.lt.step ha.left,
end

def f_p (p : ℕ) (hp : nat.prime p) (n : ℕ): polynomial ℤ := polynomial.X ^ (p - 1) * (∏ i in finset.range n, (polynomial.X - (polynomial.C (i+1:ℤ)))^p)


theorem f_eval_on_ℝ_add (f g : polynomial ℤ) (t : ℝ) : f_eval_on_ℝ (f + g) t = (f_eval_on_ℝ f t) + (f_eval_on_ℝ g t) :=
begin
  simp [f_eval_on_ℝ],
end

theorem f_eval_on_ℝ_sum (s : finset ℕ) (f : ℕ -> polynomial ℤ) (t : ℝ) : f_eval_on_ℝ (∑ i in s, f i) t = ∑ i in s, f_eval_on_ℝ (f i) t :=
begin
  apply finset.induction_on s, simp [f_eval_on_ℝ],
  intros n s hn ih, rw finset.sum_insert, rw f_eval_on_ℝ_add, rw ih, rw finset.sum_insert, assumption, assumption,
end

theorem f_eval_on_ℝ_mul (f g : polynomial ℤ) (t : ℝ) : f_eval_on_ℝ (f * g) t = (f_eval_on_ℝ f t) * (f_eval_on_ℝ g t) :=
begin
  simp [f_eval_on_ℝ],
end

theorem f_eval_on_ℝ_prod (s : finset ℕ) (f : ℕ -> polynomial ℤ) (t : ℝ) : f_eval_on_ℝ (∏ i in s, f i) t = ∏ i in s, f_eval_on_ℝ (f i) t :=
begin
  apply finset.induction_on s, simp [f_eval_on_ℝ], intros n s hn ih, rw finset.prod_insert, rw f_eval_on_ℝ_mul, rw ih, rw finset.prod_insert, assumption, assumption,
end

theorem deg_f_p (p : ℕ) (hp : nat.prime p) (n : ℕ) : (f_p p hp n).nat_degree = (n+1)*p - 1 :=
begin
  rw f_p,
  have eq1 := @polynomial.nat_degree_mul_eq ℤ _ (polynomial.X ^ (p - 1)) (∏ i in finset.range n, (polynomial.X - (polynomial.C (i+1:ℤ)))^p) _ _,
  
  rw eq1,
  have triv : (polynomial.X : polynomial ℤ).degree = 1,
  {
    simp,
  },
  replace triv : polynomial.X.nat_degree = 1,
  {
    have triv' : ↑polynomial.X.nat_degree = polynomial.X.degree,  
    { 
      apply eq.symm,
      apply polynomial.degree_eq_nat_degree, intro rid, rw rid at triv, simp at triv, exact option.not_mem_none 1 triv,
    },
    rw triv at triv', 
    rw polynomial.nat_degree, rw triv, exact rfl,
  }, simp,
  rw triv, simp,

  have triv' : (∏ (i : ℕ) in finset.range n, (polynomial.X - polynomial.C (i+1:ℤ)) ^ p).nat_degree 
              = ∑ i in finset.range n, ((polynomial.X - polynomial.C (i+1:ℤ)) ^ p).nat_degree,
  {
    apply prod_deg, 
    intros i hi, intro rid, 
    replace rid := @pow_eq_zero (polynomial ℤ) _ (polynomial.X - polynomial.C (i+1:ℤ)) p rid,
    rw sub_eq_zero_iff_eq at rid,
    have rid' : (polynomial.C (i+1:ℤ)).nat_degree = 1,
    rw <-rid, exact triv, have rid'' := polynomial.nat_degree_C (i+1:ℤ), rw rid' at rid'', linarith,
  }, simp at triv',
  rw triv',
  have triv'' : (∑ (x : ℕ) in finset.range n, p * (polynomial.X - (polynomial.C ↑x + 1)).nat_degree) = ∑ x in finset.range n, p,
  {
    apply congr_arg, ext, rename x i,
    have eq1 : (polynomial.X - (polynomial.C (i:ℤ) + 1)) =  (polynomial.X - (polynomial.C (i + 1:ℤ))),
    {
      simp,
    },
    rw eq1,
    have deg1 : (polynomial.X - polynomial.C (i + 1:ℤ)).degree = 1,
    {
      apply polynomial.degree_X_sub_C,
    },
    have deg2 : (polynomial.X - polynomial.C (i + 1:ℤ)).nat_degree = 1,
    {
      rw polynomial.nat_degree, rw deg1, exact rfl,
    },
    rw deg2, rw mul_one,
  },
  rw triv'', rw finset.sum_const, simp, ring, have eq2 := (@nat.add_sub_assoc p 1 _ (p*n)),
  rw eq2, rw add_comm,
  linarith [((@nat.prime_def_lt p).1 hp).1],

  {
    intro rid, replace rid := pow_eq_zero rid, exact polynomial.X_ne_zero rid,
  },

  {
    intro rid, rw finset.prod_eq_zero_iff at rid,
    choose i hi using rid,
    have hi1 := hi.1, have hi2 := hi.2, replace hi2 := pow_eq_zero hi2,
    have deg1 := polynomial.degree_X_sub_C (i+1:ℤ), rw hi2 at deg1, simp at deg1,
    have triv := @ne_bot_of_gt ℕ _ 0 1 _, exact option.not_mem_none 1 deg1, exact lt_add_one 0,
  }
end


def J (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) : ℝ := 
  ∑ i in finset.range g.nat_degree.succ, (g.coeff i : ℝ) * (II (f_p p hp g.nat_degree) i (nonneg_nat i))

private lemma J_eq1 (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) : 
  (J g p hp) = ∑ i in finset.range g.nat_degree.succ, (g.coeff i:ℝ) * (I (f_p p hp g.nat_degree) i (nonneg_nat i)) :=

begin
  rw J, apply congr_arg, ext,
  rw II_eq_I,
end


private lemma J_eq2 (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) :
  (∑ i in finset.range g.nat_degree.succ, (g.coeff i:ℝ) * (I (f_p p hp g.nat_degree) i (nonneg_nat i))) =
   (∑ k in finset.range g.nat_degree.succ, (g.coeff k:ℝ) * ((k:ℝ).exp * (∑ j in finset.range (f_p p hp g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p hp g.nat_degree) j) 0)))
  -(∑ k in finset.range g.nat_degree.succ, (g.coeff k:ℝ) * (∑ j in finset.range (f_p p hp g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p hp g.nat_degree) j) (k:ℝ))))) :=

begin
  rw <-finset.sum_sub_distrib, apply congr_arg, ext, rename x i,  rw <-mul_sub, rw <-I,
end

private lemma mul_eq_mul' (a b c d : ℝ) : a = c -> b = d -> a * b = c * d :=
begin
  intros h1 h2, simp [h1, h2],
end

private lemma J_eq3 (g : polynomial ℤ) (e_root_g : (polynomial.aeval ℤ ℝ e) g = 0) (p : ℕ) (hp : nat.prime p):
  (∑ k in finset.range g.nat_degree.succ, (g.coeff k:ℝ) * ((k:ℝ).exp * (∑ j in finset.range (f_p p hp g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p hp g.nat_degree) j) 0)))) = 0 :=
begin
  have eq1 : 
    (∑ k in finset.range g.nat_degree.succ, (g.coeff k:ℝ) * ((k:ℝ).exp * (∑ j in finset.range (f_p p hp g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p hp g.nat_degree) j) 0)))) =
    ∑ k in finset.range g.nat_degree.succ, ((g.coeff k:ℝ) * (k:ℝ).exp) * (∑ j in finset.range (f_p p hp g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p hp g.nat_degree) j) 0)),
    {
      apply congr_arg, ext, rename x i, ring,
    },
  rw eq1,
  rw <-finset.sum_mul,
  have eq2 : (∑ x in g.support, (g.coeff x:ℝ) * (x:ℝ).exp) = (∑ (x : ℕ) in finset.range g.nat_degree.succ, (g.coeff x:ℝ) * (x:ℝ).exp),
  {
    apply finset.sum_subset, intros i hi,
    simp, suffices : i ≤ g.nat_degree, {exact nat.lt_succ_iff.mpr this}, apply polynomial.le_nat_degree_of_ne_zero,
    have triv := (g.3 i).1 hi, exact triv,
    intros i hi Hi, rw mul_eq_zero, left, norm_cast, by_contra, exact Hi ((g.3 i).2 a),
  },
  rw <-eq2,

  have eq3 : (∑ x in g.support, (g.coeff x:ℝ) * (x:ℝ).exp) = (polynomial.aeval ℤ ℝ e) g,
  {
    rw polynomial.aeval_def, rw polynomial.eval₂, rw finsupp.sum, apply congr_arg, ext, simp, rw e,
    apply mul_eq_mul', norm_cast,

    induction x with x IH, simp,
    rw nat.succ_eq_add_one, simp, rw real.exp_add, rw IH, ring,
  }, rw eq3, rw e_root_g, rw zero_mul,
end

theorem J_eq (g : polynomial ℤ) (e_root_g : (polynomial.aeval ℤ ℝ e) g = 0) 
             (p : ℕ) (hp : nat.prime p) : 
  (J g p hp) = - ∑ k in finset.range g.nat_degree.succ,
                (∑ j in finset.range (f_p p hp g.nat_degree).nat_degree.succ,
                  (g.coeff k : ℝ) * (f_eval_on_ℝ (deriv_n (f_p p hp g.nat_degree) j) (k:ℝ))) :=

begin
  rw J_eq1, rw J_eq2, rw J_eq3, simp, apply congr_arg, ext, rw finset.mul_sum, assumption,
end


theorem sum_swap_index (s1 s2 : finset ℕ) (g : ℕ -> ℕ -> ℝ) : ∑ i in s1, (∑ j in s2, g i j) = ∑ j in s2, (∑ i in s1, g i j) :=
begin
  exact finset.sum_comm,
end

theorem J_eq' (g : polynomial ℤ) (e_root_g : (polynomial.aeval ℤ ℝ e) g = 0) 
              (p : ℕ) (hp : nat.prime p) : 
  (J g p hp) = - ∑ j in finset.range (f_p p hp g.nat_degree).nat_degree.succ,
                (∑ k in finset.range g.nat_degree.succ,
                  (g.coeff k : ℝ) * (f_eval_on_ℝ (deriv_n (f_p p hp g.nat_degree) j) (k:ℝ))) :=
begin
  rw J_eq,
  exact congr_arg has_neg.neg (sum_swap_index (finset.range g.nat_degree.succ) (finset.range (f_p p hp g.nat_degree).nat_degree.succ)
     (λ (i j : ℕ), ↑(g.coeff i) * f_eval_on_ℝ (deriv_n (f_p p hp g.nat_degree) j) ↑i)), assumption,
end

private lemma f_eval_on_ℝ_nat (f : polynomial ℤ) (k : ℕ) : (f_eval_on_ℝ f (k:ℝ)) = ℤembℝ (polynomial.eval k f) :=
begin
  apply polynomial.induction_on f,
  {
    intro a, simp [f_eval_on_ℝ],
  },
  {
    intros p q hp hq,
    simp [f_eval_on_ℝ_add, hp, hq],
  },
  {
    intros m a ha, simp [f_eval_on_ℝ_mul,f_eval_on_ℝ] at ha ⊢,
  },
end

lemma coe_J (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) :
    ∑ j in finset.range (f_p p hp g.nat_degree).nat_degree.succ,
      (∑ k in finset.range g.nat_degree.succ,
        (g.coeff k : ℝ) * (f_eval_on_ℝ (deriv_n (f_p p hp g.nat_degree) j) (k:ℝ))) =
    ℤembℝ (∑ j in finset.range (f_p p hp g.nat_degree).nat_degree.succ,
            (∑ k in finset.range g.nat_degree.succ,
              (g.coeff k) * (polynomial.eval (k:ℤ) (deriv_n (f_p p hp g.nat_degree) j)))) :=
begin
  rw ring_hom.map_sum, apply finset.sum_congr, exact rfl,
  intros i hi, rw ring_hom.map_sum, apply finset.sum_congr, refl,
  intros j hj, rw ring_hom.map_mul, simp, apply mul_eq_mul', exact rfl, rw f_eval_on_ℝ_nat, simp,
end

theorem J_eq'' (g : polynomial ℤ) (e_root_g : (polynomial.aeval ℤ ℝ e) g = 0) 
              (p : ℕ) (hp : nat.prime p) : 
  (J g p hp) =  - ℤembℝ (∑ j in finset.range (f_p p hp g.nat_degree).nat_degree.succ,
            (∑ k in finset.range g.nat_degree.succ,
              (g.coeff k) * (polynomial.eval (k:ℤ) (deriv_n (f_p p hp g.nat_degree) j)))) :=
begin
  rw J_eq', rw neg_eq_iff_neg_eq, rw neg_neg, rw <-coe_J, assumption,
end

theorem eval_sum' (s : finset ℕ) (f : ℕ -> polynomial ℤ) (t : ℤ) : polynomial.eval t (∑ i in s, f i) = ∑ i in s, polynomial.eval t (f i) :=
begin
  apply finset.induction_on s, simp,
  intros a s ha ih, rw finset.sum_insert, rw polynomial.eval_add, rw ih, rw finset.sum_insert, exact ha, exact ha,
end

theorem eval_prod' (s : finset ℕ) (f : ℕ -> polynomial ℤ) (t : ℤ) : polynomial.eval t (∏ i in s, f i) = ∏ i in s, polynomial.eval t (f i) :=
begin
  apply finset.induction_on s, simp,
  intros a s ha ih, rw finset.prod_insert, rw polynomial.eval_mul, rw ih, rw finset.prod_insert, exact ha, exact ha,
end

-- private theorem deriv_X_2_0 : deriv_n (polynomial.X^2) 0 = (polynomial.X)^2 := 
-- begin
--   simp [deriv_zero],
-- end

-- private theorem deriv_X_2_1 : deriv_n ((polynomial.X:polynomial ℤ)^2) 1 = 2 • (polynomial.X:polynomial ℤ) :=
-- begin
--   simp [deriv_n, polynomial.derivative], rw finsupp.sum,
--   have triv : ((polynomial.X:polynomial ℤ) ^ 2).support = ({2}:finset ℕ),
--   {
    
--   }
-- end
-- | deriv_n 1 (polynomial.X^2) = 2 • polynomial.X := sorry
-- | deriv_n 2 (polynomial.X^2) = polynomial.C 2 := sorry

private lemma succ_pred (a b : ℕ) (h : a.succ = b) : a = b.pred :=
begin
  induction a with a IH, rw [<-h], exact rfl, exact (congr_arg nat.pred h).congr_right.mp rfl,
end

lemma deriv_X_pow (n : ℕ) (k : ℕ) (hk : k ≤ n) : 
  (deriv_n (polynomial.X^n) k) = ((finset.range k).prod (λ i, (n-i:ℤ))) • (polynomial.X ^ (n-k)) :=
begin
  induction k with k ih, simp [deriv_zero],
  rw deriv_n, rw function.iterate_succ_apply', rw <-deriv_n, rw ih, 
  rw polynomial.derivative_smul (∏ (i : ℕ) in finset.range k, (n - i:ℤ)) (polynomial.X ^ (n - k)),
  ext, rename n_1 i, rw polynomial.coeff_smul, rw polynomial.coeff_smul, rw polynomial.coeff_derivative, simp,
  split_ifs, rw finset.prod_range_succ, have triv : (i+1:ℤ)=(n-k:ℤ),
  {
    norm_cast, rw h, apply int.of_nat_sub, exact le_of_lt hk,
  }, rw triv, ring,

  {
    rw nat.sub_succ at h_1, rw <-nat.succ_eq_add_one at h, exfalso,
    exact h_1 (succ_pred i (n-k) h),
  },

  {
    rw nat.sub_succ at h_1, rw h_1 at h, rw <-nat.succ_eq_add_one at h,
    rw nat.succ_pred_eq_of_pos at h, exfalso, simp at h, exact h, exact nat.sub_pos_of_lt hk,
  },

  {
    refl,
  },
  {
    exact le_of_lt hk,
  },
end

lemma deriv_X_pow' (n : ℕ) (k : ℕ) (hk : k ≤ n) : 
  (deriv_n (polynomial.X^n) k) = (polynomial.C ((finset.range k).prod (λ i, (n-i:ℤ)))) * (polynomial.X ^ (n-k)) :=
begin
  rw deriv_X_pow, ext, rw polynomial.coeff_smul,  rw polynomial.coeff_C_mul, assumption,
end

-- lemma coeff_X_sub_pow (n i : ℕ) (c : ℤ) : ((polynomial.X - polynomial.C c)^n).coeff i = (n.choose i : ℤ) * (-c)^(n-i) :=
-- begin
--   induction n with n ih, simp,
--   split_ifs, rw h, simp, simp, have eq := nat.choose_zero_succ i.pred,
-- end

lemma deriv1_X_sub_pow (c:ℤ) (m:ℕ) : ((polynomial.X - polynomial.C c)^m).derivative = (polynomial.C (m:ℤ)) * (polynomial.X - polynomial.C c)^ (m-1) :=
begin
  cases m, simp,
  induction m with m IH, simp, simp, rw nat.succ_eq_add_one, rw pow_add, rw pow_one, rw polynomial.derivative_mul, rw IH,
  rw [mul_assoc],
  have triv : (polynomial.X - polynomial.C c) ^ (m.succ - 1) * (polynomial.X - polynomial.C c) = (polynomial.X - polynomial.C c) ^ (m.succ - 1) * (polynomial.X - polynomial.C c) ^ 1,
  {
    simp,
  }, rw triv,
  rw <-pow_add, simp, rw <-nat.succ_eq_add_one,
  have triv : (polynomial.C ↑m + 1) * (polynomial.X - polynomial.C c) ^ m.succ + (polynomial.X - polynomial.C c) ^ m.succ
            = (polynomial.C ↑m + 1) * (polynomial.X - polynomial.C c) ^ m.succ + polynomial.C 1 * (polynomial.X - polynomial.C c) ^ m.succ,
  {
    simp,
  },
  rw triv, rw <-add_mul, simp,
end

lemma deriv_X_sub_pow (n k : ℕ) (c : ℤ) (hk : k ≤ n) :
  (deriv_n ((polynomial.X-polynomial.C c)^n) k) = (polynomial.C ((finset.range k).prod (λ i, (n-i:ℤ)))) * ((polynomial.X - polynomial.C c) ^ (n-k)) :=
begin
  induction k with k IH, simp [deriv_zero],
  {
    rw deriv_n, rw function.iterate_succ_apply', rw <-deriv_n, rw IH, rw polynomial.derivative_mul, simp, rw finset.prod_range_succ, simp,
    suffices : ((polynomial.X - polynomial.C c) ^ (n - k)).derivative  = (polynomial.C (n:ℤ) - polynomial.C (k:ℤ)) * (polynomial.X - polynomial.C c) ^ (n - k.succ),
    {
      rw this, ring,
    },
    have triv : (polynomial.C (n:ℤ) - polynomial.C (k:ℤ)) = (polynomial.C (n-k:ℤ)), simp,
    ext, rename n_1 m, rw triv, rw polynomial.coeff_C_mul, rw polynomial.coeff_derivative,
    

  },
end


theorem f_p_prod_part1 (p : ℕ) (hp : nat.prime p) (n j : ℕ) (hj : j < p - 1) 
  (k : ℕ) (hk : k.succ ∈ finset.range n.succ) :
  ∀ i:ℕ, (i ∈ finset.range j.succ) ->
          polynomial.eval (k.succ:ℤ) (deriv_n (∏ (i : ℕ) in finset.range n, (polynomial.X - (polynomial.C (i + 1:ℤ))) ^ p) i) = 0 :=
begin
  induction n with n IH, simp at hk, exfalso, exact nat.succ_ne_zero k hk,
  {
    simp at hk, replace hk : k.succ ≤ n.succ, exact nat.lt_succ_iff.mp hk, replace hk : k.succ < n.succ ∨ k.succ = n.succ, exact lt_or_eq_of_le hk,
    cases hk, simp at IH, replace IH := IH hk, intros i hi, simp at hi,
    rw finset.prod_range_succ, rw deriv_n_poly_prod, rw eval_sum', apply finset.sum_eq_zero, intros x hx, simp at hx,
    have hx' : x < j.succ, {exact gt_of_ge_of_gt hi hx,}, replace hx' := IH x hx', simp, right, assumption,

    intros x hx, rw finset.prod_range_succ, rw deriv_n_poly_prod, rw eval_sum', apply finset.sum_eq_zero, intros y hy, rw polynomial.eval_mul, simp,
    left, right, simp at hx hy,
    have triv : (polynomial.C ↑n + 1) = polynomial.C (n+1:ℤ), {simp,}, rw triv,
    rw deriv_X_sub_pow p (x-y) (n+1:ℤ), rw polynomial.eval_mul, rw mul_eq_zero, right, rw [nat.succ_eq_add_one,nat.succ_eq_add_one] at hk,
    rw [nat.succ_eq_add_one] at hx hy,
    have triv : (k+1:ℤ)=(n+1:ℤ), {norm_cast, exact hk}, rw triv, simp, rw zero_pow,
    replace hj : j + 1 < p, 
    {
      exact nat.lt_pred_iff.mp hj,
    },
    have ineq : x < p,
    {
      exact gt.trans hj hx,
    },
    have ineq2 : x - y ≤ x,
    {
      exact nat.sub_le x y,
    },
    have ineq3 : x - y < p,
    {
      exact gt_of_gt_of_ge ineq ineq2,
    },
    exact nat.sub_pos_of_lt ineq3,
    replace hj : j + 1 < p, 
    {
      exact nat.lt_pred_iff.mp hj,
    },
    have ineq : x < p,
    {
      exact gt.trans hj hx,
    },
    have ineq2 : x - y ≤ x,
    {
      exact nat.sub_le x y,
    },
    have ineq3 : x - y < p,
    {
      exact gt_of_gt_of_ge ineq ineq2,
    },
    exact le_of_lt ineq3,
  }
end



theorem deriv_f_p_k1 (p : ℕ) (hp : nat.prime p) (n j : ℕ) (hj : j < p - 1) (k : ℕ) (hk : k ∈ finset.range n.succ): 
  polynomial.eval (k:ℤ) (deriv_n (f_p p hp n) j) = 0 :=
begin
  rw f_p,
  rw deriv_n_poly_prod (polynomial.X ^ (p - 1)) (∏ (i : ℕ) in finset.range n, (polynomial.X - polynomial.C (↑i + 1)) ^ p) j,
  rw eval_sum', apply finset.sum_eq_zero, intros i hi,
  cases k,
  {
    -- k = 0,
    simp at hi hk,
    have ineq : j - i < p - 1,
    {
      rw nat.succ_eq_add_one at hi,
      have ineq : j - i ≤ j, 
      {
        exact nat.sub_le j i,
      },
      exact gt_of_gt_of_ge hj ineq,
    },
    rw polynomial.eval_mul, rw mul_eq_zero, left, rw polynomial.eval_mul, rw mul_eq_zero, right, 
    rw deriv_X_pow', rw polynomial.eval_mul, simp, right, apply zero_pow, 
    exact nat.sub_pos_of_lt ineq,
    exact le_of_lt ineq,
  },

  {
    -- k ≥ 1,
    rw polynomial.eval_mul, rw mul_eq_zero, right,
    have H := f_p_prod_part1 p hp n j hj k, simp at H, simp at hk, replace H := H hk, simp at hi,
    replace H := H i hi, simp at H ⊢, exact H,
  },
end

theorem e_transcendental : ¬ is_algebraic ℤ e :=
begin
  by_contra e_algebraic,
  rw is_algebraic at e_algebraic,
  choose g g_def using e_algebraic,
  have g_nonzero := g_def.1,
  have e_root_g := g_def.2,

  sorry
end


end e