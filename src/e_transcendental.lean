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

-- theorem f_bar_p (p : ℕ) (hp : nat.prime p) (n i : ℕ) : i ≤ n -> polynomial.eval (i : ℤ) (f_bar (f_p p hp n)) ≤ (2*n:ℤ)^(f_p p hp n).nat_degree :=
-- begin
--   generalize hfp : f_p p hp n = fp,
--   generalize hm : fp.nat_degree = m,
--   induction n with n IH,
--   {
--     simp, intro hi, rw hi, rw <-hfp at hm, rw deg_f_p at hm, simp at hm, rw zero_pow, simp [f_p] at hfp, rw <-hfp,
--     simp [f_bar],
--   }
-- end



def J (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) : ℝ := 
  ∑ i in finset.range g.nat_degree.succ, (g.coeff i : ℝ) * (II (f_p p hp g.nat_degree) i (nonneg_nat i))


theorem abs_J_ineq1' (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) :
  abs (J g p hp) ≤ ∑ i in finset.range g.nat_degree.succ, (abs (g.coeff i)) * (i : ℝ) * (i:ℝ).exp * (f_eval_on_ℝ (f_bar (f_p p hp g.nat_degree)) (i:ℝ)) :=
begin
  have ineq1 : abs (J g p hp) ≤ (∑ i in finset.range g.nat_degree.succ, abs ((g.coeff i : ℝ) * (II (f_p p hp g.nat_degree) i (nonneg_nat i)))),
  {
    apply finset.abs_sum_le_sum_abs,
  },

  have triv : 
    (∑ i in finset.range g.nat_degree.succ, abs ((g.coeff i : ℝ) * (II (f_p p hp g.nat_degree) i (nonneg_nat i)))) =
    (∑ i in finset.range g.nat_degree.succ, abs ((g.coeff i : ℝ)) * abs((II (f_p p hp g.nat_degree) i (nonneg_nat i)))),
  {
    apply finset.sum_congr, refl, intros, rw abs_mul,
  },

  rw triv at ineq1,

  have ineq2:
    (∑ i in finset.range g.nat_degree.succ, abs ((g.coeff i : ℝ)) * abs((II (f_p p hp g.nat_degree) i (nonneg_nat i)))) ≤
    (∑ i in finset.range g.nat_degree.succ, abs ((g.coeff i : ℝ)) * (i:ℝ)*(i:ℝ).exp * (f_eval_on_ℝ (f_bar (f_p p hp g.nat_degree)) (i:ℝ))),
  {
    apply finset.sum_le_sum, intros x hx, replace triv : (x:ℝ) ≥ 0, {norm_cast, exact bot_le,},
    have ineq3 := abs_II_le2 (f_p p hp g.nat_degree) (x:ℝ) triv, 
    have triv2 : (II (f_p p hp g.nat_degree) ↑x _) = (II (f_p p hp g.nat_degree) ↑x triv),
    {
      rw II,
    }, rw triv2, rw mul_assoc, rw mul_assoc, apply mul_le_mul, exact le_refl (abs ↑(polynomial.coeff g x)),
    rw <-mul_assoc, exact ineq3, exact abs_nonneg (II (f_p p hp (polynomial.nat_degree g)) ↑x triv), exact abs_nonneg _,
  },
  exact le_trans ineq1 ineq2,
end


-- lemma coe_f_eval (f : polynomial ℤ) (i : ℕ) : f_eval_on_ℝ f (i:ℝ) = ((@polynomial.eval ℤ _ (i : ℤ) f):ℝ) :=
-- begin
--   simp [f_eval_on_ℝ], 
-- end


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

lemma deriv_X_pow_too_much (n : ℕ) (k : ℕ) (hk : k > n) :
  (deriv_n (polynomial.X^n) k) = 0 :=
begin
  induction k with k IH, exfalso, linarith,
  {
    replace hk : n ≤ k,
    {
      exact nat.lt_succ_iff.mp hk,
    },
    replace hk : n < k ∨ n = k,
    {
      exact lt_or_eq_of_le hk,
    },
    cases hk,
    {
      have IH' := IH hk,
      rw <-deriv_succ, rw IH', simp,
    },
    {
      rw <-hk, rw <-deriv_succ, rw deriv_X_pow', simp, exact le_refl n,
    }
  }
end

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
    have triv : (polynomial.C (n:ℤ) - polynomial.C (k:ℤ)) = (polynomial.C (n-k:ℤ)), simp, rw deriv1_X_sub_pow, rw triv,
    suffices : polynomial.C ↑(n - k) = polynomial.C (n - k:ℤ),
    {
      rw this, refl,
    },
    ext, rw polynomial.coeff_C, split_ifs, rw h, simp,
    suffices : int.of_nat (n-k) = ↑n - ↑k, rw <-this, simp, apply int.of_nat_sub, exact le_of_lt hk, rw polynomial.coeff_C, simp [h], exact le_of_lt hk,
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

lemma fact_eq_prod (n : ℕ) : (n.fact:ℤ) = ∏ i in finset.range n, (i+1:ℤ) :=
begin
  induction n with n ih, simp,
  {
    rw nat.fact_succ, rw finset.prod_range_succ, simp, rw ih,
  },
end

lemma fact_eq_prod' (n : ℕ) : (n.fact:ℤ) = ∏ i in finset.range n, (n-i:ℤ) :=
begin
  induction n with n ih, simp,
  {
    rw nat.fact_succ, rw finset.prod_range_succ', simp, rw ih, rw mul_comm,
  },
end

theorem deriv_f_p_p_sub1_0 (p : ℕ) (hp : nat.prime p) (n : ℕ) : 
  polynomial.eval 0 (deriv_n (f_p  p hp n) (p-1)) = (p-1).fact * (-1)^(n*p)*(n.fact)^p :=
begin
  rw f_p, rw deriv_n_poly_prod, rw eval_sum',
  have triv : ∑ (i : ℕ) in
      finset.range (p - 1).succ,
      polynomial.eval 0
        (polynomial.C ↑((p - 1).choose i) * deriv_n (polynomial.X ^ (p - 1)) (p - 1 - i) *
           deriv_n (∏ (i : ℕ) in finset.range n, (polynomial.X - polynomial.C (↑i + 1)) ^ p) i) = 
      ∑ (i : ℕ) in
      finset.range (p - 1).succ,
      polynomial.eval 0
        (polynomial.C ↑((p - 1).choose i) * deriv_n (polynomial.X ^ (p - 1)) (p - 1 - i)) *
      polynomial.eval 0 (deriv_n (∏ (i : ℕ) in finset.range n, (polynomial.X - polynomial.C (↑i + 1)) ^ p) i),
  {
    apply congr_arg, ext, rw polynomial.eval_mul,
  }, rw triv,

  replace triv : ((p - 1).fact:ℤ) * (-1) ^ (n * p) * (n.fact:ℤ) ^ p = ∑ i in finset.range 1, polynomial.eval 0 (polynomial.C ↑((p - 1).choose i) * deriv_n (polynomial.X ^ (p - 1)) (p - 1 - i)) *
        polynomial.eval 0 (deriv_n (∏ (i : ℕ) in finset.range n, (polynomial.X - polynomial.C (↑i + 1)) ^ p) i),
  {
    simp, simp [deriv_zero], rw eval_prod', simp,
    have eq1 : ∏ (x : ℕ) in finset.range n, (-1 + -(x:ℤ)) ^ p = ∏ (x : ℕ) in finset.range n, (-(1+x)) ^ p,
    {
      apply congr_arg, ext, simp, rw add_comm,
    },
    rw eq1,
    replace eq1 : ∏ (x : ℕ) in finset.range n, (-(1+x:ℤ)) ^ p = ∏ (x : ℕ) in finset.range n, (-1)^p * (1+x:ℤ) ^ p,
    {
      apply congr_arg, ext, rw neg_pow,
    }, rw eq1, rw finset.prod_mul_distrib, simp, rw <-pow_mul, rw mul_comm p n, rw finset.prod_pow,
    replace eq1 : (∏ (x : ℕ) in finset.range n, (1 + x:ℤ)) = (n.fact:ℤ),
    {
      rw fact_eq_prod, apply congr_arg, ext, rw add_comm,
    }, rw eq1,
    rw deriv_X_pow', rw polynomial.eval_mul, simp, rw <-fact_eq_prod', exact mul_assoc ↑((p - 1).fact) ((-1) ^ (n * p)) (↑(nat.fact n) ^ p),
    exact le_refl (p - 1),
  },
  rw triv, apply eq.symm, apply finset.sum_subset, simp, intros x hx1 hx2,rw deriv_X_pow', rw polynomial.eval_mul, simp, left, right, right,
  apply zero_pow, simp at hx1 hx2 ⊢, replace triv : (p-1).succ = p, 
  {
    rw nat.sub_one, apply nat.succ_pred_eq_of_pos, exact nat.prime.pos hp, 
  }, rw triv at hx1, suffices : (p - 1 - x) < p - 1, exact nat.sub_pos_of_lt this,
  replace triv : x ≤ p - 1, exact nat.le_pred_of_lt hx1, apply nat.sub_lt_of_pos_le, exact bot_lt_iff_ne_bot.mpr hx2, assumption, exact (p - 1).sub_le x,
end

theorem f_p_n_succ (p : ℕ) (hp : nat.prime p) (n : ℕ) : (f_p p hp n.succ) = (f_p p hp n) * (polynomial.X- polynomial.C (n+1:ℤ))^p :=
begin
  rw f_p, rw f_p, rw finset.prod_range_succ, ring,
end




theorem deriv_f_p_sub1 (p : ℕ) (hp : nat.prime p) (n : ℕ) : ∀ x : ℕ, ∀ j : ℕ, j < p ->
  x > 0 -> x < n.succ -> polynomial.eval (x:ℤ) (deriv_n (f_p p hp n) j) = 0 :=
begin
  induction n with n hn,
  {
    intros x j hj hx1 hx2,
    rw f_p, linarith,
  },
  {
    intros x j hj hx1 hx2,
    rw f_p_n_succ, rw deriv_n_poly_prod, rw eval_sum', apply finset.sum_eq_zero, intros y hy, simp at hy,
    rw polynomial.eval_mul, rw polynomial.eval_mul, rw polynomial.eval_C,
    replace hx2 : x < n.succ ∨ x = n.succ, exact nat.lt_succ_iff_lt_or_eq.mp hx2,
    replace triv : j - y ≤ j, exact nat.sub_le j y,
    have y_p : j - y < p, exact gt_of_gt_of_ge hj triv,
    have hn' : ∀ (x : ℕ), x > 0 → x < n.succ → polynomial.eval ↑x (deriv_n (f_p p hp n) (j-y)) = 0,
    {
      intros, apply hn, assumption, assumption, assumption,
    },
    cases hx2,
    {
      -- x < n.succ
      have hn'' := hn' x hx1 hx2, rw hn'', rw mul_zero, rw zero_mul,
    },
    {
      -- x = n.succ
      rw mul_eq_zero, right, rw hx2, rw deriv_X_sub_pow, rw polynomial.eval_mul, rw polynomial.eval_pow, simp, right, apply zero_pow,
      replace triv : y < p, exact gt_of_ge_of_gt hj hy, exact nat.sub_pos_of_lt triv,
      replace triv : y < p, exact gt_of_ge_of_gt hj hy, exact le_of_lt triv,
    },
  }
end

theorem when_j_eq_p_sub1 (p : ℕ) (hp : nat.prime p) (g : polynomial ℤ): 
  (∑ k in finset.range g.nat_degree.succ,
              (g.coeff k) * (polynomial.eval (k:ℤ) (deriv_n (f_p p hp g.nat_degree) (p-1)))) = (g.coeff 0) * (polynomial.eval 0 (deriv_n (f_p  p hp g.nat_degree) (p-1))) :=
begin
  have triv : g.coeff 0 * polynomial.eval 0 (deriv_n (f_p p hp g.nat_degree) (p - 1)) = ∑ (k : ℕ) in finset.range 1, g.coeff k * polynomial.eval ↑k (deriv_n (f_p p hp g.nat_degree) (p - 1)),
  {
     simp,
  }, rw triv, apply eq.symm, apply finset.sum_subset, simp,
  intros x hx1 hx2, simp at hx1 hx2, 
  rw deriv_f_p_sub1, simp, 
  have triv := @nat.sub_one_sub_lt p 0 _, simp at triv, exact triv, exact nat.prime.pos hp, exact bot_lt_iff_ne_bot.mpr hx2, assumption,
end



-- theorem when_j_ge_p_k_eq_zero (p : ℕ) (hp : nat.prime p) (n:ℕ) : ∀ j : ℕ, j > p -> (p.fact:ℤ) ∣ polynomial.eval 0 (deriv_n (f_p p hp n) j) :=
-- begin
--    induction n with n IHn,
--    {
--      rw f_p, simp, intros j hj, rw deriv_X_pow_too_much, simp, have triv : p - 1 ≤ p, exact nat.sub_le p 1, exact gt_of_gt_of_ge hj triv,
--    },
--    {
--      intros j hj,
--      rw f_p_n_succ, rw deriv_n_poly_prod, rw eval_sum',
--      apply finset.dvd_sum,
--      intros y hy, simp at hy IHn,
--      rw polynomial.eval_mul, rw polynomial.eval_mul,
--    }
-- end


def set_of_abs_coeff (g : polynomial ℤ) : finset ℤ := finset.image (λ i : ℕ, abs (g.coeff i)) g.support
def set_of_1_abs_coeff (g : polynomial ℤ) : finset ℤ := insert 1 (set_of_abs_coeff g)
theorem set_of_1_abs_coeff_nonempty (g : polynomial ℤ) : finset.nonempty (set_of_1_abs_coeff g) :=
begin
  rw set_of_1_abs_coeff, use 1, simp,
end

def max_abs_coeff_1 (g : polynomial ℤ) := finset.max' (set_of_1_abs_coeff g) (set_of_1_abs_coeff_nonempty g)
lemma max_abs_coeff_1_ge_1 (g : polynomial ℤ) : 1 ≤ max_abs_coeff_1 g :=
begin
  rw max_abs_coeff_1, apply finset.le_max', rw set_of_1_abs_coeff, simp,
end

def M (g : polynomial ℤ) : ℝ := ((max_abs_coeff_1 g:ℝ) * (g.nat_degree:ℝ) * (g.nat_degree:ℝ).exp * (2*g.nat_degree:ℝ)^(g.nat_degree+1))


theorem abs_J_ineq1 (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) : abs (J g p hp) ≤ (M g)^p :=
begin
  sorry
end


theorem abs_J_ineq2 (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) (hp2 : p > g.nat_degree ∧ p > (g.coeff 0).nat_abs) : ((p-1).fact:ℝ) ≤ (abs (J g p hp)) :=
begin
  sorry
end

-- lemma test (a : ℕ) (n : ℕ) : tendsto

lemma sum_sub_sum1 (m : ℕ) (f : ℕ -> ℂ) : (∑ i in finset.range m.succ, f i) - (∑ i in finset.range m, f i) = f m :=
begin
  rw finset.sum_range_succ, simp,
end

lemma fact_grows_fast' (M : ℕ) : ∃ N : ℕ, ∀ n : ℕ, n > N -> (n.fact) > M ^ (n+1) :=
begin
by_cases (M = 0),
{
  rw h, use 1, intros n hn, simp, rw nat.zero_pow, exact nat.fact_pos n, exact nat.succ_pos n,
},
  have H := complex.is_cau_exp (M:ℂ),
  have triv : (1/M:ℝ) > 0, apply one_div_pos_of_pos, norm_cast, exact bot_lt_iff_ne_bot.mpr h,
  have H2 := is_cau_seq.cauchy₂ H triv,
  choose i hi using H2, use i, intros n hn,
  have H3 := hi n.succ n _ _, rw finset.sum_range_succ at H3, simp at H3,
  have triv2 : ((M:ℂ) ^ n).abs = (↑M ^ n),
  {
    have eq1 : ↑((M:ℝ)^n) = (M:ℂ)^n, simp, rw <-eq1, rw complex.abs_of_real, rw abs_of_pos, apply pow_pos, norm_num, exact bot_lt_iff_ne_bot.mpr h,
  },
  rw triv2 at H3, norm_num at H3, rw div_lt_iff at H3,
  replace triv2 : (M:ℝ) > 0, norm_num, exact bot_lt_iff_ne_bot.mpr h,
  have H4 := (mul_lt_mul_right triv2).2 H3,
  replace triv2 : (M:ℝ)^n * (M:ℝ) = (M:ℝ)^(n+1), rw pow_add, simp, rw triv2 at H4,
  replace triv2 : (↑M)⁻¹ * ↑(n.fact) * ↑M = (n.fact:ℝ),
  {
    rw mul_comm, rw <-mul_assoc, 
    have triv3 : (M:ℝ) * (↑M)⁻¹ = 1, rw mul_comm, apply inv_mul_cancel, norm_num, assumption, rw triv3, simp,
  },
  rw triv2 at H4, norm_cast at H4, assumption, norm_cast, exact nat.fact_pos n, 
  suffices : n.succ > i, exact le_of_lt this, exact nat.lt.step hn, exact le_of_lt hn,
end

lemma fact_grows_fast (M : ℝ) (hM : M ≥ 0) : ∃ N : ℕ, ∀ n : ℕ, n > N -> (n.fact : ℝ) > M^(n+1) :=
begin
  have triv := (@archimedean_iff_nat_lt ℝ _).1 _ M,
  choose M' hM' using triv,
  replace triv := fact_grows_fast' M',
  choose N hN using triv, use N, intros n hn,
  replace hN := hN n hn,
  have ineq : (M':ℝ) ^ (n + 1) > M ^ (n+1),
  {
    apply pow_lt_pow_of_lt_left, assumption, assumption, exact nat.succ_pos n,
  },
  suffices : (n.fact:ℝ) > (M':ℝ) ^ (n + 1),
  {
    exact gt.trans this ineq,
  },
  norm_cast, assumption, exact real.archimedean,
end


theorem contradiction (M : ℝ) (hM : M ≥ 0) (z : ℤ) : ∃ p : nat.primes, (p.val:ℤ) > z ∧ ((p.val-1).fact:ℝ) > M^p.val :=
begin
  have grow_rate := fact_grows_fast M hM,
  choose N hN using grow_rate,
  have p_exists := nat.exists_infinite_primes (max (N+2) (z.nat_abs+1)),
  choose p Hp using p_exists, use (⟨p, Hp.right⟩ : nat.primes), simp at Hp ⊢,
  split,
  {
    have triv : z ≤ (z.nat_abs:ℤ), rw <-int.abs_eq_nat_abs, exact le_max_left z (-z),
    have hp := Hp.left.right,
    replace hp : (z.nat_abs + 1:ℤ) ≤ p, norm_cast, assumption,
    have triv2 : (z.nat_abs : ℤ) < (z.nat_abs:ℤ) + 1, exact lt_add_one ↑(int.nat_abs z), exact gt_of_gt_of_ge hp triv,
  },
  {
    have triv := hN (p-1) _, simp at triv,
    have eq1 : (p - 1 + 1) = p, {apply nat.sub_add_cancel, exact le_of_lt Hp.right.one_lt,},
    rw eq1 at triv, assumption,
    have triv := Hp.left.left,
    replace triv : N + 1 < p , exact triv, exact nat.lt_pred_iff.mpr triv,
  },
end

theorem e_transcendental : ¬ is_algebraic ℤ e :=
begin
-- main part
  by_contra e_algebraic,
  rw is_algebraic at e_algebraic,
  choose g g_def using e_algebraic,
  have g_nonzero := g_def.1,
  have e_root_g := g_def.2,
  have contradiction := contradiction (M g) _ (max g.nat_degree (abs (g.coeff 0))),
  choose p Hp using contradiction,
  have abs_J_ineq1 := abs_J_ineq1 g p.val p.property,
  simp at Hp,
  have abs_J_ineq2 := abs_J_ineq2 g p.val p.property _,
  have rid := le_trans abs_J_ineq2 abs_J_ineq1,
  have rid2 := Hp.right, replace rid2 : ¬ ((M g ^ p) ≥ ((p.val - 1).fact:ℝ)),
  {
    exact not_le.mpr rid2,
  },  exact rid2 rid,


-- assumptions I used in part and lemmas 
  {
    split,
    have triv := Hp.left.left, exact triv,
    have triv := Hp.left.right, rw int.abs_eq_nat_abs at triv, simp at triv, assumption,
  },

  {
    rw M, apply mul_nonneg, apply mul_nonneg, apply mul_nonneg, norm_cast, exact ge_trans (max_abs_coeff_1_ge_1 g) trivial,
    norm_cast, exact bot_le, have triv : (g.nat_degree : ℝ).exp > 0, exact (polynomial.nat_degree g:ℝ).exp_pos, exact le_of_lt triv,
    norm_num, apply pow_nonneg, apply mul_nonneg, linarith, norm_cast, exact bot_le,
  },
end


end e