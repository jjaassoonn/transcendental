import data.real.basic
import data.complex.exponential
import ring_theory.algebraic
import e_trans_helpers2
import data.int.basic
import data.polynomial

noncomputable theory
open_locale classical
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
  simp only [polynomial.nat_degree_one, finset.sum_empty, finset.range_zero, finset.prod_empty],

  rw finset.sum_range_succ, rw finset.prod_range_succ,
  have triv : (∀ (i : ℕ), i ∈ finset.range s → f i ≠ 0),
  {
    intros i hi, apply hf, simp only [finset.mem_range] at hi ⊢, exact nat.lt.step hi,
  },
  replace ih := ih triv, rw <-ih, apply polynomial.nat_degree_mul_eq,
  apply hf, simp only [finset.self_mem_range_succ],
  intro rid, rw [finset.prod_eq_zero_iff] at rid,
  choose a ha using rid,
  refine hf a _ ha.2, simp only [finset.mem_range] at ha ⊢, exact nat.lt.step ha.left,
end

/-Definition
For any prime number $p$ and natural number $n$, we can define a polynomial
\[X^{p-1}(X-1)^p\cdots(X-n)^p\]
-/
def f_p (p : ℕ) (hp : nat.prime p) (n : ℕ): polynomial ℤ := polynomial.X ^ (p - 1) * (∏ i in finset.range n, (polynomial.X - (polynomial.C (i+1:ℤ)))^p)

/-Theorem
The degree of `f_p n` is $(n+1)p-1$
-/
theorem deg_f_p (p : ℕ) (hp : nat.prime p) (n : ℕ) : (f_p p hp n).nat_degree = (n+1)*p - 1 :=
begin
  rw f_p,
  -- We have that the degree of a bunch of non-zero polynomials is the sum of their degree
  have eq1 := @polynomial.nat_degree_mul_eq ℤ _ (polynomial.X ^ (p - 1)) (∏ i in finset.range n, (polynomial.X - (polynomial.C (i+1:ℤ)))^p) _ _,
  
  rw eq1,
  -- and $X$ has degree one
  have triv : (polynomial.X : polynomial ℤ).nat_degree = 1 := by simp only [polynomial.nat_degree_X],
  simp only [polynomial.C_add, polynomial.C_1, polynomial.nat_degree_pow_eq, triv, mul_one],

  have triv' : (∏ (i : ℕ) in finset.range n, (polynomial.X - polynomial.C (i+1:ℤ)) ^ p).nat_degree 
              = ∑ i in finset.range n, ((polynomial.X - polynomial.C (i+1:ℤ)) ^ p).nat_degree,
  {
    apply prod_deg, 
    intros i hi, intro rid, 
    replace rid := @pow_eq_zero (polynomial ℤ) _ (polynomial.X - polynomial.C (i+1:ℤ)) p rid,
    rw sub_eq_zero_iff_eq at rid,
    have rid' : (polynomial.C (i+1:ℤ)).nat_degree = 1,
    rw <-rid, exact triv, have rid'' := polynomial.nat_degree_C (i+1:ℤ), linarith,
  }, simp only [polynomial.C_add, polynomial.C_1, polynomial.nat_degree_pow_eq] at triv',
  rw triv',
  have triv'' : (∑ (x : ℕ) in finset.range n, p * (polynomial.X - (polynomial.C ↑x + 1)).nat_degree) = ∑ x in finset.range n, p,
  {
    apply congr_arg, ext, rename x i,
    have eq1 : (polynomial.X - (polynomial.C (i:ℤ) + 1)) =  (polynomial.X - (polynomial.C (i + 1:ℤ))):= by simp only [polynomial.C_add, polynomial.C_1],
    rw eq1,
    have deg1 : (polynomial.X - polynomial.C (i + 1:ℤ)).degree = 1 := polynomial.degree_X_sub_C _,
    have deg2 : (polynomial.X - polynomial.C (i + 1:ℤ)).nat_degree = 1,
    {
      rw polynomial.nat_degree, rw deg1, exact rfl,
    },
    rw deg2, rw mul_one,
  },
  rw triv'', rw finset.sum_const, simp only [nat.nsmul_eq_mul, finset.card_range], ring, 
  have eq2 := (@nat.add_sub_assoc p 1 _ (p*n)),
  rw eq2, rw add_comm, exact nat.succ_le_iff.mpr (nat.prime.pos hp),

  intro rid, replace rid := pow_eq_zero rid, exact polynomial.X_ne_zero rid,


  {
    intro rid, rw finset.prod_eq_zero_iff at rid,
    choose i hi using rid,
    have hi1 := hi.1, have hi2 := hi.2, replace hi2 := pow_eq_zero hi2,
    have deg1 := polynomial.degree_X_sub_C (i+1:ℤ), rw hi2 at deg1, simp only [polynomial.degree_zero] at deg1,
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
  rw <-finset.sum_sub_distrib, apply congr_arg, ext i, rw <-mul_sub, rw <-I,
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
    simp only [finset.mem_range], suffices : i ≤ g.nat_degree, {exact nat.lt_succ_iff.mpr this}, apply polynomial.le_nat_degree_of_ne_zero,
    have triv := (g.3 i).1 hi, exact triv,
    intros i hi Hi, rw mul_eq_zero, left, norm_cast, by_contra, exact Hi ((g.3 i).2 a),
  },
  rw <-eq2,

  have eq3 : (∑ x in g.support, (g.coeff x:ℝ) * (x:ℝ).exp) = (polynomial.aeval ℤ ℝ e) g,
  {
    rw polynomial.aeval_def, rw polynomial.eval₂, rw finsupp.sum, apply congr_arg, ext, simp only [ring_hom.eq_int_cast], rw e,
    apply mul_eq_mul', norm_cast,

    induction x with x IH, simp only [real.exp_zero, nat.cast_zero, pow_zero],
    rw nat.succ_eq_add_one, simp only [nat.cast_add, nat.cast_one], rw real.exp_add, rw IH, ring,
  }, rw eq3, rw e_root_g, rw zero_mul,
end

theorem J_eq (g : polynomial ℤ) (e_root_g : (polynomial.aeval ℤ ℝ e) g = 0) 
             (p : ℕ) (hp : nat.prime p) : 
  (J g p hp) = - ∑ k in finset.range g.nat_degree.succ,
                (∑ j in finset.range (f_p p hp g.nat_degree).nat_degree.succ,
                  (g.coeff k : ℝ) * (f_eval_on_ℝ (deriv_n (f_p p hp g.nat_degree) j) (k:ℝ))) :=
begin
  rw J_eq1, rw J_eq2, rw J_eq3, simp only [neg_inj, zero_sub], apply congr_arg, ext, rw finset.mul_sum, assumption,
end

theorem sum_swap_index (s1 s2 : finset ℕ) (g : ℕ -> ℕ -> ℝ) : ∑ i in s1, (∑ j in s2, g i j) = ∑ j in s2, (∑ i in s1, g i j) := finset.sum_comm

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
    intro a, simp only [f_eval_on_ℝ, polynomial.map_C, polynomial.eval_C],
  },
  {
    intros p q hp hq,
    simp only [f_eval_on_ℝ_add, hp, hq, int.cast_add, ring_hom.eq_int_cast, polynomial.eval_add],
  },
  {
    intros m a ha, simp only [f_eval_on_ℝ, int.cast_coe_nat, polynomial.eval_X, polynomial.map_C, int.cast_pow, polynomial.eval_C,
 polynomial.map_X, int.cast_mul, polynomial.eval_pow, polynomial.map_pow, polynomial.eval_mul,
 polynomial.map_mul] at ha ⊢, simp only [int.cast_coe_nat, int.cast_pow, ring_hom.eq_int_cast, int.cast_mul],
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
  intros j hj, rw ring_hom.map_mul, simp only [ring_hom.eq_int_cast], apply mul_eq_mul', exact rfl, rw f_eval_on_ℝ_nat, simp only [ring_hom.eq_int_cast],
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
  apply finset.induction_on s, simp only [finset.sum_empty, polynomial.eval_zero],
  intros a s ha ih, rw finset.sum_insert, rw polynomial.eval_add, rw ih, rw finset.sum_insert, exact ha, exact ha,
end

theorem eval_prod' (s : finset ℕ) (f : ℕ -> polynomial ℤ) (t : ℤ) : polynomial.eval t (∏ i in s, f i) = ∏ i in s, polynomial.eval t (f i) :=
begin
  apply finset.induction_on s, simp only [polynomial.eval_one, finset.prod_empty],
  intros a s ha ih, rw finset.prod_insert, rw polynomial.eval_mul, rw ih, rw finset.prod_insert, exact ha, exact ha,
end

theorem deriv_n_C_mul (c : ℤ) (n : ℕ) : ∀ f : polynomial ℤ, (deriv_n (polynomial.C c * f) n) = (polynomial.C c) * (deriv_n f n) :=
begin
  induction n with n IH, simp only [zeroth_deriv, forall_const, eq_self_iff_true],
  intro f,
  rw deriv_n, rw function.iterate_succ, simp only [polynomial.derivative_mul, zero_mul, function.comp_app, polynomial.derivative_C, zero_add], rw <-deriv_n, rw IH, refl,
end

theorem dvd_poly_pow_deriv (f : polynomial ℤ) (n m : ℕ) (c : ℤ) (hn : n > 0) (hm : m > 0) : (n:ℤ) ∣ polynomial.eval c (deriv_n (f^n) m) :=
begin
    cases m, linarith,

    rw [deriv_n, function.iterate_succ], simp only [function.comp_app], rw [<-deriv_n], rw poly_pow_deriv, 
    have triv : polynomial.C ↑n * f ^ (n - 1) * f.derivative = polynomial.C ↑n * (f ^ (n - 1) * f.derivative),
    {
      ring,
    }, rw triv,
    rw deriv_n_C_mul, rw polynomial.eval_mul, simp only [polynomial.eval_C, dvd_mul_right], assumption,
end


private lemma succ_pred (a b : ℕ) (h : a.succ = b) : a = b.pred :=
begin
  induction a with a IH, rw [<-h], exact rfl, exact (congr_arg nat.pred h).congr_right.mp rfl,
end

lemma deriv_X_pow (n : ℕ) (k : ℕ) (hk : k ≤ n) : 
  (deriv_n (polynomial.X^n) k) = ((finset.range k).prod (λ i, (n-i:ℤ))) • (polynomial.X ^ (n-k)) :=
begin
  induction k with k ih, simp only [zeroth_deriv, one_smul, finset.range_zero, finset.prod_empty, nat.sub_zero],
  rw deriv_n, rw function.iterate_succ_apply', rw <-deriv_n, rw ih, 
  rw polynomial.derivative_smul (∏ (i : ℕ) in finset.range k, (n - i:ℤ)) (polynomial.X ^ (n - k)),
  ext, rename n_1 i, rw polynomial.coeff_smul, rw polynomial.coeff_smul, rw polynomial.coeff_derivative, simp only [mul_boole, polynomial.coeff_X_pow, boole_mul, mul_ite, int.nat_cast_eq_coe_nat, mul_zero],
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
    rw nat.succ_pred_eq_of_pos at h, exfalso, simp only [eq_self_iff_true, not_true] at h, exact h, exact nat.sub_pos_of_lt hk,
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
      rw <-deriv_succ, rw IH', simp only [polynomial.derivative_zero],
    },
    {
      rw <-hk, rw <-deriv_succ, rw deriv_X_pow', simp only [mul_one, nat.sub_self, polynomial.derivative_C, pow_zero], exact le_refl n,
    }
  }
end

lemma deriv1_X_sub_pow (c:ℤ) (m:ℕ) : ((polynomial.X - polynomial.C c)^m).derivative = (polynomial.C (m:ℤ)) * (polynomial.X - polynomial.C c)^ (m-1) :=
begin
  cases m, simp only [polynomial.derivative_one, int.coe_nat_zero, zero_mul, polynomial.C_0, pow_zero],
  induction m with m IH, simp only [mul_one, int.coe_nat_zero, polynomial.derivative_sub, polynomial.C_1, sub_zero, int.coe_nat_succ, pow_one,
 polynomial.derivative_X, polynomial.derivative_C, zero_add, pow_zero], simp only [nat.succ_sub_succ_eq_sub, polynomial.C_add, polynomial.C_1, int.coe_nat_succ, nat.sub_zero], rw nat.succ_eq_add_one, rw pow_add, rw pow_one, rw polynomial.derivative_mul, rw IH,
  rw [mul_assoc],
  have triv : (polynomial.X - polynomial.C c) ^ (m.succ - 1) * (polynomial.X - polynomial.C c) = (polynomial.X - polynomial.C c) ^ (m.succ - 1) * (polynomial.X - polynomial.C c) ^ 1,
  {
    simp only [pow_one],
  }, rw triv,
  rw <-pow_add, simp only [mul_one, nat.succ_sub_succ_eq_sub, polynomial.C_add, polynomial.derivative_sub, polynomial.C_1, sub_zero,
 int.coe_nat_succ, polynomial.derivative_X, polynomial.derivative_C, nat.sub_zero], rw <-nat.succ_eq_add_one,
  have triv : (polynomial.C ↑m + 1) * (polynomial.X - polynomial.C c) ^ m.succ + (polynomial.X - polynomial.C c) ^ m.succ
            = (polynomial.C ↑m + 1) * (polynomial.X - polynomial.C c) ^ m.succ + polynomial.C 1 * (polynomial.X - polynomial.C c) ^ m.succ,
  {
    simp only [one_mul, polynomial.C_1],
  },
  rw triv, rw <-add_mul, simp only [polynomial.C_1],
end

lemma deriv_X_sub_pow (n k : ℕ) (c : ℤ) (hk : k ≤ n) :
  (deriv_n ((polynomial.X-polynomial.C c)^n) k) = (polynomial.C ((finset.range k).prod (λ i, (n-i:ℤ)))) * ((polynomial.X - polynomial.C c) ^ (n-k)) :=
begin
  induction k with k IH, simp only [zeroth_deriv, one_mul, polynomial.C_1, finset.range_zero, finset.prod_empty, nat.sub_zero],
  {
    rw deriv_n, rw function.iterate_succ_apply', rw <-deriv_n, rw IH, rw polynomial.derivative_mul, simp only [zero_mul, polynomial.derivative_C, zero_add], rw finset.prod_range_succ, simp only [polynomial.C_sub, polynomial.C_mul],
    suffices : ((polynomial.X - polynomial.C c) ^ (n - k)).derivative  = (polynomial.C (n:ℤ) - polynomial.C (k:ℤ)) * (polynomial.X - polynomial.C c) ^ (n - k.succ),
    {
      rw this, ring,
    },
    have triv : (polynomial.C (n:ℤ) - polynomial.C (k:ℤ)) = (polynomial.C (n-k:ℤ)), simp only [polynomial.C_sub], rw deriv1_X_sub_pow, rw triv,
    suffices : polynomial.C ↑(n - k) = polynomial.C (n - k:ℤ),
    {
      rw this, refl,
    },
    ext, rw polynomial.coeff_C, split_ifs, rw h, simp only [polynomial.coeff_C_zero, polynomial.C_sub, polynomial.coeff_sub],
    suffices : int.of_nat (n-k) = ↑n - ↑k, rw <-this, simp only [int.of_nat_eq_coe], apply int.of_nat_sub, exact le_of_lt hk, rw polynomial.coeff_C, simp only [h, if_false], exact le_of_lt hk,
  },
end

lemma deriv_X_sub_pow_too_much (n k : ℕ) (c : ℤ) (hk : k > n) :
  (deriv_n ((polynomial.X - polynomial.C c)^n) k) = 0 :=
begin
  induction k with k IH, exfalso, have triv : n ≥ 0, exact bot_le, replace triv : ¬ n < 0, exact not_lt.mpr triv, exact triv hk,
  {
    replace hk : n ≤ k, exact nat.lt_succ_iff.mp hk,
    replace hk : n < k ∨ n = k, exact lt_or_eq_of_le hk,
    cases hk,
    {
      have triv := IH hk,
      rw <-deriv_succ, rw triv, simp only [polynomial.derivative_zero],
    },
    {
      rw <-deriv_succ, rw hk, rw deriv_X_sub_pow, simp only [mul_one, nat.sub_self, polynomial.derivative_C, pow_zero], exact le_refl k,
    },
  },
end


theorem f_p_prod_part1 (p : ℕ) (hp : nat.prime p) (n j : ℕ) (hj : j < p - 1) 
  (k : ℕ) (hk : k.succ ∈ finset.range n.succ) :
  ∀ i:ℕ, (i ∈ finset.range j.succ) ->
          polynomial.eval (k.succ:ℤ) (deriv_n (∏ (i : ℕ) in finset.range n, (polynomial.X - (polynomial.C (i + 1:ℤ))) ^ p) i) = 0 :=
begin
  induction n with n IH, simp only [finset.mem_singleton, finset.range_one] at hk, exfalso, exact nat.succ_ne_zero k hk,
  {
    simp only [finset.mem_range] at hk, replace hk : k.succ ≤ n.succ, exact nat.lt_succ_iff.mp hk, replace hk : k.succ < n.succ ∨ k.succ = n.succ, exact lt_or_eq_of_le hk,
    cases hk, simp only [polynomial.C_add, polynomial.C_1, int.coe_nat_succ, finset.mem_range] at IH, replace IH := IH hk, intros i hi, simp only [finset.mem_range] at hi,
    rw finset.prod_range_succ, rw deriv_n_poly_prod, rw eval_sum', apply finset.sum_eq_zero, intros x hx, simp only [finset.mem_range] at hx,
    have hx' : x < j.succ, {exact gt_of_ge_of_gt hi hx,}, replace hx' := IH x hx', simp only [polynomial.eval_C, polynomial.C_add, int.coe_nat_eq_zero, polynomial.C_1, polynomial.eval_mul, int.coe_nat_succ,
 mul_eq_zero], right, assumption,

    intros x hx, rw finset.prod_range_succ, rw deriv_n_poly_prod, rw eval_sum', apply finset.sum_eq_zero, intros y hy, rw polynomial.eval_mul, simp only [polynomial.eval_C, polynomial.C_add, int.coe_nat_eq_zero, polynomial.C_1, polynomial.eval_mul, int.coe_nat_succ,
 mul_eq_zero],
    left, right, simp only [finset.mem_range] at hx hy,
    have triv : (polynomial.C ↑n + 1) = polynomial.C (n+1:ℤ), {simp only [polynomial.C_add, polynomial.C_1],}, rw triv,
    rw deriv_X_sub_pow p (x-y) (n+1:ℤ), rw polynomial.eval_mul, rw mul_eq_zero, right, rw [nat.succ_eq_add_one,nat.succ_eq_add_one] at hk,
    rw [nat.succ_eq_add_one] at hx hy,
    have triv : (k+1:ℤ)=(n+1:ℤ), {norm_cast, exact hk}, rw triv, simp only [polynomial.eval_X, polynomial.eval_C, polynomial.eval_pow, polynomial.eval_sub, sub_self], rw zero_pow,
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
    simp only [nat.succ_pos', finset.mem_range] at hi hk,
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
    rw deriv_X_pow', rw polynomial.eval_mul, simp only [polynomial.eval_X, polynomial.eval_C, int.coe_nat_zero, polynomial.eval_pow, mul_eq_zero], right, apply zero_pow, 
    exact nat.sub_pos_of_lt ineq,
    exact le_of_lt ineq,
  },

  {
    -- k ≥ 1,
    rw polynomial.eval_mul, rw mul_eq_zero, right,
    have H := f_p_prod_part1 p hp n j hj k, simp only [polynomial.C_add, polynomial.C_1, int.coe_nat_succ, finset.mem_range] at H, simp only [finset.mem_range] at hk, replace H := H hk, simp only [finset.mem_range] at hi,
    replace H := H i hi, simp only [polynomial.C_add, polynomial.C_1, int.coe_nat_succ] at H ⊢, exact H,
  },
end

lemma fact_eq_prod (n : ℕ) : (n.fact:ℤ) = ∏ i in finset.range n, (i+1:ℤ) :=
begin
  induction n with n ih, simp only [int.coe_nat_zero, int.coe_nat_succ, finset.range_zero, finset.prod_empty, zero_add, nat.fact_zero],
  {
    rw nat.fact_succ, rw finset.prod_range_succ, simp only [int.coe_nat_succ, int.coe_nat_mul], rw ih,
  },
end

lemma fact_eq_prod' (n : ℕ) : (n.fact:ℤ) = ∏ i in finset.range n, (n-i:ℤ) :=
begin
  induction n with n ih, simp only [int.coe_nat_zero, int.coe_nat_succ, finset.range_zero, finset.prod_empty, zero_add, nat.fact_zero],
  {
    rw nat.fact_succ, rw finset.prod_range_succ', simp only [int.coe_nat_zero, add_sub_add_right_eq_sub, sub_zero, int.coe_nat_succ, nat.fact, int.coe_nat_mul], rw ih, rw mul_comm,
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
    simp only [polynomial.eval_C, one_mul, nat.choose_zero_right, polynomial.C_add, int.coe_nat_zero, polynomial.C_1,
 polynomial.eval_mul, int.coe_nat_succ, nat.sub_zero, zero_add, finset.sum_singleton, finset.range_one, nat.fact], simp only [zeroth_deriv], rw eval_prod', simp only [polynomial.eval_X, polynomial.eval_C, zero_sub, polynomial.eval_one, polynomial.eval_pow, polynomial.eval_add,
 neg_add_rev, polynomial.eval_sub, nat.fact],
    have eq1 : ∏ (x : ℕ) in finset.range n, (-1 + -(x:ℤ)) ^ p = ∏ (x : ℕ) in finset.range n, (-(1+x)) ^ p,
    {
      apply congr_arg, ext, simp only [neg_add_rev], rw add_comm,
    },
    rw eq1,
    replace eq1 : ∏ (x : ℕ) in finset.range n, (-(1+x:ℤ)) ^ p = ∏ (x : ℕ) in finset.range n, (-1)^p * (1+x:ℤ) ^ p,
    {
      apply congr_arg, ext, rw neg_pow,
    }, rw eq1, rw finset.prod_mul_distrib, simp only [finset.prod_const, finset.card_range], rw <-pow_mul, rw mul_comm p n, rw finset.prod_pow,
    replace eq1 : (∏ (x : ℕ) in finset.range n, (1 + x:ℤ)) = (n.fact:ℤ),
    {
      rw fact_eq_prod, apply congr_arg, ext, rw add_comm,
    }, rw eq1,
    rw deriv_X_pow', rw polynomial.eval_mul, simp only [mul_one, polynomial.eval_C, nat.sub_self, polynomial.eval_one, pow_zero], rw <-fact_eq_prod', exact mul_assoc ↑((p - 1).fact) ((-1) ^ (n * p)) (↑(nat.fact n) ^ p),
    exact le_refl (p - 1),
  },
  rw triv, apply eq.symm, apply finset.sum_subset, simp only [nat.succ_pos', finset.singleton_subset_iff, finset.range_one, finset.mem_range], intros x hx1 hx2,rw deriv_X_pow', rw polynomial.eval_mul, simp only [polynomial.eval_X, polynomial.eval_C, polynomial.C_add, int.coe_nat_eq_zero, polynomial.C_1, polynomial.eval_pow,
 polynomial.eval_mul, mul_eq_zero], left, right, right,
  apply zero_pow, simp only [finset.mem_singleton, finset.range_one, finset.mem_range] at hx1 hx2 ⊢, replace triv : (p-1).succ = p, 
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
    rw f_p_n_succ, rw deriv_n_poly_prod, rw eval_sum', apply finset.sum_eq_zero, intros y hy, simp only [finset.mem_range] at hy,
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
      rw mul_eq_zero, right, rw hx2, rw deriv_X_sub_pow, rw polynomial.eval_mul, rw polynomial.eval_pow, simp only [polynomial.eval_X, polynomial.eval_C, int.coe_nat_succ, polynomial.eval_sub, sub_self, mul_eq_zero], right, apply zero_pow,
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
     simp only [int.coe_nat_zero, finset.sum_singleton, finset.range_one],
  }, rw triv, apply eq.symm, apply finset.sum_subset, simp only [nat.succ_pos', finset.singleton_subset_iff, finset.range_one, finset.mem_range],
  intros x hx1 hx2, simp only [finset.mem_singleton, finset.range_one, finset.mem_range] at hx1 hx2, 
  rw deriv_f_p_sub1, simp only [mul_zero], 
  have triv := @nat.sub_one_sub_lt p 0 _, simp only [nat.sub_zero] at triv, exact triv, exact nat.prime.pos hp, exact bot_lt_iff_ne_bot.mpr hx2, assumption,
end


lemma dvd_iff_mul (m n : ℤ) : n ∣ m ↔ ∃ c : ℤ, m = n * c := iff.rfl

lemma dvd_iff_mul_nat (m n : ℕ) : n ∣ m ↔ ∃ c : ℕ, m = n * c := iff.rfl

private lemma k_eq_0_case (p : ℕ) (hp : nat.prime p) (n:ℕ) : ∀ j : ℕ, j ≥ p -> (p.fact:ℤ) ∣ polynomial.eval 0 (deriv_n (f_p p hp n) j) :=
begin
  rw f_p, intros j j_ge_p, rw deriv_n_poly_prod, rw eval_sum', apply finset.dvd_sum,
  intros x hx, simp only [polynomial.eval_C, polynomial.C_add, polynomial.C_1, polynomial.eval_mul, nat.fact],
  by_cases j - x = p - 1,
  {
    rw h, rw deriv_X_pow', simp only [mul_one, polynomial.eval_C, nat.sub_self, pow_zero],
    rw <-fact_eq_prod',
    suffices : (p:ℤ) ∣ polynomial.eval 0 (deriv_n (∏ (x : ℕ) in finset.range n, (polynomial.X - (polynomial.C ↑x + 1)) ^ p) x),
    {
      -- rw int.dvd at this,
      rw dvd_iff_mul at this, choose c hc using this, rw hc,
      have triv : ↑(j.choose x) * ↑((p - 1).fact) * (↑p * c) = ↑(j.choose x) * (↑((p - 1).fact) * ↑p) * c := by ring,
      rw triv,
      replace triv : ((p - 1).fact:ℤ) * ↑p = (p.fact:ℤ),
      {
        have triv' : p = (p-1).succ, rw nat.sub_one, apply eq.symm, apply nat.succ_pred_eq_of_pos, exact nat.prime.pos hp,
        conv_rhs {rw triv'}, rw nat.fact_succ, rw <-triv', norm_cast, ring,
      },
      rw triv,
      replace triv : ↑(j.choose x) * ↑(p.fact) * c = ↑(p.fact) * (↑(j.choose x) * c),
      {
        ring,
      }, rw triv,
      exact dvd.intro (↑(nat.choose j x) * c) rfl,
    },
    cases x,
    {
      exfalso, simp only [nat.sub_zero] at h, rw h at j_ge_p, have triv : p > p - 1,
      have this := @nat.sub_one_sub_lt p 0 (nat.prime.pos hp), simp only [nat.sub_zero] at this, exact this, linarith,
    },
    {
      rw finset.prod_pow, apply dvd_poly_pow_deriv, exact nat.prime.pos hp, exact nat.succ_pos x,
    },
    exact le_refl (p - 1),
  },
  replace h : j - x < p - 1 ∨ j - x > p - 1, exact lt_or_gt_of_ne h,
  cases h,
  {
    rw deriv_X_pow', rw polynomial.eval_mul, simp only [polynomial.eval_X, polynomial.eval_C, polynomial.eval_pow], rw zero_pow, simp only [zero_mul, mul_zero, dvd_zero], exact nat.sub_pos_of_lt h, exact le_of_lt h,
  },
  {
    rw deriv_X_pow_too_much, simp only [zero_mul, mul_zero, polynomial.eval_zero, dvd_zero], assumption,
  }
end

private lemma j_ge_p_prod_part (p : ℕ) (hp : nat.prime p) : ∀ n : ℕ, ∀ k : ℕ, ∀ x : ℕ,
  k > 0 -> k < n.succ ->
  (p.fact:ℤ) ∣ polynomial.eval (k:ℤ) (deriv_n (∏ i in finset.range n, (polynomial.X - polynomial.C (↑i + 1)) ^ p) x) :=
begin
  intro n,
  induction n with n IHn,
  {
    intros, linarith,
  },
  {
    intros k x hk1 hk2,
    rw finset.prod_range_succ, rw deriv_n_poly_prod, rw eval_sum',
    apply finset.dvd_sum,
    intros y hy, simp only [finset.mem_range] at hy, repeat {rw polynomial.eval_mul,}, rw polynomial.eval_C,
    replace hk2 : k ≤ n.succ, exact nat.lt_succ_iff.mp hk2,
    replace hk2 : k = n.succ ∨ k < n.succ, exact eq_or_lt_of_le hk2,
    cases hk2,
    {
      rw hk2,
      by_cases ineq : (x-y = p),
      {
        rw ineq, rw deriv_X_sub_pow, rw <-fact_eq_prod', simp only [mul_one, polynomial.eval_C, polynomial.C_add, nat.sub_self, polynomial.C_1, int.coe_nat_succ, pow_zero],
        have triv : ↑(x.choose y) * (p.fact:ℤ) * polynomial.eval (↑n + 1)
          (deriv_n (∏ (x : ℕ) in finset.range n, (polynomial.X - (polynomial.C ↑x + 1)) ^ p) y) =
          (p.fact:ℤ) * (↑(x.choose y) * polynomial.eval (↑n + 1)
          (deriv_n (∏ (x : ℕ) in finset.range n, (polynomial.X - (polynomial.C ↑x + 1)) ^ p) y)),
        {
          ring,
        }, rw triv, simp only [dvd_mul_right],
      },
      {
        replace ineq : x - y < p ∨ x - y > p,
        {
          exact lt_or_gt_of_ne ineq,
        },
        cases ineq,
        {
          rw deriv_X_sub_pow, simp only [polynomial.eval_X, polynomial.eval_C, polynomial.C_add, polynomial.C_1, polynomial.eval_one, polynomial.eval_pow,
 polynomial.eval_mul, int.coe_nat_succ, polynomial.eval_add, polynomial.eval_sub, sub_self], rw zero_pow, simp only [zero_mul, mul_zero, dvd_zero], exact nat.sub_pos_of_lt ineq, exact le_of_lt ineq,
        },
        {
          rw deriv_X_sub_pow_too_much, simp only [zero_mul, mul_zero, polynomial.eval_zero, dvd_zero], assumption,
        },
      },
    },

    replace IHn := IHn k y hk1 hk2, apply dvd_mul_of_dvd_right, exact IHn,
  },
end

private lemma k_ge_1_case (p : ℕ) (hp : nat.prime p) (n:ℕ) : ∀ j : ℕ, j ≥ p -> ∀ k : ℕ, k < n.succ -> k > 0 -> (p.fact:ℤ) ∣ polynomial.eval (k:ℤ) (deriv_n (f_p p hp n) j) := 
begin
  {
    intros j j_ge_p, intros k hk1 hk2, rw f_p,
    rw deriv_n_poly_prod, rw eval_sum', apply finset.dvd_sum,
    intros x hx, simp only [finset.mem_range] at hx, repeat {rw polynomial.eval_mul},
    by_cases hj : j - x = p - 1,
    {
      rw hj, rw deriv_X_pow', simp only [mul_one, polynomial.eval_C, polynomial.C_add, nat.sub_self, polynomial.C_1, nat.fact, pow_zero], rw <-fact_eq_prod', rw finset.prod_pow,
      cases x,
      {
        simp only [nat.sub_zero] at hj, rw hj at j_ge_p, have triv : p - 1 < p,
        have ineq := @nat.sub_one_sub_lt p 0 _, simp only [nat.sub_zero] at ineq, exact ineq, exact nat.prime.pos hp, exfalso,
        replace triv : ¬ (p - 1 ≥ p), exact not_le.mpr triv, exact triv j_ge_p,
      },
      have H := dvd_poly_pow_deriv (∏ (x : ℕ) in finset.range n, (polynomial.X - (polynomial.C ↑x + 1))) p x.succ (k:ℤ) _ _, rw dvd_iff_mul at H, 
      choose c hc using H, rw hc,
      have triv : ↑(j.choose x.succ) * ↑((p - 1).fact) * (↑p * c) = ((p-1).fact * p:ℤ) * ((j.choose x.succ) * c), ring, rw triv,
      replace triv : ((p-1).fact * p:ℤ) = ↑p.fact,
      {
        suffices : p = (p-1).succ,
        {
          conv_rhs {rw this}, rw nat.fact_succ, rw <-this, norm_cast, rw mul_comm,
        },
        rw nat.sub_one, apply eq.symm, apply nat.succ_pred_eq_of_pos, exact nat.prime.pos hp,
      },
      rw triv, simp only [dvd_mul_right], exact nat.prime.pos hp, exact nat.succ_pos x, exact le_refl _,
    },
    {
      replace hj : j - x < p - 1 ∨ j - x > p - 1,
      {
        exact lt_or_gt_of_ne hj,
      },
      cases hj,
      {
        apply dvd_mul_of_dvd_right,
        have H := j_ge_p_prod_part p hp n k x hk2 hk1, exact H,
      },
      {
        rw deriv_X_pow_too_much, simp only [zero_mul, mul_zero, polynomial.eval_zero, dvd_zero], assumption,
      },
    },
  },
end

theorem when_j_ge_p_k (p : ℕ) (hp : nat.prime p) (n:ℕ) : ∀ j : ℕ, j ≥ p -> ∀ k : ℕ, k ∈ finset.range n.succ -> (p.fact:ℤ) ∣ polynomial.eval (k:ℤ) (deriv_n (f_p p hp n) j) :=
begin
  intros j j_ge_p k hk,
  simp only [finset.mem_range] at hk,
  cases k,
  {
    exact k_eq_0_case p hp n j j_ge_p,
  },
  {
    refine k_ge_1_case p hp n j j_ge_p k.succ hk _, exact nat.succ_pos k,
  }
end


private lemma p_sub_one_le (p m : ℕ) (hp : nat.prime p) : p - 1 ≤ m.succ * p - 1 :=
begin
  induction m with m IH, simp only [one_mul], rw nat.succ_eq_add_one, rw add_mul, simp only [one_mul],
  suffices : m.succ * p - 1 ≤ m.succ * p + p - 1,
  {
    exact le_trans IH this,
  },
  have triv : m.succ * p + p - 1 = m.succ * p - 1 + p,
  {
    rw nat.sub_add_comm, apply nat.mul_pos, exact nat.succ_pos m, exact nat.prime.pos hp,
  },
  rw triv, suffices : p ≥ 0, exact nat.le.intro rfl, exact bot_le,
end

theorem J_eq_final (g : polynomial ℤ) (e_root_g : (polynomial.aeval ℤ ℝ e) g = 0) 
             (p : ℕ) (hp : nat.prime p) : ∃ M : ℤ, (J g p hp) = ℤembℝ ((-(g.coeff 0 * (↑((p - 1).fact) * (-1) ^ (g.nat_degree * p) * ↑(g.nat_degree.fact) ^ p))) + (p.fact:ℤ) * M) :=
begin
  have J_eq := J_eq'' g e_root_g p hp, rw J_eq, rw <-ring_hom.map_neg,
  suffices : ∃ (M : ℤ),
        (-∑ (j : ℕ) in
             finset.range (f_p p hp g.nat_degree).nat_degree.succ,
             ∑ (k : ℕ) in
               finset.range g.nat_degree.succ,
               g.coeff k * polynomial.eval ↑k (deriv_n (f_p p hp g.nat_degree) j)) =
       -(g.coeff 0 * (↑((p - 1).fact) * (-1) ^ (g.nat_degree * p) * ↑(g.nat_degree.fact) ^ p)) + (p.fact:ℤ) * M,
  {
    choose M hM using this, use M, apply congr_arg, rw hM,
  },
  generalize m_def : (f_p p hp g.nat_degree).nat_degree = m,
  have hm := deg_f_p p hp g.nat_degree,
  rw m_def at hm,
  have seteq : finset.range m.succ = finset.range (p-1) ∪ {p-1} ∪ finset.Ico p m.succ,
  {
    ext, split,
    {
      intros ha, simp only [finset.mem_range] at ha,
      by_cases (a < p - 1),
      simp only [finset.Ico.mem, finset.mem_union, finset.union_assoc, finset.mem_singleton, finset.mem_range], left, exact h,
      replace h : a ≥ p - 1, exact not_lt.mp h, replace h : p - 1 = a ∨ a > p - 1, exact eq_or_lt_of_le h, simp only [finset.Ico.mem, finset.mem_union, finset.union_assoc, finset.mem_singleton, finset.mem_range],
      cases h,
      {
        right, left, exact eq.symm h,
      },
      {
        right, right, split, exact nat.le_of_pred_lt h, assumption,
      }
    },
    {
      intros ha, simp only [finset.Ico.mem, finset.mem_union, finset.union_assoc, finset.mem_singleton, finset.mem_range] at ha ⊢,
      cases ha,
      have triv : p - 1 ≤ m, rw hm, apply p_sub_one_le, exact hp,
      {
        have ineq := lt_of_lt_of_le ha triv, exact nat.lt.step ineq,
      },
      cases ha,
      {
        rw ha, have triv : p - 1 ≤ m, rw hm, apply p_sub_one_le, exact hp, exact nat.lt_succ_iff.mpr triv,
      },
      exact ha.2,
    },
  },
  rw seteq, rw finset.sum_union, rw finset.sum_union, 
  have eq1 : ∑ (x : ℕ) in
                 finset.range (p - 1),
                 ∑ (k : ℕ) in
                   finset.range g.nat_degree.succ,
                   g.coeff k * polynomial.eval ↑k (deriv_n (f_p p hp g.nat_degree) x) = 0,
  {
    rw finset.sum_eq_zero, intros, rw finset.sum_eq_zero, intros,
    rw mul_eq_zero, right, rw deriv_f_p_k1, simp only [finset.mem_range] at H, exact H, exact H_1,
  }, rw eq1, rw zero_add, rw finset.sum_singleton,

  have eq2 := when_j_eq_p_sub1 p hp g,
  have eq2' := deriv_f_p_p_sub1_0 p hp g.nat_degree, rw eq2' at eq2, rw eq2,

  -- have eq3 := when_j_ge_p_k,
  have H3 :  (p.fact:ℤ) ∣ ∑ (x : ℕ) in
               finset.Ico p m.succ,
               ∑ (k : ℕ) in
                 finset.range g.nat_degree.succ,
                 g.coeff k * polynomial.eval (k:ℤ) (deriv_n (f_p p hp g.nat_degree) x),
  {
    apply finset.dvd_sum, intros x hx, apply finset.dvd_sum, intros y hy,
    apply dvd_mul_of_dvd_right,
    apply when_j_ge_p_k, simp only [finset.Ico.mem] at hx, exact hx.1, exact hy,
  },

  rw dvd_iff_mul at H3,
  choose c eq3 using H3, rw eq3, rw neg_add, use -c, rw neg_mul_eq_mul_neg ↑(p.fact),
  
  {
    rw finset.disjoint_iff_inter_eq_empty, simp only [finset.not_mem_range_self, not_false_iff, finset.inter_singleton_of_not_mem],
  },
  {
    rw finset.disjoint_iff_inter_eq_empty, rw finset.eq_empty_iff_forall_not_mem, intros, intro rid, simp only [finset.Ico.mem, finset.mem_union, finset.mem_singleton, finset.mem_range, finset.mem_inter] at rid,
    have h1 := rid.1, have h2 := rid.2.1, have h3 := rid.2.2, cases h1,
    {
      have contra : p < p - 1, exact gt_of_gt_of_ge h1 h2, 
      replace contra : ¬ (p ≥  p - 1), exact not_le.mpr contra, have triv : p ≥ p - 1, exact nat.sub_le p 1, exact contra triv,
    },
    {
      rw h1 at h2,
      have triv : p > p - 1, have rid := @nat.sub_one_sub_lt p 0 (nat.prime.pos hp), simp only [nat.sub_zero] at rid, exact rid, have rid : p < p,
      exact gt_of_gt_of_ge triv h2, exact lt_irrefl p rid,
    },
  },
end

private lemma coe_abs_ineq (z1 z2 : ℤ) : z1 ≤ abs z2 -> (z1:ℝ) ≤ abs(ℤembℝ z2) :=
begin
  intros, simp only [ring_hom.eq_int_cast], norm_cast, exact a,
end

theorem abs_J_ineq2 (g : polynomial ℤ) (e_root_g : (polynomial.aeval ℤ ℝ e) g = 0) (coeff_nonzero : (g.coeff 0) ≠ 0)(p : ℕ) (hp : nat.prime p) (hp2 : p > g.nat_degree ∧ p > (g.coeff 0).nat_abs) : ((p-1).fact:ℝ) ≤ (abs (J g p hp)) :=
begin
  have J_eq := J_eq_final g e_root_g p hp,
  choose c eq1 using J_eq, rw eq1, 
  have H := coe_abs_ineq ((p-1).fact:ℤ) (-(g.coeff 0 * (↑((p - 1).fact) * (-1) ^ (g.nat_degree * p) * ↑(g.nat_degree.fact) ^ p)) + ↑(p.fact) * c) _, conv_lhs at H {simp only [int.cast_coe_nat, int.cast_pow, int.cast_add, ring_hom.eq_int_cast, int.cast_mul, int.cast_one, ne.def, triv,
 not_false_iff, neg_eq_zero, one_ne_zero, int.cast_neg, int.coe_nat_mul],}, exact H,
  norm_cast,

  have triv : p = (p-1).succ, rw nat.sub_one, rw nat.succ_pred_eq_of_pos, exact nat.prime.pos hp,
  replace triv : p.fact = (p-1).fact * p, conv_lhs {rw triv,}, rw nat.fact_succ, rw <-triv, rw mul_comm, rw triv,

  rw neg_mul_eq_mul_neg, rw neg_mul_eq_mul_neg,
  
  have eq2 : (g.coeff 0 * (↑((p - 1).fact) * (-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.fact ^ p)) +
         ↑((p - 1).fact * p) * c) = 
         ((p - 1).fact:ℤ) * ((g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.fact ^ p))) + (↑p*c)),
  {
    rw mul_add, 
    have triv1 : g.coeff 0 * (↑((p - 1).fact) * (-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.fact ^ p)) = ↑((p - 1).fact) * (g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.fact ^ p))),
    {
      ring,
    },
    rw triv1,
    replace triv1 : ↑((p - 1).fact * p) * c = ↑((p - 1).fact) * (↑p * c), simp only [int.coe_nat_mul], ring, rw triv1,
  },
  rw eq2, rw abs_mul,
  have triv : abs ↑((p - 1).fact) = ((p-1).fact:ℤ),
  {
    apply abs_of_pos, norm_cast, exact (p - 1).fact_pos,
  }, rw triv,
  suffices : 1 ≤ abs (g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.fact ^ p)) + ↑p * c),
  {
    have triv : ((p - 1).fact:ℤ) = ↑((p - 1).fact) * 1, simp only [mul_one], conv_lhs {rw triv,}, apply mul_le_mul, exact le_refl ↑((p - 1).fact),
    assumption, exact trivial, norm_cast, exact bot_le,
  },

  suffices : 0 < abs (g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.fact ^ p)) + ↑p * c),
  {
    exact this,
  },
  rw abs_pos_iff, intro rid,
  have rid2 : (p:ℤ) ∣ g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.fact ^ p)) + ↑p * c,
  rw rid, exact dvd_zero ↑p,
  
  replace rid2 : (p:ℤ) ∣ g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.fact ^ p)),
  {
    refine (dvd_add_iff_left _).2 rid2, exact dvd.intro c rfl,
  },
  have triv : (-1:ℤ) ^ (g.nat_degree * p) = 1 ∨ (-1:ℤ) ^ (g.nat_degree * p) = -1,
  {
    apply neg_one_pow_eq_or,
  },
  cases triv,
  {
    rw triv_1 at rid2, simp only [one_mul, int.coe_nat_pow, dvd_neg, int.mul_neg_eq_neg_mul_symm] at rid2,
    replace rid2 := int.dvd_nat_abs_of_of_nat_dvd rid2,
    rw int.nat_abs_mul at rid2,
    rw nat.prime.dvd_mul at rid2,
    cases rid2,
    {
      have ineq1 : (g.coeff 0).nat_abs > 0,
      {
        apply int.nat_abs_pos_of_ne_zero, exact coeff_nonzero,
      },

      rw dvd_iff_mul_nat at rid2, choose m hm using rid2,
      cases m,
      {
        rw mul_zero at hm, linarith,
      },
      {
        have ineq2 : p * m.succ ≥ p, exact nat.le_add_left p (nat.mul p m), rw <-hm at ineq2,
        have contra : ¬(p > (g.coeff 0).nat_abs), exact not_lt.mpr ineq2, exact contra hp2.2,
      },
    },
    {
      rw int.nat_abs_pow at rid2,
      have H := nat.prime.dvd_of_dvd_pow hp rid2,
      have eq1 : (g.nat_degree.fact:ℤ).nat_abs = g.nat_degree.fact,
      {
        suffices : ((g.nat_degree.fact:ℤ).nat_abs:ℤ)= (g.nat_degree.fact:ℤ), norm_cast, rw <-int.abs_eq_nat_abs,
        rw abs_of_pos, norm_cast, exact (polynomial.nat_degree g).fact_pos,
      }, rw eq1 at H,
      rw nat.prime.dvd_fact at H,
      replace H : ¬(p > g.nat_degree), exact not_lt.mpr H, exact H hp2.1, exact hp,
    },
    exact hp,
  },
  {
    rw triv_1 at rid2, simp only [int.neg_mul_eq_neg_mul_symm, one_mul, int.coe_nat_pow, neg_neg] at rid2,
    replace rid2 := int.dvd_nat_abs_of_of_nat_dvd rid2,
    rw int.nat_abs_mul at rid2,
    rw nat.prime.dvd_mul at rid2,
    cases rid2,
    {
      have ineq1 : (g.coeff 0).nat_abs > 0,
      {
        apply int.nat_abs_pos_of_ne_zero, exact coeff_nonzero,
      },

      rw dvd_iff_mul_nat at rid2, choose m hm using rid2,
      cases m,
      {
        rw mul_zero at hm, linarith,
      },
      {
        have ineq2 : p * m.succ ≥ p, exact nat.le_add_left p (nat.mul p m), rw <-hm at ineq2,
        have contra : ¬(p > (g.coeff 0).nat_abs), exact not_lt.mpr ineq2, exact contra hp2.2,
      },
    },
    {
      rw int.nat_abs_pow at rid2,
      have H := nat.prime.dvd_of_dvd_pow hp rid2,
      have eq1 : (g.nat_degree.fact:ℤ).nat_abs = g.nat_degree.fact,
      {
        suffices : ((g.nat_degree.fact:ℤ).nat_abs:ℤ)= (g.nat_degree.fact:ℤ), norm_cast, rw <-int.abs_eq_nat_abs,
        rw abs_of_pos, norm_cast, exact (polynomial.nat_degree g).fact_pos,
      }, rw eq1 at H,
      rw nat.prime.dvd_fact at H,
      replace H : ¬(p > g.nat_degree), exact not_lt.mpr H, exact H hp2.1, exact hp,
    },
    exact hp,
  },
  
end


lemma abs_sum_le_sum_abs' {f : (ℕ×ℕ) → ℤ} {s : finset (ℕ×ℕ)} :
  abs (∑ x in s, f x) ≤ ∑ x in s, abs (f x) :=
begin
  apply finset.induction_on s, simp only [],
  {
    intros a s ha H,
    rw finset.sum_insert, rw finset.sum_insert,
    have triv := @abs_add ℤ _ (f a) (∑ (x : ℕ × ℕ) in s, f x),
    have triv2 : abs (f a) + abs (∑ (x : ℕ × ℕ) in s, f x) ≤ abs (f a) + (∑ (x : ℕ × ℕ) in s, abs (f x)), exact add_le_add_left H (abs (f a)),
    exact le_trans triv triv2, assumption, assumption,
  },
end

theorem eval_f_bar_mul (f g : polynomial ℤ) (k : ℕ) : polynomial.eval (k:ℤ) (f_bar (f * g)) ≤ (polynomial.eval (k:ℤ) (f_bar f)) * (polynomial.eval (k:ℤ) (f_bar g)) :=
begin
  by_cases (f=0 ∨ g=0),
  {
    cases h, rw h, simp only [f_bar_0, zero_mul, polynomial.eval_zero], rw h, simp only [f_bar_0, mul_zero, polynomial.eval_zero],
  },
  replace h := not_or_distrib.1 h,
  {
    rw polynomial.as_sum (f_bar (f*g)), rw eval_sum', rw bar_same_deg, rw <-polynomial.eval_mul,
    rw polynomial.as_sum ((f_bar f)*(f_bar g)),
    have deg_eq : (f_bar f * f_bar g).nat_degree = f.nat_degree + g.nat_degree,
    {
      rw polynomial.nat_degree_mul_eq, rw bar_same_deg, rw bar_same_deg, intro rid, exact h.1 (f_bar_eq_0 f rid), intro rid, exact h.2 (f_bar_eq_0 g rid),
    },
    rw deg_eq,
    replace deg_eq : (f * g).nat_degree = f.nat_degree + g.nat_degree,
    {
      rw polynomial.nat_degree_mul_eq, intro rid, exact h.1 rid, intro rid, exact h.2 rid,
    },
    rw deg_eq, rw eval_sum', apply finset.sum_le_sum,
    intros x hx, simp only [polynomial.eval_X, polynomial.eval_C, polynomial.eval_pow, polynomial.eval_mul], rw coeff_f_bar_mul, rw polynomial.coeff_mul,
    cases k, cases x, simp only [mul_one, finset.nat.antidiagonal_zero, finset.sum_singleton, pow_zero], rw bar_coeff, rw bar_coeff, rw abs_mul, simp only [int.coe_nat_zero], rw zero_pow, simp only [mul_zero], exact nat.succ_pos x,
    have ineq : abs (∑ (p : ℕ × ℕ) in finset.nat.antidiagonal x, f.coeff p.fst * g.coeff p.snd) ≤ 
                ∑ (p : ℕ × ℕ) in finset.nat.antidiagonal x, abs(f.coeff p.fst * g.coeff p.snd),
    {
      apply abs_sum_le_sum_abs',
    }, 
    have triv : ∑ (p : ℕ × ℕ) in finset.nat.antidiagonal x, abs(f.coeff p.fst * g.coeff p.snd) = ∑ (p : ℕ × ℕ) in finset.nat.antidiagonal x, abs(f.coeff p.fst) * abs(g.coeff p.snd),
    {
      apply congr_arg, ext, rw abs_mul,
    },
    rw triv at ineq,
    apply mul_le_mul, exact ineq, exact le_refl (↑(nat.succ k) ^ x), apply pow_nonneg, norm_cast, exact bot_le,
    apply finset.sum_nonneg, intros, rw bar_coeff, rw bar_coeff, rw <-abs_mul, exact abs_nonneg (polynomial.coeff f x_1.fst * polynomial.coeff g x_1.snd),
  },
end


lemma f_bar_1 : f_bar 1 = 1 :=
begin
  ext, simp only [bar_coeff, polynomial.coeff_one], split_ifs, exact rfl, exact rfl,
end


lemma eval_f_bar_nonneg (f : polynomial ℤ) (i:ℕ) : polynomial.eval (i:ℤ) (f_bar f) ≥ 0 :=
begin
    rw f_bar_eq, rw eval_sum', apply finset.sum_nonneg, intros, simp only [polynomial.eval_X, polynomial.eval_C, polynomial.eval_pow, polynomial.eval_mul], apply mul_nonneg, exact abs_nonneg (polynomial.coeff f x), exact pow_nonneg trivial x,
end

theorem eval_f_bar_pow (f : polynomial ℤ) (k n : ℕ) : polynomial.eval (k:ℤ) (f_bar (f^n)) ≤ (polynomial.eval (k:ℤ) (f_bar f))^n :=
begin
  induction n with n H,
  simp only [f_bar_1, polynomial.eval_one, pow_zero],
  rw pow_succ, have ineq := eval_f_bar_mul f (f^n) k,
  have ineq2 : polynomial.eval ↑k (f_bar f) * polynomial.eval ↑k (f_bar (f ^ n)) ≤  polynomial.eval ↑k (f_bar f) * polynomial.eval ↑k (f_bar f) ^ n,
  {
    apply mul_le_mul, exact le_refl (polynomial.eval ↑k (f_bar f)), exact H, exact eval_f_bar_nonneg (f ^ n) k, exact eval_f_bar_nonneg f k,
  },
  exact le_trans ineq ineq2,
end

theorem eval_f_bar_prod (f : ℕ -> polynomial ℤ) (k : ℕ) (s:finset ℕ): polynomial.eval (k:ℤ) (f_bar (∏ i in s, (f i))) ≤ (∏ i in s, polynomial.eval (k:ℤ) (f_bar (f i))) :=
begin
  apply finset.induction_on s, simp only [f_bar_1, polynomial.eval_one, finset.prod_empty],
  intros a s ha H, rw finset.prod_insert, rw finset.prod_insert,
  have ineq := eval_f_bar_mul (f a) (∏ (x : ℕ) in s, f x) k,
  have ineq2 : polynomial.eval ↑k (f_bar (f a)) * polynomial.eval ↑k (f_bar (∏ (x : ℕ) in s, f x)) ≤
    polynomial.eval ↑k (f_bar (f a)) * ∏ (i : ℕ) in s, polynomial.eval ↑k (f_bar (f i)),
  {
    apply mul_le_mul, exact le_refl _, exact H, exact eval_f_bar_nonneg (∏ (x : ℕ) in s, f x) k, exact eval_f_bar_nonneg (f a) k,
  },
  exact le_trans ineq ineq2, assumption, assumption,
end


theorem abs_J_ineq1' (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) :
  abs (J g p hp) ≤ ∑ i in finset.range g.nat_degree.succ, (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * (f_eval_on_ℝ (f_bar (f_p p hp g.nat_degree)) (i:ℝ)) :=
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

private lemma coe_sum (s : finset ℕ) (f : ℕ -> ℤ) : ↑(∑ i in s, f i) = (∑ i in s, ((f i):ℝ)) :=
begin
  apply finset.induction_on s, simp only [int.cast_zero, finset.sum_empty], intros a s ha H, rw finset.sum_insert, simp only [int.cast_add], rw H, rw finset.sum_insert, assumption, assumption,
end

lemma coe_f_eval (f : polynomial ℤ) (i : ℕ) : f_eval_on_ℝ f (i:ℝ) = ((@polynomial.eval ℤ _ (i : ℤ) f):ℝ) :=
begin
  simp only [f_eval_on_ℝ, polynomial.eval_map], rw polynomial.eval, rw polynomial.eval₂, rw polynomial.eval₂, rw finsupp.sum, rw finsupp.sum, rw coe_sum,

  apply finset.sum_congr, refl, intros, simp only [int.cast_coe_nat, int.cast_pow, ring_hom.eq_int_cast, id.def, int.cast_mul], norm_cast,
end

private lemma f_bar_X_pow {n : ℕ} : f_bar (polynomial.X ^ n) = polynomial.X^n :=
begin
  ext, rw bar_coeff, simp only [polynomial.coeff_X_pow], split_ifs, exact rfl, exact rfl,
end

private lemma f_bar_X_sub_pow (n k : ℕ) (c:ℕ) : polynomial.eval (k:ℤ) (f_bar ((polynomial.X - polynomial.C (c:ℤ))^n)) ≤ polynomial.eval (k:ℤ) (polynomial.X + polynomial.C (c:ℤ))^n :=
begin
  induction n with n hn, simp only [pow_zero], rw f_bar_1, simp only [polynomial.eval_one],
  rw pow_succ,
  have ineq1 := eval_f_bar_mul (polynomial.X - polynomial.C (c:ℤ)) ((polynomial.X - polynomial.C (c:ℤ)) ^ n) k,
  have id1 : f_bar (polynomial.X - polynomial.C ↑c) = polynomial.X + polynomial.C (c:ℤ),
  {
    ext, rw bar_coeff, simp only [polynomial.coeff_add, polynomial.coeff_sub], rw polynomial.coeff_X, split_ifs, rw <-h, rw polynomial.coeff_C, split_ifs, exfalso, linarith, simp only [add_zero, sub_zero, abs_one],
    simp only [zero_sub, abs_neg, zero_add], rw polynomial.coeff_C, split_ifs, apply abs_of_nonneg, simp only [], simp only [abs_zero], 
  },
  rw id1 at ineq1,
  rw pow_succ, 
  have ineq2 : polynomial.eval ↑k (polynomial.X + polynomial.C ↑c) *
      polynomial.eval ↑k (f_bar ((polynomial.X - polynomial.C ↑c) ^ n)) ≤ 
      polynomial.eval ↑k (polynomial.X + polynomial.C ↑c) * polynomial.eval ↑k (polynomial.X + polynomial.C ↑c) ^ n,
  {
    apply mul_le_mul, exact le_refl (polynomial.eval ↑k (polynomial.X + polynomial.C ↑c)), exact hn, exact eval_f_bar_nonneg ((polynomial.X - polynomial.C ↑c) ^ n) k,
    simp only [polynomial.eval_X, polynomial.eval_C, polynomial.eval_add],
  },
  exact le_trans ineq1 ineq2,
end

lemma f_p_est (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) (j:ℕ) (hi : j ∈ finset.range g.nat_degree.succ) : @polynomial.eval ℤ _ (j:ℤ) (f_bar (f_p p hp g.nat_degree)) ≤ (2 * ↑(g.nat_degree.succ)) ^ (p + p * g.nat_degree) :=
begin
  simp only [finset.mem_range] at hi,
  rw f_p,
  have ineq1 := eval_f_bar_mul (polynomial.X ^ (p - 1)) (∏ (i : ℕ) in finset.range g.nat_degree, (polynomial.X - polynomial.C (↑i + 1)) ^ p) j,
  rw f_bar_X_pow at ineq1,
  have triv : (polynomial.eval (j:ℤ) (polynomial.X ^ (p - 1))) = (↑j)^(p-1),
  {
    simp only [polynomial.eval_X, polynomial.eval_pow],
  },
  rw triv at ineq1,
  replace triv : (j:ℤ)^(p-1) < (2*↑g.nat_degree.succ)^(p-1),
  {
    norm_cast, apply nat.pow_lt_pow_of_lt_left,
    have ineq : 1 * g.nat_degree.succ ≤ 2 * g.nat_degree.succ,
    {
      apply mul_le_mul, exact one_le_two, exact le_refl _, exact bot_le, exact bot_le,
    }, rw one_mul at ineq, exact gt_of_ge_of_gt ineq hi,
    exact nat.prime.pred_pos hp,
  },
  have triv' : (2*g.nat_degree.succ:ℤ)^(p-1) ≤ (2*g.nat_degree.succ:ℤ)^p,
  {
    norm_cast, have ineq := (@pow_le_pow ℕ _ (2*g.nat_degree.succ) (p-1) p) _ _, simp only [nat.pow_eq_pow] at ineq ⊢, exact ineq, exact inf_eq_left.mp rfl,
    exact nat.sub_le p 1,
  },
  replace triv : (j:ℤ)^(p-1) < (2*g.nat_degree.succ:ℤ)^p,
  {
    exact gt_of_ge_of_gt triv' triv,
  },

  have ineq2 : (j:ℤ) ^ (p - 1) * polynomial.eval ↑j (f_bar (∏ (i : ℕ) in finset.range g.nat_degree,(polynomial.X - polynomial.C (↑i + 1)) ^ p)) ≤
              (2*g.nat_degree.succ:ℤ)^p * polynomial.eval ↑j
        (f_bar (∏ (i : ℕ) in finset.range g.nat_degree, (polynomial.X - polynomial.C (↑i + 1)) ^ p)),
  {
    apply mul_le_mul, exact le_of_lt triv, exact le_refl
  (polynomial.eval ↑j
     (f_bar (∏ (i : ℕ) in finset.range (polynomial.nat_degree g), (polynomial.X - polynomial.C (↑i + 1)) ^ p))),
     exact eval_f_bar_nonneg (∏ (i : ℕ) in finset.range g.nat_degree, (polynomial.X - polynomial.C (↑i + 1)) ^ p) j, norm_cast, exact bot_le,
  },

  replace ineq1 : polynomial.eval (j:ℤ)
      (f_bar
         (polynomial.X ^ (p - 1) *
            ∏ (i : ℕ) in finset.range g.nat_degree, (polynomial.X - polynomial.C (i + 1:ℤ)) ^ p)) ≤ 
      (2*g.nat_degree.succ:ℤ) ^ p *
      polynomial.eval (j:ℤ)
        (f_bar (∏ (i : ℕ) in finset.range g.nat_degree, (polynomial.X - polynomial.C (↑i + 1)) ^ p)),
  {
    exact le_trans ineq1 ineq2,
  },

  replace ineq2 :
    polynomial.eval (j:ℤ)
        (f_bar (∏ (i : ℕ) in finset.range g.nat_degree, (polynomial.X - polynomial.C (↑i + 1)) ^ p)) ≤
    (∏ i in finset.range g.nat_degree, polynomial.eval (j:ℤ) (f_bar ((polynomial.X - polynomial.C (↑i+1))^p))),
  {
    apply eval_f_bar_prod,
  },

  have ineq3 : (∏ i in finset.range g.nat_degree, polynomial.eval (j:ℤ) (f_bar ((polynomial.X - polynomial.C (↑i+1))^p))) ≤ 
    (∏ i in finset.range g.nat_degree, polynomial.eval (j:ℤ) (f_bar ((polynomial.X - polynomial.C (↑i+1))))^p),
  {
    apply finset.prod_le_prod, intros, exact eval_f_bar_nonneg ((polynomial.X - polynomial.C (↑x + 1)) ^ p) j,
    intros, exact eval_f_bar_pow (polynomial.X - polynomial.C (↑x + 1)) j p,
  },

  have ineq4 : (∏ i in finset.range g.nat_degree, polynomial.eval (j:ℤ) (f_bar ((polynomial.X - polynomial.C (↑i+1))))^p) ≤
  (∏ i in finset.range g.nat_degree, (polynomial.eval (j:ℤ) (polynomial.X + polynomial.C (↑i+1)))^p),
  {
    apply finset.prod_le_prod, intros, exact pow_nonneg (eval_f_bar_nonneg (polynomial.X - polynomial.C (↑x + 1)) j) p, intros,
    have : (f_bar (polynomial.X - polynomial.C (x + 1:ℤ))) = polynomial.X + polynomial.C (x+1:ℤ),
    {
      ext, simp only [bar_coeff, polynomial.coeff_X, polynomial.coeff_C, polynomial.C_add, polynomial.coeff_add, polynomial.coeff_one,
 polynomial.C_1, polynomial.coeff_sub], split_ifs, rw h_1 at h, linarith, exfalso, linarith, linarith, simp only [add_zero, sub_zero, abs_one], rw zero_sub, rw abs_neg, simp only [zero_add],
      rw abs_of_nonneg, norm_cast, exact bot_le, rw zero_sub, rw abs_neg, rw zero_add, apply abs_of_nonneg, norm_cast, simp only [zero_le],
      exfalso, exact h_1 (eq.symm h_2), simp only [add_zero, sub_zero, abs_zero],
    },
    rw this,
  },

  have eq1 : (∏ i in finset.range g.nat_degree, (polynomial.eval (j:ℤ) (polynomial.X + polynomial.C (↑i+1)))^p) =
    (∏ i in finset.range g.nat_degree, (j+i+1:ℤ)^p),
  {
    apply finset.prod_congr, refl, intros, simp only [polynomial.eval_X, polynomial.eval_C, polynomial.eval_add], apply congr_arg, refl,
  },
  rw eq1 at ineq4,

  have ineq4' : (∏ i in finset.range g.nat_degree, (j+i+1:ℤ)^p) ≤ (∏ i in finset.range g.nat_degree, (2*g.nat_degree.succ:ℤ)^p),
  {
    apply finset.prod_le_prod, intros, norm_cast, exact bot_le, intros, norm_cast, apply nat.pow_le_pow_of_le_left, rw two_mul, simp only [finset.mem_range] at H,
    rw add_assoc, apply add_le_add, exact le_of_lt hi, exact nat.le_succ_of_le H,
  },

  have eq2 : (∏ i in finset.range g.nat_degree, (2*g.nat_degree.succ:ℤ)^p) = (2*g.nat_degree.succ:ℤ)^(p*g.nat_degree),
  {
    rw finset.prod_const, simp only [int.coe_nat_succ, finset.card_range], rw pow_mul,
  },

  rw eq2 at ineq4',
  replace ineq4 := le_trans ineq4 ineq4',

  have ineq5 : (2 * ↑(g.nat_degree.succ)) ^ p *
      (polynomial.eval ↑j
        (f_bar (∏ (i : ℕ) in finset.range g.nat_degree, (polynomial.X - polynomial.C (↑i + 1)) ^ p))) ≤
      (2 * ↑(g.nat_degree.succ)) ^ p * ∏ (i : ℕ) in finset.range g.nat_degree,
        polynomial.eval ↑j (f_bar ((polynomial.X - polynomial.C (↑i + 1)) ^ p)),

  {
    apply mul_le_mul, exact le_refl ((2 * ↑((polynomial.nat_degree g).succ)) ^ p), exact ineq2, exact eval_f_bar_nonneg (∏ (i : ℕ) in finset.range g.nat_degree, (polynomial.X - polynomial.C (↑i + 1)) ^ p) j,
    norm_cast, exact bot_le,
  },

  have ineq6 : (2 * ↑(g.nat_degree.succ)) ^ p * ∏ (i : ℕ) in finset.range g.nat_degree,
        polynomial.eval ↑j (f_bar ((polynomial.X - polynomial.C (i + 1:ℤ)) ^ p)) ≤ 
        (2 * ↑(g.nat_degree.succ)) ^ p * (2 * ↑(g.nat_degree.succ)) ^ (p * g.nat_degree),
  {
    apply mul_le_mul, exact le_refl ((2 * ↑((polynomial.nat_degree g).succ)) ^ p), exact le_trans ineq3 ineq4,
    apply finset.prod_nonneg, intros, exact eval_f_bar_nonneg ((polynomial.X - polynomial.C (↑x + 1)) ^ p) j,
    norm_cast, exact bot_le,
  },

  rw <-pow_add at ineq6,
  exact le_trans ineq1 (le_trans ineq5 ineq6),
end

def set_of_abs_coeff (g : polynomial ℤ) : finset ℤ := finset.image (λ i : ℕ, abs (g.coeff i)) g.support
def set_of_1_abs_coeff (g : polynomial ℤ) : finset ℤ := insert 1 (set_of_abs_coeff g)
theorem set_of_1_abs_coeff_nonempty (g : polynomial ℤ) : finset.nonempty (set_of_1_abs_coeff g) :=
begin
  rw set_of_1_abs_coeff, use 1, simp only [true_or, eq_self_iff_true, finset.mem_insert],
end

def max_abs_coeff_1 (g : polynomial ℤ) := finset.max' (set_of_1_abs_coeff g) (set_of_1_abs_coeff_nonempty g)
lemma max_abs_coeff_1_ge_1 (g : polynomial ℤ) : 1 ≤ max_abs_coeff_1 g :=
begin
  rw max_abs_coeff_1, apply finset.le_max', rw set_of_1_abs_coeff, simp only [true_or, eq_self_iff_true, finset.mem_insert],
end


private lemma abs_J_ineq1'_coe (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) : 
  (∑ i in finset.range g.nat_degree.succ, 
    (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * (f_eval_on_ℝ (f_bar (f_p p hp g.nat_degree)) (i:ℝ))) =
 ((∑ i in finset.range g.nat_degree.succ, 
  (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * ((@polynomial.eval ℤ _ (i:ℤ) (f_bar (f_p p hp g.nat_degree)):ℝ)))) :=
begin
  apply finset.sum_congr, refl, intros,
  suffices : f_eval_on_ℝ (f_bar (f_p p hp g.nat_degree)) (x:ℝ) = ((@polynomial.eval ℤ _ (x:ℤ) (f_bar (f_p p hp g.nat_degree))):ℝ),
  {
    rw this,
  },
  rw coe_f_eval,
end

lemma nat_mul_real (n:ℕ) (r:ℝ) : n •ℕ r = (n:ℝ) * r :=
begin
  induction n with n hn, simp only [nat.cast_zero, zero_mul, zero_nsmul],
  rw succ_nsmul, rw hn, rw nat.succ_eq_add_one, norm_num, ring,
end


lemma abs_J_ineq1'' (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) :
  abs (J g p hp) ≤ 
  ((∑ i in finset.range g.nat_degree.succ, 
    (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * ((@polynomial.eval ℤ _ (i:ℤ) (f_bar (f_p p hp g.nat_degree)):ℝ)))) :=
begin
  rw <-abs_J_ineq1'_coe, exact abs_J_ineq1' g p hp,
end

lemma sum_ineq_1 (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) :
  ((∑ i in finset.range g.nat_degree.succ, 
    (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * ((@polynomial.eval ℤ _ (i:ℤ) (f_bar (f_p p hp g.nat_degree)):ℝ)))) ≤
  (g.nat_degree.succ:ℝ) *
      (↑(max_abs_coeff_1 g) * (↑(g.nat_degree) + 1) * ((g.nat_degree:ℝ) + 1).exp *
         (2 * (↑(g.nat_degree) + 1)) ^ (p + p * g.nat_degree)) :=
begin
  have ineq1 : 
  (∑ i in finset.range g.nat_degree.succ, 
    (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * ((@polynomial.eval ℤ _ (i:ℤ) (f_bar (f_p p hp g.nat_degree)):ℝ))) ≤
  (∑ i in finset.range g.nat_degree.succ, (max_abs_coeff_1 g:ℝ) * (g.nat_degree.succ : ℝ) * (g.nat_degree.succ:ℝ).exp * ((2 * ↑(g.nat_degree.succ)) ^ (p + p * g.nat_degree))),
  {
    apply finset.sum_le_sum, intros, simp only [finset.mem_range] at H, 
    by_cases hx : (x ∈ g.support),
    {
      apply mul_le_mul,
      {
        apply mul_le_mul, norm_cast,
        apply mul_le_mul, rw max_abs_coeff_1, apply finset.le_max', rw set_of_1_abs_coeff, simp only [finset.mem_insert], right, rw set_of_abs_coeff,
        rw finset.mem_image, use x, split, assumption, refl, norm_cast, exact le_of_lt H, norm_cast, exact bot_le,
        have max_abs_coeff_1_ge_1 := max_abs_coeff_1_ge_1 g, exact ge_trans max_abs_coeff_1_ge_1 trivial,
        rw real.exp_le_exp, norm_cast, exact le_of_lt H, norm_cast, have triv := real.exp_pos (x:ℝ), exact le_of_lt triv,
        norm_cast, apply mul_nonneg, have max_abs_coeff_1_ge_1 := max_abs_coeff_1_ge_1 g, exact ge_trans max_abs_coeff_1_ge_1 trivial,
        norm_cast, exact bot_le,
      },
      {
        norm_cast,
        have est := f_p_est g p hp x, simp only [int.coe_nat_succ, finset.mem_range] at est, replace est := est H, simp only [int.coe_nat_zero, int.coe_nat_pow, int.coe_nat_succ, zero_add, int.coe_nat_mul], exact est,
      },
      {
        norm_cast, exact eval_f_bar_nonneg (f_p p hp (polynomial.nat_degree g)) x,
      },
      {
        apply mul_nonneg, apply mul_nonneg, norm_cast, have max_abs_coeff_1_ge_1 := max_abs_coeff_1_ge_1 g, exact ge_trans max_abs_coeff_1_ge_1 trivial,
        norm_cast, exact bot_le, norm_cast, have triv := real.exp_pos (g.nat_degree.succ:ℝ), exact le_of_lt triv,
      },
    },
    {
      have hx' : g.coeff x = 0,
      {
        by_contra, exact hx((g.3 x).2 a),
      },
      rw hx', simp only [int.cast_zero, zero_mul, abs_zero, nat.cast_succ], apply mul_nonneg,
      {
        apply mul_nonneg, apply mul_nonneg, norm_cast, have max_abs_coeff_1_ge_1 := max_abs_coeff_1_ge_1 g, exact ge_trans max_abs_coeff_1_ge_1 trivial,
        norm_cast, exact bot_le, have triv := real.exp_pos (g.nat_degree + 1:ℝ), exact le_of_lt triv,
      },
      apply pow_nonneg, apply mul_nonneg, norm_cast, exact bot_le, norm_cast, exact bot_le,
    }
  },

  rw finset.sum_const at ineq1, conv_rhs at ineq1 {simp only [nat.cast_succ, finset.card_range],}, rw nat_mul_real at ineq1,
  exact ineq1,
end

lemma self_le_pow_nat (n m : ℕ) (hm : m ≥ 1) : n ≤ n ^ m :=
begin
  cases n, simp only [zero_le],
  have : n.succ = n.succ^1, simp only [nat.pow_one], conv_lhs {rw this}, apply nat.pow_le_pow_of_le_right, exact nat.succ_pos n, assumption,
end

lemma sum_ineq_2 (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) : 
  (g.nat_degree.succ:ℝ) * (↑(max_abs_coeff_1 g) * (↑(g.nat_degree) + 1) * ((g.nat_degree:ℝ) + 1).exp *
         (2 * (↑(g.nat_degree) + 1)) ^ (p + p * g.nat_degree)) ≤ 
  (g.nat_degree.succ:ℝ) ^ p * (↑(max_abs_coeff_1 g) ^ p * (↑(g.nat_degree) + 1) ^ p * ((g.nat_degree:ℝ) + 1).exp ^ p *
         (2 * (↑(g.nat_degree) + 1)) ^ (p + p * g.nat_degree)) :=
begin
  have hp' : p ≥ 1,
  {
    have ineq := nat.prime.pred_pos hp, 
    replace ineq : nat.succ 0 < p.pred.succ,
    exact nat.lt_succ_iff.mpr ineq, rw nat.succ_pred_eq_of_pos at ineq, exact le_of_lt ineq, exact nat.prime.pos hp,
  },
  apply mul_le_mul,
  {
    norm_cast, apply self_le_pow_nat, assumption,
  },
  {
    apply mul_le_mul,
    apply mul_le_mul, apply mul_le_mul, norm_cast,
    have triv : max_abs_coeff_1 g = (max_abs_coeff_1 g) ^ 1, simp only [pow_one], conv_lhs {rw triv}, apply pow_le_pow, exact max_abs_coeff_1_ge_1 g,
    assumption, norm_cast, apply self_le_pow_nat, assumption, norm_cast, exact bot_le, norm_cast, apply pow_nonneg, exact ge_trans (max_abs_coeff_1_ge_1 g) trivial,
    have triv : (g.nat_degree + 1:ℝ).exp = (g.nat_degree + 1:ℝ).exp ^ 1, simp only [pow_one], conv_lhs {rw triv}, apply pow_le_pow,
    by_contra rid, simp only [not_le] at rid,
    have ineq := (real.exp_lt_one_iff.1 rid), norm_cast at ineq, linarith, assumption, 
    have ineq := real.exp_pos (↑(g.nat_degree) + 1), exact le_of_lt ineq, 

    apply mul_nonneg,  norm_cast, apply pow_nonneg, exact ge_trans (max_abs_coeff_1_ge_1 g) trivial,
    norm_cast, exact bot_le,
    exact le_refl ((2 * (↑(polynomial.nat_degree g) + 1)) ^ (p + p * polynomial.nat_degree g)),
    norm_cast, exact bot_le, apply mul_nonneg, apply mul_nonneg, norm_cast, apply pow_nonneg, exact ge_trans (max_abs_coeff_1_ge_1 g) trivial,
    norm_cast, exact bot_le, apply pow_nonneg, have ineq := real.exp_pos (↑(g.nat_degree) + 1), exact le_of_lt ineq, 
  },
  {
    apply mul_nonneg, apply mul_nonneg, apply mul_nonneg, norm_cast, exact ge_trans (max_abs_coeff_1_ge_1 g) trivial,
    norm_cast, exact bot_le, have ineq := real.exp_pos (↑(g.nat_degree) + 1), exact le_of_lt ineq, norm_cast, exact bot_le,
  },
  {
    norm_cast, exact bot_le,
  }
end


def M (g : polynomial ℤ) : ℝ := (g.nat_degree.succ:ℝ) * (↑(max_abs_coeff_1 g) * (↑(g.nat_degree) + 1) * ((g.nat_degree:ℝ) + 1).exp *
         (2 * (↑(g.nat_degree) + 1)) ^ (1 + g.nat_degree))


theorem abs_J_ineq1 (g : polynomial ℤ) (p : ℕ) (hp : nat.prime p) : abs (J g p hp) ≤ (M g)^p :=
begin
  have ineq1 := abs_J_ineq1'' g p hp,
  have ineq2 := sum_ineq_1 g p hp,
  have ineq3 := sum_ineq_2 g p hp,
  have ineq4 := le_trans (le_trans ineq1 ineq2) ineq3,
  rw M, rw mul_pow, rw mul_pow, rw mul_pow, rw mul_pow, rw <-pow_mul, rw add_mul, rw one_mul,
  have eq1 : g.nat_degree * p = p * g.nat_degree, rw mul_comm, rw eq1, exact ineq4,
end


lemma sum_sub_sum1 (m : ℕ) (f : ℕ -> ℂ) : (∑ i in finset.range m.succ, f i) - (∑ i in finset.range m, f i) = f m :=
begin
  rw finset.sum_range_succ, simp only [add_sub_cancel],
end

lemma fact_grows_fast' (M : ℕ) : ∃ N : ℕ, ∀ n : ℕ, n > N -> (n.fact) > M ^ (n+1) :=
begin
by_cases (M = 0),
{
  rw h, use 1, intros n hn, simp only [gt_iff_lt], rw nat.zero_pow, exact nat.fact_pos n, exact nat.succ_pos n,
},
  have H := complex.is_cau_exp (M:ℂ),
  have triv : (1/M:ℝ) > 0, apply one_div_pos_of_pos, norm_cast, exact bot_lt_iff_ne_bot.mpr h,
  have H2 := is_cau_seq.cauchy₂ H triv,
  choose i hi using H2, use i, intros n hn,
  have H3 := hi n.succ n _ _, rw finset.sum_range_succ at H3, simp only [one_div_eq_inv, complex.abs_cast_nat, complex.abs_div, add_sub_cancel] at H3,
  have triv2 : ((M:ℂ) ^ n).abs = (↑M ^ n),
  {
    have eq1 : ↑((M:ℝ)^n) = (M:ℂ)^n, simp only [complex.of_real_pow, complex.of_real_nat_cast], rw <-eq1, rw complex.abs_of_real, rw abs_of_pos, apply pow_pos, norm_num, exact bot_lt_iff_ne_bot.mpr h,
  },
  rw triv2 at H3, norm_num at H3, rw div_lt_iff at H3,
  replace triv2 : (M:ℝ) > 0, norm_num, exact bot_lt_iff_ne_bot.mpr h,
  have H4 := (mul_lt_mul_right triv2).2 H3,
  replace triv2 : (M:ℝ)^n * (M:ℝ) = (M:ℝ)^(n+1), rw pow_add, simp only [pow_one], rw triv2 at H4,
  replace triv2 : (↑M)⁻¹ * ↑(n.fact) * ↑M = (n.fact:ℝ),
  {
    rw mul_comm, rw <-mul_assoc, 
    have triv3 : (M:ℝ) * (↑M)⁻¹ = 1, rw mul_comm, apply inv_mul_cancel, norm_num, assumption, rw triv3, simp only [one_mul],
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
  choose p Hp using p_exists, use (⟨p, Hp.right⟩ : nat.primes), simp only [max_le_iff, gt_iff_lt] at Hp ⊢,
  split,
  {
    have triv : z ≤ (z.nat_abs:ℤ), rw <-int.abs_eq_nat_abs, exact le_max_left z (-z),
    have hp := Hp.left.right,
    replace hp : (z.nat_abs + 1:ℤ) ≤ p, norm_cast, assumption,
    have triv2 : (z.nat_abs : ℤ) < (z.nat_abs:ℤ) + 1, exact lt_add_one ↑(int.nat_abs z), exact gt_of_gt_of_ge hp triv,
  },
  {
    have triv := hN (p-1) _, simp only [gt_iff_lt] at triv,
    have eq1 : (p - 1 + 1) = p, {apply nat.sub_add_cancel, exact le_of_lt Hp.right.one_lt,},
    rw eq1 at triv, assumption,
    have triv := Hp.left.left,
    replace triv : N + 1 < p , exact triv, exact nat.lt_pred_iff.mpr triv,
  },
end

theorem non_empty_supp (f : polynomial ℤ) (hf : f ≠ 0) : f.support.nonempty :=
begin
  contrapose hf, rw finset.nonempty at hf, rw not_exists at hf, simp only [classical.not_not], ext, simp only [polynomial.coeff_zero],
  have triv := (f.3 n).2 , contrapose triv, rw not_imp, split, exact triv, exact hf n,
end

def min_degree_term (f : polynomial ℤ) (hf : f ≠ 0) : ℕ := finset.min' (f.support) (non_empty_supp f hf)
def make_const_term_nonzero (f : polynomial ℤ) (hf : f ≠ 0) : polynomial ℤ := 
begin
  constructor, swap 2,
  {
    exact finset.image (λ i : ℕ, i-(min_degree_term f hf)) f.support,
  },
  swap 2, {
    intro n, exact (f.coeff (n+(min_degree_term f hf))),
  },
  {
    intro n, split, intro hn, rw finset.mem_image at hn, choose a ha using hn, rw <-ha.2, rw nat.sub_add_cancel,
    have eq2 := (f.3 a).1 ha.1, exact eq2,
    rw min_degree_term, exact finset.min'_le f.support (non_empty_supp f hf) a ha.1,

    intro hn, rw finset.mem_image, use n + min_degree_term f hf,
    split,
    exact (f.3 (n + min_degree_term f hf)).2 hn, simp only [nat.add_sub_cancel],
  },
end

theorem coeff_after_change (f : polynomial ℤ) (hf : f ≠ 0) (n : ℕ) : (make_const_term_nonzero f hf).coeff n = (f.coeff (n+(min_degree_term f hf))) :=
begin
  simp only [make_const_term_nonzero, polynomial.coeff_mk],
end


theorem coeff_zero_after_change (f : polynomial ℤ) (hf : f ≠ 0) : (make_const_term_nonzero f hf).coeff 0 ≠ 0 :=
begin
  rw coeff_after_change, simp only [ne.def, zero_add],
  have triv : min_degree_term f hf ∈ f.support,
  rw min_degree_term, exact f.support.min'_mem (non_empty_supp f hf),
  exact (f.3 (min_degree_term f hf)).1 triv,
end


theorem supp_after_change (f : polynomial ℤ) (hf : f ≠ 0) : (make_const_term_nonzero f hf).support = finset.image (λ i : ℕ, i-(min_degree_term f hf)) f.support :=
begin
  simp only [make_const_term_nonzero],
end

theorem aeval_ (f : polynomial ℤ) (r : ℝ) : (polynomial.aeval ℤ ℝ r) f = ∑ i in f.support, (f.coeff i : ℝ) * r ^ i :=
begin
  rw polynomial.aeval_def, rw polynomial.eval₂,  rw finsupp.sum, apply congr_arg, ext, simp only [ring_hom.eq_int_cast], rw mul_eq_mul', simp only [int.cast_inj], exact rfl,
  refl,
end

theorem non_zero_root_same (f : polynomial ℤ) (hf : f ≠ 0) (r : ℝ) (r_nonzero : r ≠ 0) (root_r : (polynomial.aeval ℤ ℝ r) f = 0) :
  (polynomial.aeval ℤ ℝ r) (make_const_term_nonzero f hf) = 0 :=

begin
  rw aeval_ at root_r ⊢,
  have H := @finset.sum_bij _ _ _ _ f.1 (make_const_term_nonzero f hf).1
    (λ i, ↑(f.coeff i) * r ^ (i))
    (λ i, ↑((make_const_term_nonzero f hf).coeff i) * r ^ (i+ (min_degree_term f hf))),
  let i : Π (a : ℕ), a ∈ f.support → ℕ,
  {
    intros a ha, exact a - (min_degree_term f hf),
  },
  have i_eq : i = λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf, exact rfl,
  replace H := H i,
  have hi : ∀ (a : ℕ) (ha : a ∈ f.support), i a ha ∈ (make_const_term_nonzero f hf).support,
  {
    intros a ha, rw i_eq, 
    have triv : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a ha = a - min_degree_term f hf,
    {
      exact rfl,
    },
    rw triv, rw supp_after_change, rw finset.mem_image, use a, split, exact ha, refl,
  },
  replace H := H hi,
  have assump1 : (∀ (a : ℕ) (ha : a ∈ f.support),
     (λ (i : ℕ), ↑(f.coeff i) * r ^ i) a =
       (λ (i : ℕ), ↑((make_const_term_nonzero f hf).coeff i) * r ^ (i + min_degree_term f hf)) (i a ha)),
  {
    intros a ha, 
    have triv1 : (λ (i : ℕ), ↑(f.coeff i) * r ^ i) a = ↑(f.coeff a) * r ^ a,
    {
      exact rfl,
    }, rw triv1,
    have triv2 : (λ (i : ℕ), ↑((make_const_term_nonzero f hf).coeff i) * r ^ (i + (min_degree_term f hf))) (i a ha) = (↑((make_const_term_nonzero f hf).coeff (i a ha)) * r ^ ((i a ha) + min_degree_term f hf)),
    {
      exact rfl,
    },
    rw triv2, rw i_eq,
    have triv3 : ((λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a ha) = a - min_degree_term f hf,
    {
      exact rfl,
    }, rw triv3, rw coeff_after_change, rw nat.sub_add_cancel, rw min_degree_term, exact f.support.min'_le (non_empty_supp f hf) a ha,
  },
  replace H := H assump1,
  have assump2 : (∀ (a₁ a₂ : ℕ) (ha₁ : a₁ ∈ f.support) (ha₂ : a₂ ∈ f.support),
     i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂),
  {
    intros a1 a2 ha1 ha2 H, rw i_eq at H, 
    have triv1 : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a1 ha1 = a1 - min_degree_term f hf, exact rfl, rw triv1 at H,
    have triv2 : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a2 ha2 = a2 - min_degree_term f hf, exact rfl, rw triv2 at H,
    have triv3 := (@add_left_inj ℕ _ (min_degree_term f hf) (a1 - min_degree_term f hf) (a2 - min_degree_term f hf)).2 H,
    rw nat.sub_add_cancel at triv3, rw nat.sub_add_cancel at triv3, exact triv3, rw min_degree_term, exact f.support.min'_le (non_empty_supp f hf) a2 ha2, exact f.support.min'_le (non_empty_supp f hf) a1 ha1,
  },
  replace H := H assump2,
  have assump3 : ∀ (b : ℕ),
     b ∈ (make_const_term_nonzero f hf).support → (∃ (a : ℕ) (ha : a ∈ f.support), b = i a ha),
  {
    intros b hb, rw supp_after_change at hb, rw finset.mem_image at hb, rw i_eq, choose a Ha using hb, use a, use Ha.1,
    have triv1 : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a _ = a - min_degree_term f hf, exact rfl, exact Ha.1, rw triv1, exact eq.symm Ha.2,
  },
  replace H := H assump3,
  rw root_r at H, 
  have triv : ∑ (x : ℕ) in
      (make_const_term_nonzero f hf).support,
      (λ (i : ℕ), ↑((make_const_term_nonzero f hf).coeff i) * r ^ (i + min_degree_term f hf)) x = ∑ (x : ℕ) in
      (make_const_term_nonzero f hf).support,
      (λ (i : ℕ), ↑((make_const_term_nonzero f hf).coeff i) * r ^ i * r ^ (min_degree_term f hf)) x,
  {
    apply congr_arg, ext, simp only [], rw pow_add, ring,
  },
  rw triv at H, simp only [] at H, rw <-finset.sum_mul at H, replace H := eq.symm H, rw mul_eq_zero at H,
  cases H, rw H, replace H := pow_eq_zero H, exfalso, exact r_nonzero H,
end

theorem non_zero_after_change (f : polynomial ℤ) (hf : f ≠ 0) : (make_const_term_nonzero f hf) ≠ 0 :=
begin
  intro rid, rw polynomial.ext_iff at rid, simp only [polynomial.coeff_zero] at rid,
  replace rid := rid 0,
  exact coeff_zero_after_change f hf rid,
end

theorem coeff_sum (f : ℕ -> polynomial ℤ) (s : finset ℕ) (n : ℕ) : (∑ i in s, f i).coeff n = (∑ i in s, (f i).coeff n) :=
begin
    apply finset.induction_on s, simp only [finset.sum_empty, polynomial.coeff_zero],
    intros a s ha H, rw finset.sum_insert, rw finset.sum_insert, rw polynomial.coeff_add, rw H, assumption, assumption,
end

theorem as_sum' (f : polynomial ℤ) : f = ∑ i in f.support, (polynomial.C (f.coeff i)) * (polynomial.X^i) :=
begin
    
    ext, rw coeff_sum,
    have triv : ∑ (i : ℕ) in f.support, (polynomial.C (f.coeff i) * polynomial.X ^ i).coeff n =
        ∑ (i : ℕ) in f.support, (f.coeff i) * ((polynomial.X ^ i).coeff n),
    {
        apply congr_arg, ext, simp only [polynomial.coeff_C_mul],
    },
    rw triv,
    replace triv : ∑ (i : ℕ) in f.support, f.coeff i * (polynomial.X ^ i).coeff n =
        ∑ (i : ℕ) in f.support, (ite (n = i) (f.coeff i) 0),
    {
        apply congr_arg, simp only [mul_boole, polynomial.coeff_X_pow],
    },
    rw triv, rw finset.sum_ite, simp only [add_zero, finset.sum_const_zero], rw finset.filter_eq,
    split_ifs, simp only [finset.sum_singleton], simp only [finset.sum_empty], have f3 := (f.3 n).2, rw <-not_imp_not at f3, rw not_not at f3, replace h := f3 h, exact h,
end


theorem transform_eq (f : polynomial ℤ) (hf : f ≠ 0) : f = (make_const_term_nonzero f hf) * (polynomial.X) ^ (min_degree_term f hf) :=
begin
    
    have H := @finset.sum_bij _ _ _ _ f.1 (make_const_term_nonzero f hf).1
        (λ i, (polynomial.C (f.coeff i)) * polynomial.X ^ i)
        (λ i, (polynomial.C ((make_const_term_nonzero f hf).coeff i)) * (polynomial.X) ^ (i+ (min_degree_term f hf))),
    let i : Π (a : ℕ), a ∈ f.support → ℕ,
  {
    intros a ha, exact a - (min_degree_term f hf),
  },
  have i_eq : i = λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf, exact rfl,
  replace H := H i,
  have hi : ∀ (a : ℕ) (ha : a ∈ f.support), i a ha ∈ (make_const_term_nonzero f hf).support,
  {
    intros a ha, rw i_eq, 
    have triv : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a ha = a - min_degree_term f hf,
    {
      exact rfl,
    },
    rw triv, rw supp_after_change, rw finset.mem_image, use a, split, exact ha, refl,
  },
  replace H := H hi,
  have assump1 : (∀ (a : ℕ) (ha : a ∈ f.support),
     (λ (i : ℕ), (polynomial.C (f.coeff i)) * (polynomial.X) ^ i) a =
       (λ (i : ℕ), (polynomial.C ((make_const_term_nonzero f hf).coeff i)) * (polynomial.X) ^ (i + min_degree_term f hf)) (i a ha)),
  {
    intros a ha, 
    have triv1 : (λ (i : ℕ), (polynomial.C (f.coeff i)) * (polynomial.X) ^ i) a = (polynomial.C (f.coeff a)) * (polynomial.X) ^ a,
    {
      exact rfl,
    }, rw triv1,
    have triv2 : (λ (i : ℕ), (polynomial.C ((make_const_term_nonzero f hf).coeff i)) * (polynomial.X) ^ (i + min_degree_term f hf)) (i a ha) 
        = (polynomial.C ((make_const_term_nonzero f hf).coeff (i a ha))) * (polynomial.X) ^ (i a ha + min_degree_term f hf),
    {
      exact rfl,
    },
    rw triv2, rw i_eq,
    have triv3 : ((λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a ha) = a - min_degree_term f hf,
    {
      exact rfl,
    }, rw triv3, rw coeff_after_change, rw nat.sub_add_cancel, rw min_degree_term, exact f.support.min'_le (non_empty_supp f hf) a ha,
  },
  replace H := H assump1,
  have assump2 : (∀ (a₁ a₂ : ℕ) (ha₁ : a₁ ∈ f.support) (ha₂ : a₂ ∈ f.support),
     i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂),
  {
    intros a1 a2 ha1 ha2 H, rw i_eq at H, 
    have triv1 : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a1 ha1 = a1 - min_degree_term f hf, exact rfl, rw triv1 at H,
    have triv2 : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a2 ha2 = a2 - min_degree_term f hf, exact rfl, rw triv2 at H,
    have triv3 := (@add_left_inj ℕ _ (min_degree_term f hf) (a1 - min_degree_term f hf) (a2 - min_degree_term f hf)).2 H,
    rw nat.sub_add_cancel at triv3, rw nat.sub_add_cancel at triv3, exact triv3, rw min_degree_term, exact f.support.min'_le (non_empty_supp f hf) a2 ha2, exact f.support.min'_le (non_empty_supp f hf) a1 ha1,
  },
  replace H := H assump2,
  have assump3 : ∀ (b : ℕ),
     b ∈ (make_const_term_nonzero f hf).support → (∃ (a : ℕ) (ha : a ∈ f.support), b = i a ha),
  {
    intros b hb, rw supp_after_change at hb, rw finset.mem_image at hb, rw i_eq, choose a Ha using hb, use a, use Ha.1,
    have triv1 : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a _ = a - min_degree_term f hf, exact rfl, exact Ha.1, rw triv1, exact eq.symm Ha.2,
  },
  replace H := H assump3,
  have eq1 := as_sum' f,
  have eq2 := as_sum' (make_const_term_nonzero f hf), rw eq2,
  simp only [] at H ⊢, rw finset.sum_mul,

  
  have eq3 : ∑ (x : ℕ) in
      (make_const_term_nonzero f hf).support,
      polynomial.C ((make_const_term_nonzero f hf).coeff x) * polynomial.X ^ (x + min_degree_term f hf) =
    ∑ (x : ℕ) in
      (make_const_term_nonzero f hf).support,
      polynomial.C ((make_const_term_nonzero f hf).coeff x) * polynomial.X ^ x * polynomial.X ^ min_degree_term f hf,
  {
      apply finset.sum_congr, exact rfl, intros, rw pow_add, ring,
  },
  rw <-eq3, rw <-H, exact eq1,
end

theorem nat_degree_decrease (f:polynomial ℤ) (hf : f ≠ 0) : (make_const_term_nonzero f hf).nat_degree ≤ f.nat_degree :=
begin
  have transform_eq := transform_eq f hf,
  have eq1 := @polynomial.nat_degree_mul_eq ℤ _ (make_const_term_nonzero f hf) (polynomial.X ^ min_degree_term f hf) _ _,
  have triv : (make_const_term_nonzero f hf * polynomial.X ^ min_degree_term f hf).nat_degree = f.nat_degree,
  {
      apply congr_arg, exact eq.symm transform_eq,
  }, rw triv at eq1, exact nat.le.intro (eq.symm eq1),
  
  {
    intro rid, have contra := polynomial.ext_iff.1 rid, simp only [polynomial.coeff_zero] at contra, replace contra := contra 0,
    exact coeff_zero_after_change f hf contra,
  },

  {
    intro contra, replace contra := pow_eq_zero contra, replace contra := polynomial.ext_iff.1 contra 1, simp only [polynomial.coeff_X_one, one_ne_zero, polynomial.coeff_zero] at contra, exact contra,
  }
end


theorem e_transcendental : ¬ is_algebraic ℤ e :=
begin
-- main part
  by_contra e_algebraic,
  rw is_algebraic at e_algebraic,
  choose g g_def using e_algebraic,
  have g_nonzero := g_def.1,
  have e_root_g := g_def.2,
  generalize g'_def : make_const_term_nonzero g g_nonzero = g',
  have coeff_zero_nonzero : (g'.coeff 0) ≠ 0,
  {
    rw <-g'_def, apply coeff_zero_after_change,
  },
  have e_root_g' : (polynomial.aeval ℤ ℝ e) g' = 0,
  {
    rw <-g'_def,
    apply non_zero_root_same, rw e, exact (1:ℝ).exp_ne_zero, exact e_root_g,
  },
  have contradiction := contradiction (M g') _ (max g.nat_degree (abs (g'.coeff 0))),
  choose p Hp using contradiction,
  have abs_J_ineq1 := abs_J_ineq1 g' p.val p.property,
  simp only [gt_iff_lt, max_lt_iff, int.coe_nat_lt] at Hp,
  have abs_J_ineq2 := abs_J_ineq2 g' e_root_g' coeff_zero_nonzero p.val p.property _,
  have rid := le_trans abs_J_ineq2 abs_J_ineq1,
  have rid2 := Hp.right, replace rid2 : ¬ ((M g' ^ p) ≥ ((p.val - 1).fact:ℝ)),
  {
    exact not_le.mpr rid2,
  },  exact rid2 rid,


-- assumptions I used in part and lemmas 
  {
    split,
    have triv := Hp.left.left, have ineq := nat_degree_decrease g g_nonzero, rw g'_def at ineq, exact gt_of_gt_of_ge triv ineq,
    have triv := Hp.left.right, rw int.abs_eq_nat_abs at triv, simp only [int.coe_nat_lt] at triv, assumption,
  },

  {
    rw M, apply mul_nonneg, norm_cast, exact bot_le, apply mul_nonneg, apply mul_nonneg, norm_cast, apply mul_nonneg, exact ge_trans (max_abs_coeff_1_ge_1 g') trivial,
    norm_cast, exact bot_le, have triv : (g'.nat_degree + 1 : ℝ).exp > 0, exact (g'.nat_degree + 1:ℝ).exp_pos, exact le_of_lt triv,
    norm_num, apply pow_nonneg, apply mul_nonneg, linarith, norm_cast, exact bot_le,
  },
end

end e