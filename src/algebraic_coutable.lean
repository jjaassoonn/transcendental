import data.set.basic set_theory.schroeder_bernstein
import data.set.countable
import ring_theory.algebraic
import data.polynomial
import data.rat.default
import data.real.basic data.real.cardinality
import tactic.linarith tactic.fin_cases

noncomputable theory
local attribute [instance] classical.prop_decidable


namespace project
def algebraic_set : set real := {x | is_algebraic rat x }

def roots_real (p : polynomial rat) : set real := {x | polynomial.aeval rat real x p = 0}

def poly_rat_to_poly_real (p : polynomial rat) : polynomial real :=
begin
  constructor,
  swap,
  {
      exact p.1,
  },

  swap,
  {
      intro n,
      exact real.of_rat (p.2 n),
  },

  {
      intro n,
      split,
      intro hn,
      rw real.of_rat_eq_cast,
      norm_cast,
      exact (p.3 n).mp hn,

      rw real.of_rat_eq_cast,
      norm_cast,
      exact (p.3 n).mpr,
  },
  done
end

def poly_rat_to_poly_real_wd (p : polynomial rat) : Prop := ∀ x : real, polynomial.aeval rat real x p = (poly_rat_to_poly_real p).eval x

theorem poly_rat_to_poly_real_preserve_deg (p : polynomial rat) : p.degree = (poly_rat_to_poly_real p).degree :=
begin
  rw [poly_rat_to_poly_real, polynomial.degree, polynomial.degree], done
end

theorem poly_rat_to_poly_real_C_wd' (a : rat) : polynomial.C (real.of_rat a) = poly_rat_to_poly_real (polynomial.C a) :=
begin
  ext,
  unfold poly_rat_to_poly_real,
  rw polynomial.coeff_C,
  split_ifs,

  simp, rw h, rw <-polynomial.coeff, rw polynomial.coeff_C_zero,
  simp, rw <-polynomial.coeff, rw polynomial.coeff_C, split_ifs, norm_cast,

  done
end

theorem poly_rat_to_poly_real_C_wd : ∀ a : rat, poly_rat_to_poly_real_wd (polynomial.C a) :=
begin
  intros r x,
  rw <-poly_rat_to_poly_real_C_wd',
  simp,
  exact rfl,
  done    
end

theorem poly_rat_to_poly_real_add (p1 p2 : polynomial rat) : poly_rat_to_poly_real (p1 + p2) = poly_rat_to_poly_real p1 + poly_rat_to_poly_real p2 :=
begin
  ext,
  rw [poly_rat_to_poly_real, poly_rat_to_poly_real, poly_rat_to_poly_real],
  simp,
  norm_cast,
  done
end

theorem poly_rat_to_poly_real_add_wd (p1 p2 : polynomial rat) 
    (h1 : poly_rat_to_poly_real_wd p1) 
    (h2 : poly_rat_to_poly_real_wd p2) : poly_rat_to_poly_real_wd (p1 + p2) :=
begin
  intro x,
  simp,
  rw h1, rw h2,
  rw <-polynomial.eval_add,
  rw poly_rat_to_poly_real_add,
  done
end

theorem poly_rat_to_poly_real_pow1 (n : nat) : poly_rat_to_poly_real (polynomial.X ^ n) = polynomial.X ^ n :=
begin
  ext, rename n_1 m,
  rw poly_rat_to_poly_real, simp,
  split_ifs;
  norm_cast; rw [<-polynomial.coeff, polynomial.coeff_X_pow]; split_ifs; refl,
  done
end

theorem poly_rat_to_poly_real_pow2 (n : nat) (a : rat) : poly_rat_to_poly_real ((polynomial.C a) * polynomial.X ^ n) = (polynomial.C (real.of_rat a)) * polynomial.X ^ n :=
begin
  ext, rename n_1 m,
  rw poly_rat_to_poly_real, simp,
  norm_cast, rw [<-polynomial.coeff, polynomial.coeff_C_mul_X],
  done
end

theorem poly_rat_to_poly_real_pow_wd (n : nat) (a : rat) (h : poly_rat_to_poly_real_wd ((polynomial.C a) * polynomial.X ^ n)) : poly_rat_to_poly_real_wd ((polynomial.C a) * polynomial.X ^ n.succ) :=
begin
  intro x,
  rw poly_rat_to_poly_real_pow2,
  simp [polynomial.aeval_def],
  rw polynomial.eval₂_pow,
  rw <-polynomial.aeval_def,
  rw polynomial.aeval_X,
  exact rfl,
  done
end


theorem poly_rat_to_poly_real_ne_zero (p : polynomial rat) : p ≠ 0 ↔ (poly_rat_to_poly_real p) ≠ 0 :=
begin
  split,
  intros h hp,
  rw poly_rat_to_poly_real at hp,
  rw polynomial.ext_iff at hp,
  simp at hp,
  rw <-polynomial.coeff at hp,
  have h' : p = 0,
  exact finsupp.ext hp,
  exact h h',

  intros h hp,
  have h' : poly_rat_to_poly_real p = 0,
  unfold poly_rat_to_poly_real,
  simp, ext, simp, rw <-polynomial.coeff, rw hp, simp,
  exact h h',

  done,
end

theorem poly_rat_to_poly_real_well_defined (x : real) (p : polynomial rat) :
    poly_rat_to_poly_real_wd p :=
polynomial.induction_on
    p
    poly_rat_to_poly_real_C_wd
    poly_rat_to_poly_real_add_wd
    poly_rat_to_poly_real_pow_wd

def roots_real' (p : polynomial rat) : set real := {x | (poly_rat_to_poly_real p).eval x = 0}

theorem roots_real_eq_roots_real' (p : polynomial rat) : roots_real p = roots_real' p :=
begin
  ext, split; intro hx,
  unfold roots_real at hx,
  rw set.mem_set_of_eq at hx,
  unfold roots_real',
  rw set.mem_set_of_eq,
  have g := poly_rat_to_poly_real_well_defined x p,
  unfold poly_rat_to_poly_real_wd at g,
  have g' := g x,
  rw hx at g',
  exact eq.symm g',

  unfold roots_real' at hx,
  rw set.mem_set_of_eq at hx,
  rw roots_real,
  rw set.mem_set_of_eq,
  have g := poly_rat_to_poly_real_well_defined x p,
  unfold poly_rat_to_poly_real_wd at g,
  have g' := g x,
  rw hx at g',
  exact g',

  done
end

theorem roots_real'_eq_roots (p : polynomial rat) (hp : p ≠ 0) : roots_real' p = ↑((poly_rat_to_poly_real p).roots) :=
begin
  ext,
  have g := @polynomial.mem_roots real x _ (poly_rat_to_poly_real p) ((poly_rat_to_poly_real_ne_zero p).mp hp),
  split,
  intro hx, rw roots_real' at hx, rw set.mem_set_of_eq at hx,
  simp, apply g.mpr, exact hx,

  intro hx, simp at hx, unfold roots_real', rw set.mem_set_of_eq,
  exact g.mp hx,
  done
end

theorem roots_real_eq_roots (p : polynomial rat) (hp : p ≠ 0) : roots_real p = ↑((poly_rat_to_poly_real p).roots) :=
begin
  rw [roots_real_eq_roots_real', roots_real'_eq_roots], assumption, done
end

theorem roots_finite (p : polynomial rat) (hp : p ≠ 0) : set.finite (roots_real p) :=
begin
  rw roots_real_eq_roots,
  split, exact additive.fintype, assumption, done
end


-- Part I of project
def nat_set : set nat := @set.univ nat

def rat_n (n : nat) := fin n -> rat
def nat_n (n : nat) := fin n -> nat
def poly_n (n : nat) := {x : polynomial rat // x.nat_degree < n}
def poly_n' (n : nat) := {p : polynomial rat // p ≠ 0 ∧ p.nat_degree < n}
def rat_n' (n : nat) := {f : fin n -> rat // f ≠ 0}
def rat' := {r : rat // r ≠ 0}


theorem strange_fun_aux (q : rat) (hq : ¬(q.2 = 1 ∨ q.1 = 0)) : q ≠ 0 :=
begin
  intro absurd, rw rat.zero_iff_num_zero at absurd, 
  exact (not_or_distrib.mp hq).2 absurd
end

def strange_fun (q : rat) : rat' :=
begin

  by_cases (q.2 = 1 ∨ q.1 = 0); rename h is_q_int,
  {
    by_cases (q < 0), exact ⟨q, ne_of_lt h⟩,
    exact ⟨q + 1, by linarith⟩,
  },
  {
    exact ⟨q, strange_fun_aux q is_q_int⟩,
  }
end

theorem strange_fun_inj : function.injective strange_fun :=
begin
{
    intros q1 q2 hq,
    by_cases (q1.2 = 1 ∨ q1.1 = 0);
    by_cases (q2.2 = 1 ∨ q2.1 = 0); rename h q2_int; rename h q1_int,
    
    {
      simp [strange_fun, strange_fun, q1_int, q2_int] at hq,
      by_cases (q1 < 0); by_cases (q2 < 0); rename h q2_neg; rename h q1_neg,
      
      simp [q1_neg, q2_neg] at hq, exact hq,
      simp [q1_neg, q2_neg] at hq, linarith,
      simp [q1_neg, q2_neg] at hq, linarith,
      simp [q1_neg, q2_neg] at hq, exact hq,
    },

    {
      simp [strange_fun, strange_fun, q1_int, q2_int] at hq,
      by_cases (q1 < 0); by_cases (q2 < 0); rename h q2_neg; rename h q1_neg,
      simp [q1_neg, q2_neg] at hq, assumption,
      simp [q1_neg, q2_neg] at hq, assumption,
      simp [q1_neg, q2_neg] at hq, linarith,
      simp [q1_neg, q2_neg] at hq, cases q1_int,
      {
        simp [rat.add_num_denom, q1_int] at hq,
        simp at q1_neg,
        have g := @rat.num_denom' (q1.num + 1) 1 (by linarith) (nat.coprime_one_right (int.nat_abs (q1.num + 1))),
        norm_cast at g,
        rw <-g at hq,
        have h : ({ num := q1.num + 1, denom := 1, pos := (by linarith), cop := (nat.coprime_one_right (int.nat_abs (q1.num + 1))) } : rat).denom = q2.denom := by rw hq,
        have h' : ({ num := q1.num + 1, denom := 1, pos := (by linarith), cop := (nat.coprime_one_right (int.nat_abs (q1.num + 1))) } : rat).denom = 1 := rfl,
        rw h at h', rw not_or_distrib at q2_int, cases q2_int with q21 q22, exfalso, exact q21 h',
      },
      {
        rw <-rat.zero_iff_num_zero at q1_int,
        rw q1_int at hq, simp at hq,
        have h : q2.denom = 1,
        exact calc q2.denom = (1 : rat).denom : by rw hq
                ...         = 1 : rfl,
        rw not_or_distrib at q2_int, cases q2_int with q21 q22, exfalso, exact q21 h, 
      },
    },

    {
      simp [strange_fun, strange_fun, q1_int, q2_int] at hq,
      by_cases (q1 < 0); by_cases (q2 < 0); rename h q2_neg; rename h q1_neg; simp [q1_neg, q2_neg] at hq,
      
      assumption, linarith, assumption,
      cases q2_int with q22 q21,
      have h : q1.denom = (q2 + 1).denom := by rw hq,
      simp [rat.add_num_denom, q22] at h,
      have g := @rat.num_denom' (q2.num + 1) 1 (by linarith) (nat.coprime_one_right (int.nat_abs (q2.num + 1))),
      norm_cast at g,
      rw <-g at h,
      have h' : ({ num := q2.num + 1, denom := 1, pos := (by linarith), cop := (nat.coprime_one_right (int.nat_abs (q2.num + 1))) } : rat).denom = 1 := rfl,
      rw h' at h, exfalso, exact (not_or_distrib.mp q1_int).1 h,
      rw <-rat.zero_iff_num_zero at q21, simp [q21] at hq,
      have h : q1.denom = 1,
      exact calc q1.denom = (1 : rat).denom : by rw hq
                      ... = 1 : rfl,
      exfalso, exact (not_or_distrib.mp q1_int).1 h,
    },

    {
      simp [strange_fun, strange_fun, q1_int, q2_int] at hq,
      by_cases (q1 < 0); by_cases (q2 < 0); rename h q2_neg; rename h q1_neg; assumption,    
    },
  },
end

theorem strange_fun_sur : function.surjective strange_fun :=
begin
  {
    intro q,
    by_cases (q.1.2 = 1 ∨ q.1.1 = 0); rename h q_int,

    {
      by_cases (q.1 < 0); rename h q_pos,
      use q.1, simp [strange_fun, q_int, q_pos],
      generalize h' : q.1-1 = q',
      have q'_int : q'.2 = 1 ∨ q'.1 = 0,
      {
        cases q_int, left,
        have h'' : q.1 + (-1 : rat) = q', linarith, rw rat.add_num_denom at h'', simp [q_int] at h'', 
        have h''' : ({ num := -1 + q.1.1, denom := 1, pos := (by linarith), cop := (nat.coprime_one_right (int.nat_abs (-1 + q.1.1))) } : rat) = rat.mk (-1 + q.1.1) 1,
        rw rat.num_denom', norm_cast, rw <-h''' at h'', rw <-h'',
        left, rw <-rat.zero_iff_num_zero at q_int, simp [q_int] at h', rw <-h', exact rfl,
      },

      have q_ne_0 := q.2, rw [not_lt] at q_pos,
      have q_ge_1 : q.1 ≥ 1,
      {
        cases q_int,
        have H : q.1 = q.1.1,
        {
          rw rat.coe_int_eq_mk,
          have H : q.1 = { num := q.1.1, denom := q.1.2, pos := q.1.3, cop := q.1.4 }, {induction q.1, refl},
          conv_lhs { rw H }, rw rat.num_denom', rw q_int, norm_cast,
        },
        have H2 : q.1 > 0 := lt_of_le_of_ne q_pos (ne.symm q_ne_0), rw H at H2, norm_cast at H2,
        suffices H3 : q.1.1 ≥ 1, have H4 : (q.1.1 : rat) ≥ 1, norm_cast, assumption, rw <-H at H4, assumption, linarith,
        exfalso, rw <-rat.zero_iff_num_zero at q_int, exact q_ne_0 q_int,
      },
      have H2 : q' ≥ 0, linarith,
      have H2' : ¬ q' < 0, linarith, use q', simp [strange_fun, q'_int, H2'],
      apply subtype.eq', simp, linarith,
    },

    {
      use q.1, simp [strange_fun, q_int],
    },
  },
  done
end

theorem rat_equiv_rat' : rat ≃ rat' :=
begin
  suffices H : ∃ f : rat -> rat', function.bijective f,
  choose f Hf using H, exact equiv.of_bijective Hf,
  use strange_fun,
  split,
  exact strange_fun_inj,
  exact strange_fun_sur,
end

def zero_rat_n {n : nat} : rat_n n.succ := (fun m, 0)
def zero_poly_n {n : nat} : poly_n n.succ := ⟨0, nat.succ_pos n⟩ 

def identify (n : nat) : (poly_n n) -> (rat_n n) :=
begin
  intro p,
  intro m,
  exact p.val.coeff m.val,
  done
end

@[simp] theorem identify_0_eq_0 (n : nat) : (identify n.succ zero_poly_n) = zero_rat_n :=
begin
 rw [identify, zero_rat_n, zero_poly_n], ext, simp, done
end

lemma m_mod_n_lt_n : ∀ n : nat, n ≠ 0 -> ∀ m : nat, m % n < n :=
begin
  intros n hn m,
  have hn' : 0 < n := zero_lt_iff_ne_zero.mpr hn,
  exact @nat.mod_lt m n hn',
end

theorem inj_identify_n : ∀ n : nat, (n ≠ 0) -> function.injective (identify n) :=
begin
  intros n hn,
  unfold function.injective,
  intros p1 p2 h,
  unfold identify at h,
  simp at h,
  rw subtype.ext,
  ext, rename n_1 m,
  rw function.funext_iff at h,
  have p1_deg := p1.property,
  have p2_deg := p2.property,

  -- consider m = n, m < n, m > n seprately,
  cases (nat.lt_trichotomy m n) with ineq,
  -- m < n
  {
    let m' := (⟨m, ineq⟩ : fin n),
    have h_m := h m',
    have g : m'.val = m,
    {
        exact rfl,
    },
    rw [<-g, h_m],
  },
  rename h_1 ineq,
  cases ineq,

  -- m = n
  {
    rw ineq,
    rw [(@polynomial.coeff_eq_zero_of_nat_degree_lt rat _ p1.val n p1_deg),
        (@polynomial.coeff_eq_zero_of_nat_degree_lt rat _ p2.val n p2_deg)],
  },

  -- n < m
  {
    rw @polynomial.coeff_eq_zero_of_nat_degree_lt rat _ p1.val m (lt.trans p1_deg ineq),
    rw @polynomial.coeff_eq_zero_of_nat_degree_lt rat _ p2.val m (lt.trans p2_deg ineq),
  }
end

theorem identify_nzero_to_nzero (n : nat) (p : poly_n n.succ) (hp : p ≠ zero_poly_n) : (identify n.succ p) ≠ zero_rat_n :=
begin
  have g := inj_identify_n n.succ (nat.succ_ne_zero n),
  have g' := @g p zero_poly_n, simp at g',
  intro absurd, exact hp (g' absurd),
end

theorem sur_identify_n : ∀ n : nat, (n ≠ 0) -> function.surjective (identify n) :=
begin
    intros n hn,
    unfold function.surjective,
    intro q,
    let support : finset nat := finset.filter (λ m : nat, (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n),
    have hsupport : support = finset.filter (λ m : nat, (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n) := rfl,

    let to_fun : nat -> rat := (λ m : nat, ite (m ∈ support) (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) 0),
    have hto_fun : to_fun = (λ m : nat, ite (m ∈ support) (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) 0) := rfl,
    
    let mem_support_to_fun : ∀a, a ∈ support ↔ to_fun a ≠ 0,
    {
      intro m,
      split,
      intro hm,
      have hm'' := hm,
      rw hsupport at hm,
      have hm' := hm,
      rw finset.mem_filter at hm',
      cases hm',
      rename hm'_right qm_ne_0,
      rw hto_fun,
      have g : (λ (m : ℕ), ite (m ∈ support) (q ⟨m % n, m_mod_n_lt_n n hn m⟩) 0) m = ite (m ∈ support) (q ⟨m % n, m_mod_n_lt_n n hn m⟩) 0 := rfl,
      rw g,
      split_ifs,
      exact qm_ne_0,

      intro hm,
      have hm' := hm,
      rw hto_fun at hm',
      have g : (λ (m : ℕ), ite (m ∈ support) (q ⟨m % n, m_mod_n_lt_n n hn m⟩) 0) m = ite (m ∈ support) (q ⟨m % n, m_mod_n_lt_n n hn m⟩) 0 := rfl,
      rw g at hm',
      have g : ite (m ∈ support) (q ⟨m % n, m_mod_n_lt_n n hn m⟩) 0 ≠ 0 -> (m ∈ support),
      {
        intro h,
        by_contra,
        split_ifs at h,
        have h' : (0 : rat) = 0 := rfl,
        exact h h',
      },
      exact g hm',
    },
    let p : polynomial rat := ⟨support, to_fun, mem_support_to_fun⟩,
    have hp_support : p.support =  finset.filter (λ (m : ℕ), q ⟨m % n, m_mod_n_lt_n n hn m⟩ ≠ 0) (finset.range n) := rfl,
    have hp_support2 : ∀ m ∈ p.support, m < n,
    {
      rw hp_support,
      intro m,
      rw finset.mem_filter,
      intro hm,
      cases hm,
      exact list.mem_range.mp hm_left,
    },
    have hp_deg : (p.degree ≠ ⊥) -> p.degree < n,
    {
      intro hp_deg_not_bot,
      rw polynomial.degree,
      rw finset.sup_lt_iff,
      intros m hm,
      have hmn := hp_support2 m hm,
      swap,
      exact @with_bot.bot_lt_coe nat _ n,

      have g := @with_bot.some_eq_coe nat n,
      rw <-g,
      rw with_bot.some_lt_some,
      exact hmn,
    },

    have hp_nat_deg : p.nat_degree < n,
    {
      by_cases (p = 0),
      rename h hp_eq_0,
      have g := polynomial.nat_degree_zero,
      rw <-hp_eq_0 at g,
      rw g,
      rw zero_lt_iff_ne_zero,
      exact hn,

      rename h hp_ne_0,
      have p_deg_ne_bot : p.degree ≠ ⊥,
      {
        intro gg,
        rw polynomial.degree_eq_bot at gg,
        exact hp_ne_0 gg,
      },
      have hp_deg' := hp_deg p_deg_ne_bot,
      have g := polynomial.degree_eq_nat_degree hp_ne_0,
      rw g at hp_deg',
      rw <-with_bot.coe_lt_coe,
      exact hp_deg',
    },

    use ⟨p, hp_nat_deg⟩,
    {
      ext,
      rename x m,
      unfold identify,
      simp,
      rw hto_fun,
      have g : (λ (m : ℕ), ite (m ∈ support) (q ⟨m % n, m_mod_n_lt_n n hn m⟩) 0) (m.val) = ite (m.val ∈ support) (q ⟨m.val % n, m_mod_n_lt_n n hn m.val⟩) 0 := rfl,
      rw g,
      split_ifs,
      
      -- m.val ∈ support
      {
        simp at h,
        cases h,
        have important : m = ⟨m.1 % n, _⟩,
        {
          rw fin.ext_iff,
          simp,
          rw nat.mod_eq_of_lt,
          exact h_left,
        },
        rw <-important,
      },
      -- m.val ∉ support
      {
        simp at h,
        have h' := h m.2,
        have important : m = ⟨m.1 % n, _⟩,
        {
          rw fin.ext_iff,
          simp,
          rw nat.mod_eq_of_lt,
          exact m.2,
        },
        rw <-important at h',
        exact eq.symm h',
      },
    },
end


theorem poly_n'_equiv_rat_n' (n : nat) : poly_n' n.succ ≃ rat_n' n.succ :=
begin
  let f : (poly_n' n.succ) -> (rat_n' n.succ),
  {
    intro p,
    generalize hx : (identify n.succ) ⟨p.1, p.2.2⟩ = x,
    split, swap, exact x,
    have g := identify_nzero_to_nzero n ⟨p.1, p.2.2⟩ _,
    rw hx at g, exact g, rw [zero_poly_n], simp, exact p.2.1,
  },

  suffices f_bij : function.bijective f,
  exact equiv.of_bijective f_bij,
  split,
  {
    intros x1 x2 hx, simp at hx, rw [identify, function.funext_iff] at hx, simp at hx,
    suffices h : x1.val = x2.val, exact subtype.eq h,
    ext,
    have h1 := x1.2.2, have h2 := x2.2.2, rename n_1 m,
    by_cases (m ≥ n.succ),
    rw [polynomial.coeff_eq_zero_of_nat_degree_lt, polynomial.coeff_eq_zero_of_nat_degree_lt],
    exact lt_of_lt_of_le h2 h, exact lt_of_lt_of_le h1 h,

    simp at h, rw hx ⟨m, h⟩,
  },

  {
    intro q,
    have h := sur_identify_n n.succ (nat.succ_ne_zero n) q.1,
    choose p hp using h,
    have p_ne_0' : p ≠ zero_poly_n,
    {
      by_contra absurd, rw [ne.def, not_not] at absurd,
      have absurd' := identify_0_eq_0 n,
      rw <-absurd at absurd', rw hp at absurd', exact q.2 absurd',
    },
    have p_ne_0 : p.1 ≠ 0,
    {
      intro hp,
      have h : 0 = zero_poly_n.1 := rfl, rw h at hp,
      exact p_ne_0' (@subtype.eq _ _ p zero_poly_n hp),
    },
    use ⟨p.1, ⟨p_ne_0, p.2⟩⟩,
    rw [subtype.ext], simp, assumption,
  },
  done
end

  def f : rat_n 1 -> rat_n' 1 :=
  begin
    intro r, split, swap, exact (fun m, (strange_fun (r m)).1),
    intro a, rw function.funext_iff at a, replace a := a 0, simp at a,
    generalize hx : (strange_fun (r 0)) = x, rw hx at a, exact x.2 a,
  end


  def g : rat_n' 1 -> rat_n 1 :=
  begin
    intros g n, exact g.1 n,
  end

theorem rat_1_equiv_rat_1' : rat_n 1 ≃ rat_n' 1 :=
begin
  suffices H1 : ∃ f : rat_n 1 -> rat_n' 1, function.bijective f,
    choose h hh using H1,
    exact equiv.of_bijective hh,

  suffices H2 : ∃ f : rat_n 1 -> rat_n' 1, ∃ g : rat_n' 1 -> rat_n 1, function.injective f ∧ function.injective g,
    choose f g h using H2, exact function.embedding.schroeder_bernstein h.1 h.2,

  use f, use g, split,
  {
    intros x1 x2 hx, simp [f] at hx, rw function.funext_iff at hx, replace hx := hx 0,
    replace hx := subtype.eq hx, replace hx := strange_fun_inj hx, ext, fin_cases x, exact hx,
  },
  {
    intros x1 x2 hx, simp [g] at hx, replace hx := subtype.eq hx, exact hx,
  }
end


def fn {n : nat} : rat_n (nat.succ (nat.succ n)) -> rat_n (nat.succ n) × rat :=
begin
  intro r, split, intro m, exact r (⟨m.1, nat.lt_trans m.2 (nat.lt_succ_self n.succ)⟩ : fin n.succ.succ),
  exact r (⟨n.succ, nat.lt_succ_self n.succ⟩ : fin n.succ.succ),
end

def gn {n : nat} : rat_n (nat.succ n) × rat -> rat_n (nat.succ (nat.succ n)) :=
begin
  intros r m, cases r with p r,
  by_cases (m.1 = n.succ), exact r,
    have hm' := m.2,
    have hm : m.1 < n.succ,
    replace hm : m.1 ≤ n.succ, exact fin.le_last m, exact lt_of_le_of_ne hm h,
    exact p (⟨m.1, hm⟩ : fin n.succ),
end


theorem aux_rat_n (n : nat) : rat_n (nat.succ (nat.succ n)) ≃ rat_n (nat.succ n) × rat :=
begin
  suffices H1 : ∃ f : rat_n n.succ.succ -> rat_n n.succ × rat, function.bijective f,
    choose h hh using H1,
    exact equiv.of_bijective hh,

  suffices H2 : ∃ f : rat_n n.succ.succ -> rat_n n.succ × rat, ∃ g : rat_n n.succ × rat -> rat_n n.succ.succ, function.injective f ∧ function.injective g,
    choose f g h using H2, exact function.embedding.schroeder_bernstein h.1 h.2,

  use fn, use gn, split,
  {
    intros x1 x2 hx, simp [fn] at hx, cases hx with h1 h2, rw function.funext_iff at h1, ext,
    by_cases (x = ⟨n.succ, nat.lt_succ_self n.succ⟩), rw <-h at h2, assumption,
      simp [fin.eq_iff_veq] at h, have h2 := x.2, replace h2 : x.1 ≤ n.succ := fin.le_last x,
      have h3 : x.1 < n.succ := lt_of_le_of_ne h2 h,
      have H := h1 ⟨x.1, h3⟩, simp at H, exact H,
  },

  {
    intros x1 x2 hx, cases x1 with p1 x1, cases x2 with p2 x2,
    ext; simp; simp [gn] at hx; rw function.funext_iff at hx, swap,
      generalize hm : (⟨n.succ, nat.lt_succ_self n.succ⟩ : fin n.succ.succ) = m,
      have hm' : m.val = n.succ, rw <-hm, replace hx := hx m, simp [hm'] at hx, assumption,
      
      generalize hm : (⟨x.1, nat.lt_trans x.2 (nat.lt_succ_self n.succ)⟩ : fin n.succ.succ) = m,
      replace hx := hx m, have hm' : m.1 ≠ n.succ,
        intro a, rw <-hm at a, simp at a, have hx' := x.2, linarith,
      simp [hm'] at hx, have hm2 := m.2, replace hm2 : m.1 ≤ n.succ, exact fin.le_last m,
      have hm3 : m.1 < n.succ, exact lt_of_le_of_ne hm2 hm',
      have H : x = ⟨m.1, hm3⟩, rw fin.ext_iff at hm ⊢, simp at hm ⊢, exact hm,
      rw H, exact hx,
  },
  done
end

def fn' {n : nat} : rat_n' (nat.succ (nat.succ n)) -> rat_n (nat.succ n) × rat := 
begin
  intro p, split, intro m, 
  exact p.1 (⟨m.1, nat.lt_trans m.2 (nat.lt_succ_self n.succ)⟩ : fin n.succ.succ),
  exact p.1 (⟨n.succ, nat.lt_succ_self n.succ⟩ : fin n.succ.succ),
end

def gn' {n : nat} : rat_n (nat.succ n) × rat -> rat_n' (nat.succ (nat.succ n)) :=
begin
  intro x,
  split, swap 2, intro m,
  by_cases (m.1 = n.succ), exact (strange_fun x.2).1,
    have H2 : m.1 < n.succ,  have H2' := fin.le_last m, exact lt_of_le_of_ne H2' h,
    exact (strange_fun (x.1 ⟨m.1, H2⟩)).1,

  intro a, rw function.funext_iff at a, simp at a,
  generalize hm : (⟨n.succ, nat.lt_succ_self n.succ⟩ : fin n.succ.succ) = m,
  have a' := a m, have h : m.1 = n.succ, rw <-hm, simp [h] at a', exact (strange_fun x.2).2 a',
end


theorem aux_rat_n' (n : nat) : rat_n' (nat.succ (nat.succ n)) ≃ rat_n (nat.succ n) × rat :=
begin
  suffices H1 : ∃ f : rat_n' n.succ.succ -> rat_n n.succ × rat, function.bijective f,
    choose h hh using H1,
    exact equiv.of_bijective hh,

  suffices H2 : ∃ f : rat_n' n.succ.succ -> rat_n n.succ × rat, ∃ g : rat_n n.succ × rat -> rat_n' n.succ.succ, function.injective f ∧ function.injective g,
    choose f g h using H2, exact function.embedding.schroeder_bernstein h.1 h.2,

  use fn', use gn', split,
  {
    intros x1 x2 hx, simp [fn'] at hx, cases hx with h1 h2, rw function.funext_iff at h1,
    apply subtype.eq', ext, rename x m,
    by_cases (m.val = n.succ),
      have H1 : m = (⟨n.succ, (nat.lt_succ_self n.succ)⟩ : fin n.succ.succ), 
      rw fin.ext_iff, simp, exact h,
      rw H1, assumption,

      have H2 : m.1 < n.succ,  have H2' := fin.le_last m, exact lt_of_le_of_ne H2' h,
      have h1m := h1 ⟨m.1, H2⟩, simp at h1m, exact h1m,
  },
  {
    intros x1 x2 hx, simp [gn'] at hx, ext, rename x m,
    generalize hm' : (⟨m.1, nat.lt_trans m.2 (nat.lt_succ_self n.succ)⟩ : fin n.succ.succ) = m',
    have hm'' : m'.val = m.1, rw <-hm',
    have Hm' : m'.val ≠ n.succ, have Hm'' := ne_of_lt m.2, rw <-hm'' at Hm'', assumption,
    rw function.funext_iff at hx, have H := hx m', simp [hm'', Hm'] at H,
    replace H := subtype.eq' H,
    exact strange_fun_inj H,

    generalize hm : (⟨n.succ, nat.lt_succ_self n.succ⟩ : fin n.succ.succ) = m,
    have Hm : m.val = n.succ, rw <-hm, rw function.funext_iff at hx,
    have H := hx m, simp [Hm] at H, replace H := subtype.eq' H,
    exact strange_fun_inj H,
  }
end

theorem rat_n_equiv_rat_n' (n : nat) : rat_n n.succ ≃ rat_n' n.succ :=
begin
  induction n with n hn,
  exact rat_1_equiv_rat_1',

  suffices H1 : rat_n n.succ.succ ≃ rat_n n.succ × rat,
  suffices H2 : rat_n' n.succ.succ ≃ rat_n' n.succ × rat',
    have e1 : rat_n n.succ × rat ≃ rat_n' n.succ × rat', apply equiv.prod_congr,
      exact hn, exact rat_equiv_rat',
    exact equiv.trans (equiv.trans H1 e1) H2.symm, swap, exact aux_rat_n n,

    have e2 := aux_rat_n' n, suffices H3 : rat_n (nat.succ n) × rat ≃ rat_n' (nat.succ n) × rat', exact equiv.trans e2 H3,
    apply equiv.prod_congr, exact hn, exact rat_equiv_rat',
end

def algebraic_set'_n (n : nat) : set real := ⋃ p : (poly_n' n.succ), roots_real p.1
def algebraic_set' : set real := ⋃ n : nat, algebraic_set'_n n.succ

theorem algebraic_set'_eq_algebraic_set : algebraic_set' = algebraic_set :=
begin
  ext, split; intro hx, 
  {
    rw [algebraic_set', set.mem_Union] at hx,
    choose n hx using hx,
    rw [algebraic_set'_n, set.mem_Union] at hx,
    choose p hp using hx, rw [roots_real, set.mem_set_of_eq] at hp,
    rw [algebraic_set, set.mem_set_of_eq, is_algebraic],
    use p.val, split, exact p.2.1,assumption
  },

  {
    rw [algebraic_set, set.mem_set_of_eq] at hx,
    choose p hp using hx,
    cases hp with p_ne_0 p_x_0,
    rw [algebraic_set', set.mem_Union],
    use p.nat_degree.succ, rw [algebraic_set'_n, set.mem_Union],
    use p, split, exact p_ne_0,
    {
      suffices h1 : p.nat_degree < p.nat_degree.succ,
      suffices h2 : p.nat_degree.succ < p.nat_degree.succ.succ,
      suffices h3 : p.nat_degree.succ.succ < p.nat_degree.succ.succ.succ,
      exact lt.trans (lt.trans h1 h2) h3,
      exact lt_add_one p.nat_degree.succ.succ, exact lt_add_one (nat.succ (polynomial.nat_degree p)),
      exact lt_add_one (polynomial.nat_degree p),
    },
    simpa,
  },
  done
end

theorem poly_n'_1_coeff_ne_0 (q : poly_n' 1) : q.1.coeff 0 ≠ 0 :=
begin
  have h := q.2,
  cases h with h1 h2,
  have h : q.1 = polynomial.C (q.1.coeff 0), ext,
  by_cases (n = 0), rw h, simp,
  rw polynomial.coeff_C, simp [h], rw polynomial.coeff_eq_zero_of_nat_degree_lt,
  suffices H : 1 ≤ n, linarith, replace h : n ≠ 0 := h, rw <-nat.lt_one_add_iff, norm_num, exact zero_lt_iff_ne_zero.mpr h,
  rw h, simp, intro absurd, conv_rhs at h {rw absurd}, suffices H2 : polynomial.C (0 : rat) = 0, conv_rhs at h {rw H2}, exact h1 h,
  ext, simp,
end

def identify'_1 : (poly_n' 1) -> rat' :=
begin
  intro q, split, swap, exact q.1.coeff 0, exact poly_n'_1_coeff_ne_0 q,
end

theorem rat_1_equiv_rat : rat_n 1 ≃ rat :=
begin
  constructor, swap 3, {
    intro f, exact f ⟨0, by linarith⟩,
  }, swap 3, {
    intros r m, exact r,
  }, {
    intros x, simp, ext, rename x_1 m, 
    have hm' : m.1 = 0, have hm1 := m.2, linarith,
    have hm : m = ⟨0, by linarith⟩, rw fin.ext_iff, simp, exact hm', rw hm,
  }, {
    intros x, simp,
  }
end

theorem rat_n_denumerable {n : nat} : denumerable (rat_n n.succ) :=
begin
  induction n with n hn,
  apply denumerable.mk', suffices H : rat_n 1 ≃ rat, apply equiv.trans H, exact denumerable.eqv rat,
  exact rat_1_equiv_rat,

  apply denumerable.mk',
  have Hn := @denumerable.eqv (rat_n (nat.succ n)) hn,
  have e1 := aux_rat_n n, suffices H : rat_n (nat.succ n) × ℚ ≃ nat, exact equiv.trans e1 H,
  have e2 : rat_n (nat.succ n) × ℚ ≃ nat × rat, apply equiv.prod_congr, exact Hn, refl,
  suffices H : ℕ × ℚ ≃ nat, exact equiv.trans e2 H, exact denumerable.eqv (ℕ × ℚ),
end

theorem poly_n'_denumerable (n : nat) : denumerable (poly_n' n.succ) :=
begin
  apply denumerable.mk',
  suffices e1 : rat_n' n.succ ≃ nat, exact equiv.trans (poly_n'_equiv_rat_n' n) e1,
  suffices e2 : rat_n n.succ ≃ nat, exact equiv.trans (rat_n_equiv_rat_n' n).symm e2,
  exact @denumerable.eqv _ (rat_n_denumerable),
  done
end

theorem algebraic_set'_n_countable (n : nat) : set.countable $ algebraic_set'_n n :=
begin
  rw algebraic_set'_n,
  have h := @set.countable_Union (poly_n' n.succ) real (fun p, roots_real p.1) (poly_n'_denumerable n).1,
  simp at h, apply h,
  intro q, apply set.countable_finite, exact roots_finite q.1 q.2.1,
  done
end

theorem algebraic_set'_countable : set.countable algebraic_set' :=
begin
  apply set.countable_Union,
  intro n, exact algebraic_set'_n_countable n.succ,
end

theorem countable_algebraic_set : set.countable algebraic_set :=
begin
  rw <-algebraic_set'_eq_algebraic_set, exact algebraic_set'_countable, done
end

def real_set : set real := @set.univ real

theorem transcendental_number_exists : ∃ x : real, ¬ (is_algebraic rat x) :=
begin
  have H : algebraic_set ≠ real_set,
  {
    intro h1,
    have h2 : set.countable real_set,
    {
      rw <-h1, exact countable_algebraic_set,
    },
    have h3 : ¬ set.countable real_set := cardinal.not_countable_real,
    exact h3 h2,
  },
  
  rw [ne.def, set.ext_iff, not_forall] at H,
  choose x Hx using H,
  rw not_iff at Hx,
  replace Hx := Hx.mpr,
  use x,
  exact Hx trivial,
  done
end

end project