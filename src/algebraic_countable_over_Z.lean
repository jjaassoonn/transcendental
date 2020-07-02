import data.set.basic set_theory.schroeder_bernstein
import data.set.countable
import ring_theory.algebraic
import data.polynomial
import data.rat.default
import data.real.basic data.real.cardinality
import tactic.linarith tactic.fin_cases

noncomputable theory
open_locale classical


namespace project
/--
- For the purpose of this project, we define a real number $x$ to be algebraic if and only if
there is a polynomial $p ∈ ℤ[T]$ such that $p(x)=0$. 

- `algebraic_set` is the set of all algebraic number in ℝ.
- For any polynomial $p ∈ ℤ[T]$, `roots_real p` is the set of real roots of $p$.
- `poly_int_to_poly_real` is the trivial ring homomorphism $ℤ[T] → ℝ[T]$.
- We are essentially evaluating polynomial in two ways: one is `polynomial.aeval` used in the definition of `is_algebraic`;
  the other is to evaluate the polynomial after the embeding `poly_int_to_poly_real`. The reason that we need two method is
  because the (mathlib) built-in `polynomial.roots` which gives us a `finset ℝ` for any $p ∈ ℝ[T]$.
  `poly_int_to_poly_real_wd` is assertion that the two evaluation methods produce the same results.
  `poly_int_to_poly_real_well_defined` proves the assertion.

- Having that the two evaluation methods agree, we can use `polynomial.roots` to show ∀ p ∈ ℤ[T], `roots_real p` is finite.
  This is `roots_finite`.
-/

def algebraic_set : set ℝ := {x | is_algebraic ℤ x }

def roots_real (p : polynomial ℤ) : set ℝ := {x | polynomial.aeval ℤ ℝ x p = 0}

def poly_int_to_poly_real (p : polynomial ℤ) : polynomial ℝ := polynomial.map (algebra_map ℤ ℝ) p

def poly_int_to_poly_real_wd (p : polynomial ℤ) : Prop := ∀ x : real, polynomial.aeval ℤ ℝ x p = (poly_int_to_poly_real p).eval x

theorem poly_int_to_poly_real_preserve_deg (p : polynomial ℤ) : p.degree = (poly_int_to_poly_real p).degree :=
begin
  rw [poly_int_to_poly_real],
  apply eq.symm, apply polynomial.degree_map_eq_of_injective,
  intros x y H, simp at H, exact H,
end

theorem poly_int_to_poly_real_C_wd' (a : int) : polynomial.C (a:ℝ) = poly_int_to_poly_real (polynomial.C a) :=
begin
  simp [poly_int_to_poly_real],
end

theorem poly_int_to_poly_real_C_wd : ∀ a : ℤ, poly_int_to_poly_real_wd (polynomial.C a) :=
begin
  intros r x,
  simp [poly_int_to_poly_real],
end

theorem poly_int_to_poly_real_add (p1 p2 : polynomial ℤ) : poly_int_to_poly_real (p1 + p2) = poly_int_to_poly_real p1 + poly_int_to_poly_real p2 :=
begin
  simp [poly_int_to_poly_real],
end

theorem poly_int_to_poly_real_add_wd (p1 p2 : polynomial ℤ) 
    (h1 : poly_int_to_poly_real_wd p1) 
    (h2 : poly_int_to_poly_real_wd p2) : poly_int_to_poly_real_wd (p1 + p2) :=
begin
  simp [poly_int_to_poly_real_wd] at h1 h2 ⊢,
  intro x,
  rw h1, rw h2,
  rw <-polynomial.eval_add,
  rw poly_int_to_poly_real_add,
  done
end

theorem poly_int_to_poly_real_pow1 (n : nat) : poly_int_to_poly_real (polynomial.X ^ n) = polynomial.X ^ n :=
begin
  ext, rename n_1 m,
  rw poly_int_to_poly_real, simp,
end

theorem poly_int_to_poly_real_pow2 (n : nat) (a : ℤ) : poly_int_to_poly_real ((polynomial.C a) * polynomial.X ^ n) = (polynomial.C (real.of_rat a)) * polynomial.X ^ n :=
begin
  ext, rename n_1 m,
  rw poly_int_to_poly_real, simp,
  done
end

theorem poly_int_to_poly_real_pow_wd (n : nat) (a : ℤ) (h : poly_int_to_poly_real_wd ((polynomial.C a) * polynomial.X ^ n)) : poly_int_to_poly_real_wd ((polynomial.C a) * polynomial.X ^ n.succ) :=
begin
  intro x,
  rw poly_int_to_poly_real_pow2,
  simp [polynomial.aeval_def],
  rw polynomial.eval₂_pow,
  rw <-polynomial.aeval_def,
  rw polynomial.aeval_X,
  done
end


theorem poly_int_to_poly_real_ne_zero (p : polynomial ℤ) : p ≠ 0 ↔ (poly_int_to_poly_real p) ≠ 0 :=
begin
  split,
  intros h hp,
  rw poly_int_to_poly_real at hp,
  rw polynomial.ext_iff at hp,
  have h' : p = 0, ext,
  replace hp := hp n,
  simp [polynomial.coeff_map] at hp ⊢, exact hp, exact h h',

  intros h hp,
  have h' : poly_int_to_poly_real p = 0,
  unfold poly_int_to_poly_real, exact (congr_arg (polynomial.map (algebra_map ℤ ℝ)) hp).trans rfl,
  exact h h',
end

theorem poly_int_to_poly_real_well_defined (x : real) (p : polynomial ℤ) :
    poly_int_to_poly_real_wd p :=
polynomial.induction_on
    p
    poly_int_to_poly_real_C_wd
    poly_int_to_poly_real_add_wd
    poly_int_to_poly_real_pow_wd

def roots_real' (p : polynomial ℤ) : set real := {x | (poly_int_to_poly_real p).eval x = 0}

theorem roots_real_eq_roots_real' (p : polynomial ℤ) : roots_real p = roots_real' p :=
begin
  ext, split; intro hx,
  unfold roots_real at hx,
  rw set.mem_set_of_eq at hx,
  unfold roots_real',
  rw set.mem_set_of_eq,
  have g := poly_int_to_poly_real_well_defined x p,
  unfold poly_int_to_poly_real_wd at g,
  have g' := g x,
  rw hx at g',
  exact eq.symm g',

  unfold roots_real' at hx,
  rw set.mem_set_of_eq at hx,
  rw roots_real,
  rw set.mem_set_of_eq,
  have g := poly_int_to_poly_real_well_defined x p,
  unfold poly_int_to_poly_real_wd at g,
  have g' := g x,
  rw hx at g',
  exact g',

  done
end

theorem roots_real'_eq_roots (p : polynomial ℤ) (hp : p ≠ 0) : roots_real' p = ↑((poly_int_to_poly_real p).roots) :=
begin
  ext,
  have g := @polynomial.mem_roots real x _ (poly_int_to_poly_real p) ((poly_int_to_poly_real_ne_zero p).mp hp),
  split,
  intro hx, rw roots_real' at hx, rw set.mem_set_of_eq at hx,
  simp, apply g.mpr, exact hx,

  intro hx, simp at hx, unfold roots_real', rw set.mem_set_of_eq,
  exact g.mp hx,
  done
end

theorem roots_real_eq_roots (p : polynomial ℤ) (hp : p ≠ 0) : roots_real p = ↑((poly_int_to_poly_real p).roots) :=
begin
  rw [roots_real_eq_roots_real', roots_real'_eq_roots], assumption, done
end

theorem roots_finite (p : polynomial ℤ) (hp : p ≠ 0) : set.finite (roots_real p) :=
begin
  rw roots_real_eq_roots,
  split, exact additive.fintype, assumption,
end


-- Part I of project

/-- 
We allow the zero polynomial to have degree zero.
Otherwise we need to use type `with_bot ℕ` so that the zero polynomial has degree negative infinity
-/

def nat_set : set nat := @set.univ nat                                            -- the set of natural numbers

def int_n (n : nat) := fin n -> ℤ                                                 -- the set of ℤⁿ
def nat_n (n : nat) := fin n -> ℕ                                                 -- the set of ℕⁿ
def poly_n (n : nat) := {x : polynomial ℤ // x.nat_degree < n}                    -- the set of all polynomials in $ℤ[T]$ with degree < n
def poly_n' (n : nat) := {p : polynomial ℤ // p ≠ 0 ∧ p.nat_degree < n}           -- the set of all nonzero polynomials in $ℤ[T]$ with degree < n
def int_n' (n : nat) := {f : fin n -> ℤ // f ≠ 0}                                 -- ℤⁿ - {(0,0,...,0)}
def int' := {r : int // r ≠ 0}                                                    -- ℤ - {0}

def strange_fun : ℤ -> int' :=                                                    -- This is the bijection from ℤ to ℤ - {0}
begin
    intro m,                                                                      -- Given by
    constructor, swap, exact (ite (m<0) m (m+1)),                                 --      | n     if n < 0
    intro rid, split_ifs at rid, linarith, linarith,                              -- n ↦ -|
end                                                                               --      | n + 1 if n ≥ 0

theorem strange_fun_inj : function.injective strange_fun :=                       -- This is the proof that the strange function is injective
begin
    intros x y H, rw strange_fun at H, simp at H, split_ifs at H, 
    exact H, linarith, linarith, simp at H, exact H,
end

theorem int_eqiv_int' : ℤ ≃ int' :=                                               -- So ℤ ≃ ℤ - {0} because the strange function is a bijection
begin
  suffices H : ∃ f : int -> int', function.bijective f,
  choose f Hf using H, exact equiv.of_bijective Hf,
  use strange_fun,
  split,
  {
      exact strange_fun_inj,                                                      -- The injection part is proved above
  },
  {
      intro x,                                                                    -- The surjection part:
      by_cases (x.val < 0),                                                       -- For any x ∈ ℤ - {0}
                                                                                  
      use x.val, simp [strange_fun], simp [h], simp at h,                         -- if x < 0 then x ↦ x
      replace h : 0 = x.val ∨ 0 < x.val, exact eq_or_lt_of_le h, cases h,
      replace h := eq.symm h,
      exfalso, exact x.property h,
      replace h : 1 ≤ x.val, exact h,
      replace h : ¬ (1 > x.val), exact not_lt.mpr h,
      replace h : ¬ (x.val < 1), exact h,
      use x.val-1,                                                                -- if x ≥ 0 since x ≠ 0, we have x > 0
      simp [strange_fun], simp [h],                                               -- then x - 1 ↦ x
  },
end

def zero_int_n {n : nat} : int_n n.succ := (fun m, 0)                             -- ℤ⁰ = {0}
def zero_poly_n {n : nat} : poly_n n.succ := ⟨0, nat.succ_pos n⟩                  -- no polynomial in $ℤ[T]$ with degree < 0

def identify (n : nat) : (poly_n n) -> (int_n n) :=                               -- Given a integer polynomial of degree < n,
begin                                                                             -- we identify it with its coefficients as in ℤⁿ
  intro p,
  intro m,
  exact p.val.coeff m.val,
  done
end

@[simp] theorem identify_0_eq_0 (n : nat) : (identify n.succ zero_poly_n) = zero_int_n :=
begin
 rw [identify, zero_int_n, zero_poly_n], ext, simp, done
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
    rw [(@polynomial.coeff_eq_zero_of_nat_degree_lt int _ p1.val n p1_deg),
        (@polynomial.coeff_eq_zero_of_nat_degree_lt int _ p2.val n p2_deg)],
  },

  -- n < m
  {
    rw @polynomial.coeff_eq_zero_of_nat_degree_lt int _ p1.val m (lt.trans p1_deg ineq),
    rw @polynomial.coeff_eq_zero_of_nat_degree_lt int _ p2.val m (lt.trans p2_deg ineq),
  }
end

theorem identify_nzero_to_nzero (n : nat) (p : poly_n n.succ) (hp : p ≠ zero_poly_n) : (identify n.succ p) ≠ zero_int_n :=
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
    let support : finset ℕ := finset.filter (λ m : nat, (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n),
    have hsupport : support = finset.filter (λ m : nat, (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n) := rfl,

    let to_fun : nat -> ℤ := (λ m : nat, ite (m ∈ support) (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) 0),
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
      rw hto_fun, simp,
      
      split_ifs,
      exact qm_ne_0,

      rw [not_and] at h, simp at hm'_left,
      replace h := h hm'_left, simp at h, exfalso, exact qm_ne_0 h,

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
        have h' : (0 : ℤ) = 0 := rfl,
        exact h h',
      },
      exact g hm',
    },
    let p : polynomial ℤ := ⟨support, to_fun, mem_support_to_fun⟩,
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


theorem poly_n'_equiv_int_n' (n : nat) : poly_n' n.succ ≃ int_n' n.succ :=
begin
  let f : (poly_n' n.succ) -> (int_n' n.succ),
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
    
    replace h : m < n.succ,
    exact not_le.mp h,
    rw hx ⟨m, h⟩,
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

  def f : int_n 1 -> int_n' 1 :=
  begin
    intro r, split, swap, exact (fun m, ite ((r m) < 0) (r m) ((r m)+1)),
    intro rid,
    replace rid : (λ (m : fin 1), ite (r m < 0) (r m) (r m + 1)) 0 = 0, exact (congr_fun rid 0).trans rfl,
    simp at rid, by_cases (r 0 < 0), simp [h] at rid, linarith,
    simp [h] at rid, linarith,
  end


  def g : int_n' 1 -> int_n 1 :=
  begin
    intros g n, exact g.1 n,
  end

theorem int_1_equiv_int_1' : int_n 1 ≃ int_n' 1 :=
begin
  suffices H1 : ∃ f : int_n 1 -> int_n' 1, function.bijective f,
    choose h hh using H1,
    exact equiv.of_bijective hh,

  suffices H2 : ∃ f : int_n 1 -> int_n' 1, ∃ g : int_n' 1 -> int_n 1, function.injective f ∧ function.injective g,
    choose f g h using H2, exact function.embedding.schroeder_bernstein h.1 h.2,

  use f, use g, split,
  {
    intros x1 x2 hx, ext, simp [f] at hx, 
    replace hx := function.funext_iff.1 hx, replace hx := hx 0, fin_cases x,
    split_ifs at hx, exact hx, simp at h_1,
    have h2 : 0 ≤ x2 0 + 1, exact add_nonneg h_1 trivial, rw <-hx at h2,
    replace h2 : 0 = x1 0 ∨ 0 < x1 0, exact eq_or_lt_of_le h2, cases h2, rw <-h2 at h, linarith, linarith,
    
    simp at h, replace h : 0 = x1 0 ∨ 0 < x1 0, exact eq_or_lt_of_le h,
    cases h, rw <-h at hx, simp at hx, linarith,

    have ineq : x1 0 + 1 > 1, exact sub_lt_iff_lt_add.mp h, rw hx at ineq, linarith, simp at hx, exact hx,
  },
  {
    intros x1 x2 hx, simp [g] at hx, replace hx := subtype.eq hx, exact hx,
  }
end


def fn {n : nat} : int_n (nat.succ (nat.succ n)) -> int_n (nat.succ n) × ℤ :=
begin
  intro r, split, intro m, exact r (⟨m.1, nat.lt_trans m.2 (nat.lt_succ_self n.succ)⟩ : fin n.succ.succ),
  exact r (⟨n.succ, nat.lt_succ_self n.succ⟩ : fin n.succ.succ),
end

def gn {n : nat} : int_n (nat.succ n) × ℤ -> int_n (nat.succ (nat.succ n)) :=
begin
  intros r m, cases r with p r,
  by_cases (m.1 = n.succ), exact r,
    have hm' := m.2,
    have hm : m.1 < n.succ,
    replace hm : m.1 ≤ n.succ, exact fin.le_last m, exact lt_of_le_of_ne hm h,
    exact p (⟨m.1, hm⟩ : fin n.succ),
end

theorem aux_int_n (n : nat) : int_n (nat.succ (nat.succ n)) ≃ int_n (nat.succ n) × ℤ :=
begin
  suffices H1 : ∃ f : int_n n.succ.succ -> int_n n.succ × ℤ, function.bijective f,
    choose h hh using H1,
    exact equiv.of_bijective hh,

  suffices H2 : ∃ f : int_n n.succ.succ -> int_n n.succ × ℤ, ∃ g : int_n n.succ × ℤ -> int_n n.succ.succ, function.injective f ∧ function.injective g,
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
end

def fn' {n : nat} : int_n' (nat.succ (nat.succ n)) -> int_n (nat.succ n) × ℤ := 
begin
  intro p, split, intro m,
  exact p.1 (⟨m.1, nat.lt_trans m.2 (nat.lt_succ_self n.succ)⟩ : fin n.succ.succ),
  exact p.1 (⟨n.succ, nat.lt_succ_self n.succ⟩ : fin n.succ.succ),
end

def gn' {n : nat} : int_n (nat.succ n) × ℤ -> int_n' (nat.succ (nat.succ n)) :=
begin
  intro x,
  split, swap 2, intro m,
  by_cases (m.1 = n.succ), exact (strange_fun x.2).1,
    have H2 : m.1 < n.succ,  have H2' := fin.le_last m, exact lt_of_le_of_ne H2' h,
    exact (strange_fun (x.1 ⟨m.1, H2⟩)).1,

  intro rid, rw function.funext_iff at rid, simp at rid,
  have ineq : n.succ < n.succ.succ, exact lt_add_one (nat.succ n),
  replace rid := rid ⟨n.succ, ineq⟩, split_ifs at rid,
  have contra := (strange_fun x.snd).property, simp at contra, exact contra rid,

  simp at h, exact h,
end

lemma about_gt (m n : ℕ) (h : m < n) : m < n.succ := by exact nat.lt.step h

theorem gn'_inj {n : ℕ} : function.injective (@gn' n) :=
begin
    intros x y H, simp [gn'] at H, rw function.funext_iff at H, ext, rename x_1 m,
    have ineq : m.val < n.succ.succ,
    {
        exact nat.lt.step m.is_lt,
    },
    generalize hm' : @fin.cast_lt n.succ.succ n.succ m ineq = m',
    replace H := H m', split_ifs at H,
    have eq1 : m'.val = m.val,
    {
        rw <-hm', simp,
    }, rw eq1 at h, have rid := m.is_lt, linarith, rw <-subtype.ext at H,
    have eq1 := strange_fun_inj H, have eq2 : m'.val = m.val, rw <-hm', simp,
    have eq3 : x.1 m = x.fst ⟨m'.val, _⟩,
    {
        apply congr_arg, rw fin.eq_iff_veq, simp, rw eq2,
    }, rw eq3, rw eq1, apply congr_arg, rw fin.eq_iff_veq, simp, rw eq2,
    
    have ineq2 : n.succ < n.succ.succ, exact lt_add_one (nat.succ n),
    replace H := H ⟨n.succ, ineq2⟩, split_ifs at H, rw <-subtype.ext at H,
    exact strange_fun_inj H, rw <-subtype.ext at H,
    simp at h, exfalso, exact h,
end


theorem aux_int_n' (n : nat) : int_n' (nat.succ (nat.succ n)) ≃ int_n (nat.succ n) × ℤ :=
begin
  suffices H1 : ∃ f : int_n' n.succ.succ -> int_n n.succ × ℤ, function.bijective f,
    choose h hh using H1,
    exact equiv.of_bijective hh,

  suffices H2 : ∃ f : int_n' n.succ.succ -> int_n n.succ × ℤ, ∃ g : int_n n.succ × ℤ -> int_n' n.succ.succ, function.injective f ∧ function.injective g,
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
    exact gn'_inj,
  }
end

theorem int_n_equiv_int_n' (n : nat) : int_n n.succ ≃ int_n' n.succ :=
begin
  induction n with n hn,
  exact int_1_equiv_int_1',

  suffices H1 : int_n n.succ.succ ≃ int_n n.succ × ℤ,
  suffices H2 : int_n' n.succ.succ ≃ int_n' n.succ × int',
    have e1 : int_n n.succ × ℤ ≃ int_n' n.succ × int', apply equiv.prod_congr,
      exact hn, exact int_eqiv_int',
    exact equiv.trans (equiv.trans H1 e1) H2.symm, swap, exact aux_int_n n,

    have e2 := aux_int_n' n, suffices H3 : int_n (nat.succ n) × int ≃ int_n' (nat.succ n) × int', exact equiv.trans e2 H3,
    apply equiv.prod_congr, exact hn, exact int_eqiv_int',
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
  rw h, simp, intro absurd, conv_rhs at h {rw absurd}, suffices H2 : polynomial.C (0 : int) = 0, conv_rhs at h {rw H2}, exact h1 h,
  ext, simp,
end

def identify'_1 : (poly_n' 1) -> int' :=
begin
  intro q, split, swap, exact q.1.coeff 0, exact poly_n'_1_coeff_ne_0 q,
end

theorem int_1_equiv_int : int_n 1 ≃ ℤ :=
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

theorem int_n_denumerable {n : nat} : denumerable (int_n n.succ) :=
begin
  induction n with n hn,
  apply denumerable.mk', suffices H : int_n 1 ≃ ℤ, apply equiv.trans H, exact denumerable.eqv ℤ,
  exact int_1_equiv_int,

  apply denumerable.mk',
  have Hn := @denumerable.eqv (int_n (nat.succ n)) hn,
  have e1 := aux_int_n n, suffices H : int_n (nat.succ n) × ℤ ≃ nat, exact equiv.trans e1 H,
  have e2 : int_n (nat.succ n) × ℤ ≃ nat × ℤ, apply equiv.prod_congr, exact Hn, refl,
  suffices H : ℕ × ℤ ≃ nat, exact equiv.trans e2 H, exact denumerable.eqv (ℕ × ℤ),
end

theorem poly_n'_denumerable (n : nat) : denumerable (poly_n' n.succ) :=
begin
  apply denumerable.mk',
  suffices e1 : int_n' n.succ ≃ nat, exact equiv.trans (poly_n'_equiv_int_n' n) e1,
  suffices e2 : int_n n.succ ≃ nat, exact equiv.trans (int_n_equiv_int_n' n).symm e2,
  exact @denumerable.eqv (int_n n.succ) int_n_denumerable,
end

theorem algebraic_set'_n_countable (n : nat) : set.countable $ algebraic_set'_n n :=
begin
  rw algebraic_set'_n,
  have h := @set.countable_Union (poly_n' n.succ) real (fun p, roots_real p.1) (poly_n'_denumerable n).1,
  simp at h, apply h,
  intro q, apply set.finite.countable, exact roots_finite q.1 q.2.1,
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

theorem transcendental_number_exists : ∃ x : real, ¬ (is_algebraic ℤ x) :=
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