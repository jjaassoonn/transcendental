import ring_theory.algebraic
import data.real.cardinality
import tactic

noncomputable theory
open_locale classical

/--
- For the purpose of this project, we define a real number $x$ to be algebraic if and only if
there is a non-zero polynomial $p ∈ ℤ[T]$ such that $p(x)=0$. 

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
  intros x y H, simp only [ring_hom.eq_int_cast, int.cast_inj] at H, exact H,
end

theorem poly_int_to_poly_real_C_wd' (a : int) : polynomial.C (a:ℝ) = poly_int_to_poly_real (polynomial.C a) := 
begin
  simp only [poly_int_to_poly_real], rw polynomial.map_C, ext, simp only [ring_hom.eq_int_cast],
end

theorem poly_int_to_poly_real_C_wd : ∀ a : ℤ, poly_int_to_poly_real_wd (polynomial.C a) := λ _ _, by simp only [poly_int_to_poly_real, polynomial.map_C, polynomial.eval_C, polynomial.aeval_C]
theorem poly_int_to_poly_real_add (p1 p2 : polynomial ℤ) : poly_int_to_poly_real (p1 + p2) = poly_int_to_poly_real p1 + poly_int_to_poly_real p2 :=
begin
  simp only [poly_int_to_poly_real, polynomial.map_add],
end

theorem poly_int_to_poly_real_add_wd (p1 p2 : polynomial ℤ) 
    (h1 : poly_int_to_poly_real_wd p1) 
    (h2 : poly_int_to_poly_real_wd p2) : poly_int_to_poly_real_wd (p1 + p2) :=
begin
  simp only [poly_int_to_poly_real_wd, alg_hom.map_add] at h1 h2 ⊢,
  intro x,
  rw [h1, h2, <-polynomial.eval_add, poly_int_to_poly_real_add]
end

theorem poly_int_to_poly_real_pow1 (n : nat) : poly_int_to_poly_real (polynomial.X ^ n) = polynomial.X ^ n :=
begin
  ext m,
  simp only [poly_int_to_poly_real, polynomial.map_X, polynomial.map_pow],
end

theorem poly_int_to_poly_real_pow2 (n : nat) (a : ℤ) : poly_int_to_poly_real ((polynomial.C a) * polynomial.X ^ n) = (polynomial.C (real.of_rat a)) * polynomial.X ^ n :=
begin
  rw [poly_int_to_poly_real, polynomial.map_mul, polynomial.map_C, polynomial.map_pow, polynomial.map_X], simp only [ring_hom.eq_int_cast, rat.cast_coe_int, real.of_rat_eq_cast],
end

theorem poly_int_to_poly_real_pow_wd (n : nat) (a : ℤ) (h : poly_int_to_poly_real_wd ((polynomial.C a) * polynomial.X ^ n)) : poly_int_to_poly_real_wd ((polynomial.C a) * polynomial.X ^ n.succ) :=
begin
  intro x,
  rw [polynomial.aeval_def, poly_int_to_poly_real, polynomial.map_mul, polynomial.map_C, polynomial.eval_mul, polynomial.eval_C, polynomial.map_pow, polynomial.eval_pow, polynomial.eval₂_mul, polynomial.eval₂_C, polynomial.eval₂_pow], 
  simp only [polynomial.eval_X, polynomial.map_X, polynomial.eval₂_X],
end


theorem poly_int_to_poly_real_ne_zero (p : polynomial ℤ) : p ≠ 0 ↔ (poly_int_to_poly_real p) ≠ 0 :=
begin
  split,
  intros h hp,
  rw poly_int_to_poly_real at hp,
  rw polynomial.ext_iff at hp,
  have h' : p = 0, ext,
  replace hp := hp n,
  simp only [polynomial.coeff_map, int.cast_eq_zero, ring_hom.eq_int_cast, polynomial.coeff_zero] at hp ⊢, exact hp, exact h h',

  intros h hp,
  have h' : poly_int_to_poly_real p = 0, unfold poly_int_to_poly_real, exact (congr_arg (polynomial.map (algebra_map ℤ ℝ)) hp).trans rfl,
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
  rwa hx at g',
end

theorem roots_real'_eq_roots (p : polynomial ℤ) (hp : p ≠ 0) : roots_real' p = ↑((poly_int_to_poly_real p).roots) :=
begin
  ext,
  have g := @polynomial.mem_roots real x _ (poly_int_to_poly_real p) ((poly_int_to_poly_real_ne_zero p).mp hp),
  split,
  intro hx, rw roots_real' at hx, rw set.mem_set_of_eq at hx,
  simp only [finset.mem_coe], apply g.mpr, exact hx,

  intro hx, simp only [finset.mem_coe] at hx, unfold roots_real', rw set.mem_set_of_eq,
  exact g.mp hx,
end

theorem roots_real_eq_roots (p : polynomial ℤ) (hp : p ≠ 0) : roots_real p = ↑((poly_int_to_poly_real p).roots) :=
begin
  rw [roots_real_eq_roots_real', roots_real'_eq_roots], assumption,
end

theorem roots_finite (p : polynomial ℤ) (hp : p ≠ 0) : set.finite (roots_real p) :=
begin
  rw roots_real_eq_roots,
  split, exact additive.fintype, assumption,
end

/-- 
We allow the zero polynomial to have degree zero.
Otherwise we need to use type `with_bot ℕ` so that the zero polynomial has degree negative infinity
-/

def nat_set : set nat := @set.univ nat                                            -- the set of natural numbers

notation `int_n` n := fin n -> ℤ                                                  -- the set of ℤⁿ
notation `nat_n` n := fin n -> ℕ                                                  -- the set of ℕⁿ
notation `poly_n` n := {x : polynomial ℤ // x.nat_degree < n}                     -- the set of all polynomials in $ℤ[T]$ with degree < n
notation `poly_n'` n := {p : polynomial ℤ // p ≠ 0 ∧ p.nat_degree < n}            -- the set of all nonzero polynomials in $ℤ[T]$ with degree < n
notation `int_n'` n := {f : fin n -> ℤ // f ≠ 0}                                  -- ℤⁿ - {(0,0,...,0)}
notation `int'` := {r : ℤ // r ≠ 0}                                                    -- ℤ - {0}

def strange_fun : ℤ -> int' := λ m, if h : m < 0 then ⟨m, by linarith⟩ else ⟨m + 1, by linarith⟩                                                 
-- This is the bijection from ℤ to ℤ - {0}
 -- Given by
--      | n     if n < 0
-- n ↦ -|
--      | n + 1 if n ≥ 0

theorem strange_fun_inj : function.injective strange_fun :=                       -- This is the proof that the strange function is injective
begin
    intros x y H, rw strange_fun at H, simp only [subtype.mk_eq_mk] at H, split_ifs at H, 
    exact H, linarith, linarith, 
    simp only [subtype.mk_eq_mk, add_left_inj] at H, exact H,
end

theorem int_eqiv_int' : ℤ ≃ int' :=                                               -- So ℤ ≃ ℤ - {0} because the strange function is a bijection
begin
  suffices H : ∃ f : ℤ -> int', function.bijective f,
  choose f Hf using H, exact equiv.of_bijective f Hf,
  use strange_fun,
  split,
  {
      exact strange_fun_inj,                                                      -- The injection part is proved above
  },
  {
      intro x,                                                                    -- The surjection part:
      by_cases (x.val < 0),                                                       -- For any x ∈ ℤ - {0}
                                                                                  
      use x.val, simp only [strange_fun], simp only [h, if_true, subtype.eta, dif_pos], simp only [not_lt] at h,                      -- if x < 0 then x ↦ x
      replace h : 0 = x.val ∨ 0 < x.val, exact eq_or_lt_of_le h, cases h,
      replace h := eq.symm h,
      exfalso, exact x.property h,
      replace h : 1 ≤ x.val, exact h,
      replace h : ¬ (1 > x.val), exact not_lt.mpr h,
      replace h : ¬ (x.val < 1), exact h,
      use x.val-1,                                                                -- if x ≥ 0 since x ≠ 0, we have x > 0
      simp only [strange_fun, h, sub_lt_zero, sub_add_cancel, subtype.eta, if_false, sub_lt_zero, dif_neg, not_false_iff],                                            -- then x - 1 ↦ x
  },
end

def zero_int_n {n : nat} : int_n n.succ := (fun m, 0)                             -- ℤ⁰ = {0}
def zero_poly_n {n : nat} : poly_n n.succ := ⟨0, nat.succ_pos n⟩                  -- no polynomial in $ℤ[T]$ with degree < 0

def identify (n : nat) : (poly_n n) -> (int_n n) := λ p m, p.val.coeff m.val      -- Given a integer polynomial of degree < n,
                                                                                  -- we identify it with its coefficients as in ℤⁿ


@[simp] theorem identify_0_eq_0 (n : nat) :                                       -- so the zero polynomial is 0
  (identify n.succ zero_poly_n) = zero_int_n :=
begin
 rw [identify, zero_int_n, zero_poly_n], ext, simp only [polynomial.coeff_zero],
end

lemma m_mod_n_lt_n : ∀ n : nat, n ≠ 0 -> ∀ m : nat, m % n < n :=                  -- the remainder of m dividing n is smaller than n
begin
  intros n hn m,
  have hn' : 0 < n := zero_lt_iff_ne_zero.mpr hn,
  exact @nat.mod_lt m n hn',
end

theorem inj_identify_n :                                                          -- identification is injective:
  ∀ n : nat, (n ≠ 0) -> function.injective (identify n) :=                        -- different polynomial is identified with different m-tuple
begin                                                                             -- because all the coefficients are the same
  intros n hn,                                                      
  intros p1 p2 h,                                                                 -- given two polynomials p1 p2 and the assumption that 
  unfold identify at h,                                                           -- p1 and p2 are identified to the same tuple                                                                     -- we have that ∀ m < n, the mth coefficient of p1 equals to
  rw subtype.ext_iff_val,                                                         -- the mth coefficient of p2
  ext m,                                                                          -- we need to prove ∀ m ∈ ℕ, the mth coefficient of p1 equals to
  rw function.funext_iff at h,                                                    -- the mth coefficent of p2. So we take an arbitrary m ∈ ℕ.
  have p1_deg := p1.property,                                                     
  have p2_deg := p2.property,                                                     -- p1 and p2 both have degree < n

  -- consider m = n, m < n, m > n seprately,
  cases (nat.lt_trichotomy m n) with ineq,
  -- m < n
  {
    let m' := (⟨m, ineq⟩ : fin n),                                                -- for m < n, it is proved using the assumption above.
    have h_m := h m',
    have g : m'.val = m := rfl,
    rw [<-g, h_m],
  },
  rename h_1 ineq, cases ineq,

  -- m = n
  {                                                                               -- for m = n, lhs = rhs = 0
    rw [ineq, (@polynomial.coeff_eq_zero_of_nat_degree_lt ℤ _ p1.val n p1_deg), (@polynomial.coeff_eq_zero_of_nat_degree_lt ℤ _ p2.val n p2_deg)],
  },

  -- n < m
  {
    rw [@polynomial.coeff_eq_zero_of_nat_degree_lt ℤ _                             -- for m > n, lhs = rhs = 0
          p1.val m (lt.trans p1_deg ineq), 
        @polynomial.coeff_eq_zero_of_nat_degree_lt ℤ _ 
          p2.val m (lt.trans p2_deg ineq)],
  }
end

theorem identify_nzero_to_nzero (n : nat) (p : poly_n n.succ) (hp : p ≠ zero_poly_n) : 
  (identify n.succ p) ≠ zero_int_n :=                                             -- non-zero polynomial is sent to non-zero tuple
begin                                                                             -- so the identification process descends to identify
  have g := inj_identify_n n.succ (nat.succ_ne_zero n),                           -- non-zero polynomial with non-zero tuple
  have g' := @g p zero_poly_n, simp only [identify_0_eq_0] at g',
  intro absurd, exact hp (g' absurd),
end

theorem sur_identify_n : ∀ n : nat, (n ≠ 0) -> function.surjective (identify n) :=
begin                                                                                                                             -- identifunction is also surjective
    intros n hn,
    intro q,
    -- we can define a polynomial whose non-zero coefficients are exact at non-zero elements of q;                                                                                                                     -- given an element q in ℤⁿ
    let p : polynomial ℤ := { support := finset.filter (λ m : nat, (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n), 
      to_fun := (λ m : nat, ite (m ∈ (finset.filter (λ m : nat, (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n))) (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) 0),
      mem_support_to_fun := begin
        intro m,                                                                                                                    -- every index with a non-zero coefficient is in support
        split,
        intro hm,
        rw finset.mem_filter at hm,
        cases hm with hm_left qm_ne0,
        simp only [ne.def, finset.mem_filter, finset.mem_range, ne.def, finset.mem_filter, finset.mem_range],
      
        split_ifs,
        exact h.2,

        simp only [not_and, classical.not_not] at h, simp only [finset.mem_range] at hm_left,
        replace h := h hm_left, exfalso, exact qm_ne0 h,

        intro hm,
        dsimp at hm,
        have g : ite (m ∈ (finset.filter (λ m : nat, (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n))) (q ⟨m % n, m_mod_n_lt_n n hn m⟩) 0 ≠ 0 -> (m ∈ (finset.filter (λ m : nat, (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n))),
        {
          intro h,
          by_contra,
          split_ifs at h,
          have h' : (0 : ℤ) = 0 := rfl,
          exact h h',
        },
        exact g hm,
      end},
    have hp_support2 : ∀ m ∈ p.support, m < n,                                                         
    {
      dsimp,
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

    have hp_nat_deg : p.nat_degree < n,                                           -- So the polynomial has degree < n
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

    use ⟨p, hp_nat_deg⟩,                                                          -- We claim that this polynomial is identified with q
    {
      ext m,
      simp only [identify, polynomial.coeff_mk],
      split_ifs,                                                                  -- So we need to prove that forall m, coefficient at m equals the corresponding elements of q
                                                                                  -- So we separate this into two cases: m ∈ support and m ∉ support
      -- m.val ∈ support                                                                             
      {
        simp only [ne.def, finset.mem_filter, finset.mem_range] at h,
        cases h,
        have important : m = ⟨m.1 % n, _⟩,                                        -- If m ∈ support, true by our choice of polynomial
        {
          ext,
          simp only [],
          rw nat.mod_eq_of_lt,
          exact h_left,
        },
        rw <-important,
      },
      -- m.val ∉ support
      {
        simp only [not_and, finset.mem_filter, finset.mem_range, classical.not_not] at h,                                                                -- If m ∉ support, then lhs = rhs = 0
        have h' := h m.2,
        have important : m = ⟨m.1 % n, _⟩,
        {
          rw fin.ext_iff,
          simp only [],
          rw nat.mod_eq_of_lt,
          exact m.2,
        },
        rw <-important at h',
        exact eq.symm h',
      },
    },
end


theorem poly_n'_equiv_int_n' (n : nat) : (poly_n' n.succ) ≃ (int_n' n.succ) :=    -- We use the fact that identification is bijection to prove
begin                                                                             -- that non-zero polynomial of degree < n is equipotent to ℤⁿ for n ≥ 1
  let f : (poly_n' n.succ) -> (int_n' n.succ),
  {
    intro p,
    generalize hx : (identify n.succ) ⟨p.1, p.2.2⟩ = x,
    split, swap, exact x,
    have g := identify_nzero_to_nzero n ⟨p.1, p.2.2⟩ _,
    rw hx at g, exact g, rw [zero_poly_n], simp only [subtype.mk_eq_mk, ne.def], exact p.2.1,
  },

  suffices f_bij : function.bijective f,
  exact equiv.of_bijective f f_bij,
  split,
  {
    intros x1 x2 hx, simp only [subtype.mk_eq_mk, identify, function.funext_iff] at hx, apply subtype.eq,
    ext m,
    have h1 := x1.2.2, have h2 := x2.2.2,
    by_cases (m ≥ n.succ),
    rw [polynomial.coeff_eq_zero_of_nat_degree_lt, polynomial.coeff_eq_zero_of_nat_degree_lt],
    exact lt_of_lt_of_le h2 h, exact lt_of_lt_of_le h1 h, 
    
    replace h : m < n.succ, exact not_le.mp h,
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
    simp only [subtype.ext_iff_val, subtype.eta], assumption,
  },
end

def f : (int_n 1) -> (int_n' 1) :=                                                -- This is an injective function from ℤ to ℤ - {0}
begin
  intro r, split, swap, exact (fun m, ite ((r m) < 0) (r m) ((r m)+1)),
  intro rid,
  replace rid : (λ (m : fin 1), ite (r m < 0) (r m) (r m + 1)) 0 = 0, exact (congr_fun rid 0).trans rfl,
  simp only [] at rid, by_cases (r 0 < 0), 
    simp only [h, if_true] at rid, linarith,
    simp only [h, if_false] at rid, linarith,
end


def g : (int_n' 1) -> (int_n 1) := λ h n, h.1 n                                   -- This is an injective function from ℤ - {0} to ℤ

theorem int_1_equiv_int_1' : (int_n 1) ≃ (int_n' 1) :=                            -- We use the two injective functions and Schröder-Berstein theorem
begin                                                                             -- to prove ℤ ≃ ℤ - {0}
  suffices H1 : ∃ f : (int_n 1) -> (int_n' 1), function.bijective f,
    choose h hh using H1,
    exact equiv.of_bijective h hh,

  suffices H2 : ∃ f : (int_n 1) -> (int_n' 1), ∃ g : (int_n' 1) -> (int_n 1), function.injective f ∧ function.injective g,
    choose f g h using H2, exact function.embedding.schroeder_bernstein h.1 h.2,

  use f, use g, split,
  {
    intros x1 x2 hx, ext, simp only [f, subtype.mk_eq_mk] at hx, 
    replace hx := function.funext_iff.1 hx, replace hx := hx 0, fin_cases x,
    split_ifs at hx, exact hx, simp only [not_lt] at h_1,
    have h2 : 0 ≤ x2 0 + 1, exact add_nonneg h_1 trivial, rw <-hx at h2,
    replace h2 : 0 = x1 0 ∨ 0 < x1 0, exact eq_or_lt_of_le h2, cases h2, rw <-h2 at h, linarith, linarith,
    
    simp only [not_lt] at h, replace h : 0 = x1 0 ∨ 0 < x1 0, exact eq_or_lt_of_le h,
    cases h, rw <-h at hx, simp only [zero_add] at hx, linarith,

    have ineq : x1 0 + 1 > 1, exact sub_lt_iff_lt_add.mp h, rw hx at ineq, linarith, simp only [add_left_inj] at hx, exact hx,
  },
  {
    intros x1 x2 hx, simp only [g, id.def] at hx, exact subtype.eq hx,
  }
end


def fn {n : nat} : (int_n n.succ.succ) -> (int_n n.succ) × ℤ :=                   -- This is an injection from ℤ^{n+1} to ℤⁿ × ℤ for n ≥ 1
begin
  intro r, split, intro m, exact r (⟨m.1, nat.lt_trans m.2 (nat.lt_succ_self n.succ)⟩),
  exact r (⟨n.succ, nat.lt_succ_self n.succ⟩),
end

def gn {n : nat} : (int_n n.succ) × ℤ -> (int_n n.succ.succ) :=                   -- This is an injection from ℤⁿ × ℤ to ℤ^{n+1} for n ≥ 1
begin
  intros r m, cases r with p r,
  by_cases (m.1 = n.succ), exact r,
    have hm' := m.2,
    have hm : m.1 < n.succ,
    replace hm : m.1 ≤ n.succ, exact fin.le_last m, exact lt_of_le_of_ne hm h,
    exact p (⟨m.1, hm⟩ : fin n.succ),
end

theorem aux_int_n (n : nat) :                                                     -- So again using the two injections and Schröder-Berstein
  (int_n n.succ.succ) ≃ (int_n n.succ) × ℤ :=                       -- We know ℤⁿ × ℤ ≃ ℤ^{n+1} for n ≥ 1
begin
  suffices H1 : ∃ f : (int_n n.succ.succ) -> (int_n n.succ) × ℤ, function.bijective f,
    choose h hh using H1,
    exact equiv.of_bijective h hh,

  suffices H2 : ∃ f : (int_n n.succ.succ) -> (int_n n.succ) × ℤ, ∃ g : (int_n n.succ) × ℤ -> (int_n n.succ.succ), function.injective f ∧ function.injective g,
    choose f g h using H2, exact function.embedding.schroeder_bernstein h.1 h.2,

  use fn, use gn, split,
  {
    intros x1 x2 hx, simp only [fn, id.def, prod.mk.inj_iff] at hx, cases hx with h1 h2, rw function.funext_iff at h1, ext,
    by_cases (x = ⟨n.succ, nat.lt_succ_self n.succ⟩), rw <-h at h2, assumption,
      simp only [fin.eq_iff_veq] at h, have h2 := x.2, replace h2 : x.1 ≤ n.succ := fin.le_last x,
      have h3 : x.1 < n.succ := lt_of_le_of_ne h2 h,
      have H := h1 ⟨x.1, h3⟩, simp only [fin.eta] at H, exact H,
  },

  {
    intros x1 x2 hx, cases x1 with p1 x1, cases x2 with p2 x2,
    ext; simp only []; simp only [gn, id.def] at hx; rw function.funext_iff at hx, swap,
      generalize hm : (⟨n.succ, nat.lt_succ_self n.succ⟩ : fin n.succ.succ) = m,
      have hm' : m.val = n.succ, rw <-hm, replace hx := hx m, simp only [hm', dif_pos] at hx, assumption,
      
      generalize hm : (⟨x.1, nat.lt_trans x.2 (nat.lt_succ_self n.succ)⟩ : fin n.succ.succ) = m,
      replace hx := hx m, have hm' : m.1 ≠ n.succ,
        intro a, rw <-hm at a, simp only [] at a, have hx' := x.2, linarith,
      simp only [hm', dif_neg, not_false_iff] at hx, have hm2 := m.2, replace hm2 : m.1 ≤ n.succ, exact fin.le_last m,
      have hm3 : m.1 < n.succ, exact lt_of_le_of_ne hm2 hm',
      have H : x = ⟨m.1, hm3⟩, rw fin.ext_iff at hm ⊢, simp only [] at hm ⊢, exact hm,
      rw H, exact hx,
  },
end

def fn' {n : nat} : (int_n' n.succ.succ) -> (int_n n.succ) × ℤ :=                -- We modify the above injection slightly to be from (ℤ^{n+1} - {0}) to ℤⁿ × ℤ for n ≥ 1.
begin
  intro p, split, intro m,
  exact p.1 (⟨m.1, nat.lt_trans m.2 (nat.lt_succ_self n.succ)⟩ : fin n.succ.succ),
  exact p.1 (⟨n.succ, nat.lt_succ_self n.succ⟩ : fin n.succ.succ),
end

def gn' {n : nat} : (int_n n.succ) × ℤ -> (int_n' n.succ.succ) :=                -- We modify the above injection slightly to be from  ℤⁿ × ℤ to (ℤ^{n+1}  - {0})for n ≥ 1.
begin
  intro x,
  split, swap 2, intro m,
  by_cases (m.1 = n.succ), exact (strange_fun x.2).1,
    have H2 : m.1 < n.succ,  have H2' := fin.le_last m, exact lt_of_le_of_ne H2' h,
    exact (strange_fun (x.1 ⟨m.1, H2⟩)).1,

  intro rid, rw function.funext_iff at rid, simp only [pi.zero_apply] at rid,
  have ineq : n.succ < n.succ.succ, exact lt_add_one (nat.succ n),
  replace rid := rid ⟨n.succ, ineq⟩, split_ifs at rid,
  have contra := (strange_fun x.snd).property, simp only [ne.def] at contra, exact contra rid,

  simp only [eq_self_iff_true, not_true] at h, exact h,
end

lemma about_gt (m n : ℕ) (h : m < n) : m < n.succ := by exact nat.lt.step h

theorem gn'_inj {n : ℕ} : function.injective (@gn' n) :=
begin
    intros x y H, simp only [gn', subtype.mk_eq_mk, function.funext_iff] at H, ext m,
    have ineq : m.val < n.succ.succ,
    {
        exact nat.lt.step m.is_lt,
    },
    generalize hm' : @fin.cast_lt n.succ.succ n.succ m ineq = m',
    replace H := H m', split_ifs at H,
    have eq1 : m'.val = m.val,
    {
        rw <-hm', simp only [fin.cast_lt_val],
    }, rw eq1 at h, have rid := m.is_lt, linarith, rw <-subtype.ext_iff_val at H,
    have eq1 := strange_fun_inj H, have eq2 : m'.val = m.val, rw <-hm', simp only [fin.cast_lt_val],
    have eq3 : x.1 m = x.fst ⟨m'.val, _⟩,
    {
        apply congr_arg, rw fin.eq_iff_veq, simp only [], rw eq2,
    }, rw eq3, rw eq1, apply congr_arg, rw fin.eq_iff_veq, simp only [], rw eq2,
    
    have ineq2 : n.succ < n.succ.succ, exact lt_add_one (nat.succ n),
    replace H := H ⟨n.succ, ineq2⟩, split_ifs at H, rw <-subtype.ext_iff_val at H,
    exact strange_fun_inj H, rw <-subtype.ext_iff_val at H,
    simp only [eq_self_iff_true, not_true] at h, exfalso, exact h,
end


theorem aux_int_n' (n : nat) : 
  (int_n' n.succ.succ) ≃ (int_n n.succ) × ℤ :=                                    -- Again by the above injections and Schröder-Berstein
begin                                                                             -- we have (ℤ^{n+1} - {0}) ≃ ℤⁿ × ℤ for n ≥ 1
  suffices H1 : ∃ f : (int_n' n.succ.succ) -> (int_n n.succ) × ℤ, function.bijective f,
    choose h hh using H1,
    exact equiv.of_bijective h hh,

  suffices H2 : ∃ f : (int_n' n.succ.succ) -> (int_n n.succ) × ℤ, ∃ g : (int_n n.succ) × ℤ -> (int_n' n.succ.succ), function.injective f ∧ function.injective g,
    choose f g h using H2, exact function.embedding.schroeder_bernstein h.1 h.2,

  use fn', use gn', split,
  {
    intros x1 x2 hx, simp only [fn', id.def, prod.mk.inj_iff] at hx, cases hx with h1 h2, rw function.funext_iff at h1,
    apply subtype.eq, ext, rename x m,
    by_cases (m.val = n.succ),
      have H1 : m = (⟨n.succ, (nat.lt_succ_self n.succ)⟩ : fin n.succ.succ), 
      rw fin.ext_iff, simp only [], exact h,
      rw H1, assumption,

      have H2 : m.1 < n.succ,  have H2' := fin.le_last m, exact lt_of_le_of_ne H2' h,
      have h1m := h1 ⟨m.1, H2⟩, simp only [fin.eta] at h1m, exact h1m,
  },
  {
    exact gn'_inj,
  }
end

theorem int_n_equiv_int_n' (n : nat) : (int_n n.succ) ≃ int_n' n.succ :=          -- Use above and induction we are ready to prove
begin                                                                             -- ∀ n ∈ ℕ, n ≥ 1 → ℤⁿ ≃ (ℤⁿ - {0})
  induction n with n hn,
  exact int_1_equiv_int_1',

  suffices H1 : (int_n n.succ.succ) ≃ (int_n n.succ) × ℤ,
  suffices H2 : (int_n' n.succ.succ) ≃ (int_n' n.succ) × int',
    have e1 : (int_n n.succ) × ℤ ≃ (int_n' n.succ) × int', apply equiv.prod_congr,
      exact hn, exact int_eqiv_int',
    exact equiv.trans (equiv.trans H1 e1) H2.symm, swap, exact aux_int_n n,

    have e2 := aux_int_n' n, suffices H3 : (int_n nat.succ n) × ℤ ≃ (int_n' nat.succ n) × int', exact equiv.trans e2 H3,
    apply equiv.prod_congr, exact hn, exact int_eqiv_int',
end

/--
- For any n ∈ ℕ_{≥1}, `algebraic_set'_n` is the set of all the roots of non-zero polynomials of degree less than n.
- `algebraic_set'` is the set of all the roots of all the non-zero polynomials with integer coefficient.
- Both of the definition is of the flavour of the second evaluation methods.
- The `algebraic_set'_eq_algebraic_set` asserts `algebraic_set' = algebraic_set`. LHS is using the second evaluation method; RHS is using
  the first method.
-/

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
    simpa only [],
  },
end

theorem poly_n'_1_coeff_ne_0 (q : poly_n' 1) : q.1.coeff 0 ≠ 0 :=                 -- A non-zero polynomial of degree < 1 has a non-zero constant term
begin
  have h := q.2,
  cases h with h1 h2,
  have h : q.1 = polynomial.C (q.1.coeff 0), ext,
  by_cases (n = 0), rw h, simp only [polynomial.coeff_C_zero],
  rw polynomial.coeff_C, simp only [h, if_false], rw polynomial.coeff_eq_zero_of_nat_degree_lt,
  suffices H : 1 ≤ n, linarith, replace h : n ≠ 0 := h, rw <-nat.lt_one_add_iff, norm_num, exact zero_lt_iff_ne_zero.mpr h,
  rw h, simp only [polynomial.coeff_C_zero, ne.def], intro absurd, conv_rhs at h {rw absurd}, suffices H2 : polynomial.C (0 : int) = 0, conv_rhs at h {rw H2}, exact h1 h,
  ext, simp only [polynomial.C_0],
end

def identify'_1 : (poly_n' 1) -> int' := λ q, ⟨q.1.coeff 0, poly_n'_1_coeff_ne_0 q⟩ 
-- So we can identify the set of non-zero polynomial of degree < 1 with ℤ - {0}


theorem int_1_equiv_int : (int_n 1) ≃ ℤ :=                                        -- ℤ¹ ≃ ℤ
{ to_fun := (λ f, f ⟨0, by linarith⟩),
  inv_fun := (λ r m, r),
  left_inv := begin
    intro x, dsimp, ext m, fin_cases m,
  end,
  right_inv := λ x, rfl,}

/--
- denumerable means countably infinite
- countable means coutably infinite or countable
-/

theorem int_n_denumerable {n : nat} : denumerable (int_n n.succ) :=               -- for all n ∈ ℕ, n ≥ 1 → ℤⁿ is denumerable
begin
  induction n with n hn,                                                          -- To prove this, we use induction: ℤ¹ ≃ ℤ is denumerable
  apply denumerable.mk', suffices H : (int_n 1) ≃ ℤ, apply equiv.trans H, exact denumerable.eqv ℤ,
  exact int_1_equiv_int,

  apply denumerable.mk',                                                          -- Suppose ℤⁿ is denumerable, then ℤ^{n+1} ≃ ℤⁿ × ℤ ≃ ℕ × ℤ is denumerable
  have Hn := @denumerable.eqv (int_n n.succ) hn,                            
  have e1 := aux_int_n n, suffices H : (int_n n.succ) × ℤ ≃ ℕ, exact equiv.trans e1 H,
  have e2 : (int_n n.succ) × ℤ ≃ ℕ × ℤ, apply equiv.prod_congr, exact Hn, refl,
  suffices H : ℕ × ℤ ≃ nat, exact equiv.trans e2 H, exact denumerable.eqv (ℕ × ℤ),
end

theorem poly_n'_denumerable (n : nat) : denumerable (poly_n' n.succ) :=           -- So the set of non-zero polynomials of degree < n ≃ ℤⁿ - {0} ≃ ℤⁿ is denumerable
begin
  apply denumerable.mk',
  suffices e1 : (int_n' n.succ) ≃ ℕ, exact equiv.trans (poly_n'_equiv_int_n' n) e1,
  suffices e2 : (int_n n.succ) ≃ ℕ, exact equiv.trans (int_n_equiv_int_n' n).symm e2,
  exact @denumerable.eqv (int_n n.succ) int_n_denumerable,
end

theorem algebraic_set'_n_countable (n : nat) :                                    -- The set of roots of non-zero polynomial of degree < n is countable
  set.countable $ algebraic_set'_n n :=                                           -- being countable union of finite set.
    @set.countable_Union (poly_n' n.succ) ℝ (λ p, roots_real p.1) (poly_n'_denumerable n).1 
      (λ q, set.finite.countable (roots_finite q.1 q.2.1))


theorem algebraic_set'_countable : set.countable algebraic_set' :=                -- So the set of roots of non-zero polynomial is countable
  set.countable_Union (λ n, algebraic_set'_n_countable n.succ)                    -- being countable union of countable set

theorem algebraic_set_countable : set.countable algebraic_set :=                  -- So the set of algebraic number (no matter which evaluation method we are using)
begin                                                                             -- is countable
  rw <-algebraic_set'_eq_algebraic_set, exact algebraic_set'_countable
end

def real_set : set ℝ := @set.univ ℝ                                               -- the set ℝ
notation `transcendental` x := ¬(is_algebraic ℤ x)

theorem transcendental_number_exists : ∃ x : ℝ, transcendental x :=        -- Since ℝ is uncouble, algebraic numbers are countable
begin                                                                             
  have H : algebraic_set ≠ real_set,                                              -- ℝ ≠ algebraic_set
  {                                                                               -- otherwise ℝ must be countable which is not true
    intro h1,
    have h2 : set.countable real_set,
    {
      rw <-h1, exact algebraic_set_countable,
    },
    have h3 : ¬ set.countable real_set := cardinal.not_countable_real,
    exact h3 h2,
  },
  
  rw [ne.def, set.ext_iff, not_forall] at H,                                    -- Since algebraic_set ⊊ ℝ, there is some x ∈ ℝ but not algebraic
  choose x Hx using H, rw not_iff at Hx, replace Hx := Hx.mpr,
  use x, exact Hx trivial,
end
