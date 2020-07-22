import ring_theory.algebraic
import data.real.cardinality
import small_things
import tactic

noncomputable theory
open_locale classical

notation α`[X]` := polynomial α

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

def roots_real (p : ℤ[X]) : set ℝ := {x | polynomial.aeval ℤ ℝ x p = 0}

def poly_int_to_poly_real (p : ℤ[X]) : polynomial ℝ := polynomial.map ℤembℝ p

def poly_int_to_poly_real_wd (p : ℤ[X]) := ∀ x : real, polynomial.aeval ℤ ℝ x p = (poly_int_to_poly_real p).eval x

theorem poly_int_to_poly_real_preserve_deg (p : ℤ[X]) : p.degree = (poly_int_to_poly_real p).degree :=
begin
  rw [poly_int_to_poly_real],
  apply eq.symm, apply polynomial.degree_map_eq_of_injective,
  intros x y H, simp only [ring_hom.eq_int_cast, int.cast_inj] at H, exact H,
end

theorem poly_int_to_poly_real_C_wd' (a : int) : polynomial.C (a:ℝ) = poly_int_to_poly_real (polynomial.C a) := 
begin
  simp only [poly_int_to_poly_real], rw polynomial.map_C, ext, simp only [ring_hom.eq_int_cast],
end

theorem poly_int_to_poly_real_C_wd : ∀ a : ℤ, poly_int_to_poly_real_wd (polynomial.C a) := λ _ _, by simp only [poly_int_to_poly_real, polynomial.aeval_def, polynomial.eval_map, ℤembℝ]

theorem poly_int_to_poly_real_add (p1 p2 : polynomial ℤ) : poly_int_to_poly_real (p1 + p2) = poly_int_to_poly_real p1 + poly_int_to_poly_real p2 :=
begin
  simp only [poly_int_to_poly_real, polynomial.map_add],
end

theorem poly_int_to_poly_real_add_wd (p1 p2 : ℤ[X]) 
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
  simp only [polynomial.eval_X, polynomial.map_X, polynomial.eval₂_X, ℤembℝ],
end


theorem poly_int_to_poly_real_ne_zero (p : ℤ[X]) : p ≠ 0 ↔ (poly_int_to_poly_real p) ≠ 0 :=
begin
suffices : p = 0 ↔ (poly_int_to_poly_real p) = 0, exact not_congr this,
split, 
  intros h, rw h, ext, simp only [poly_int_to_poly_real, polynomial.map_zero],

  simp only [poly_int_to_poly_real], intro hp,
  ext, rw polynomial.ext_iff at hp,
  replace hp := hp n, simp only [polynomial.coeff_zero, polynomial.coeff_map] at hp ⊢,
  rw <-ℤembℝ_zero at hp,
  exact ℤembℝ_inj hp,
end

theorem poly_int_to_poly_real_well_defined (x : real) (p : polynomial ℤ) :
    poly_int_to_poly_real_wd p :=
begin
  apply polynomial.induction_on p,
  exact poly_int_to_poly_real_C_wd,
  exact poly_int_to_poly_real_add_wd,
  exact poly_int_to_poly_real_pow_wd,
end

def roots_real' (p : ℤ[X]) : set ℝ := {x | (poly_int_to_poly_real p).eval x = 0}

theorem roots_real_eq_roots (p : ℤ[X]) (hp : p ≠ 0) : roots_real p = ↑(poly_int_to_poly_real p).roots :=
begin
  simp only [roots_real], ext, split,
  intros hx, simp only [set.mem_set_of_eq] at hx,
  simp only [finset.mem_coe], 
  rw [polynomial.mem_roots, polynomial.is_root.def, <-(poly_int_to_poly_real_well_defined x)],
  exact hx,
  rw <-poly_int_to_poly_real_ne_zero, exact hp,

  intro hx, simp only [finset.mem_coe] at hx,
  rw [polynomial.mem_roots, polynomial.is_root.def, <-(poly_int_to_poly_real_well_defined x)] at hx,
  simp only [set.mem_set_of_eq], exact hx,
  rw <-poly_int_to_poly_real_ne_zero, exact hp,
end

theorem roots_finite (p : polynomial ℤ) (hp : p ≠ 0) : set.finite (roots_real p) :=
begin
  rw (roots_real_eq_roots p hp), exact (poly_int_to_poly_real p).roots.finite_to_set,
end

/- 
We allow the zero polynomial to have degree zero.
Otherwise we need to use type `with_bot ℕ` so that the zero polynomial has degree negative infinity
-/

notation `int_n` n := fin n -> ℤ                                                  -- the set of ℤⁿ
notation `nat_n` n := fin n -> ℕ                                                  -- the set of ℕⁿ
notation `poly_n'` n := {p : ℤ[X] // p ≠ 0 ∧ p.nat_degree < n}            -- the set of all nonzero polynomials in $ℤ[T]$ with degree < n
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

theorem strange_fun_sur : function.surjective strange_fun :=
begin
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
simp only [strange_fun, h, sub_lt_zero, sub_add_cancel, subtype.eta, if_false, sub_lt_zero, dif_neg, not_false_iff],  
end

theorem int_eqiv_int' : ℤ ≃ int' :=                                               -- So ℤ ≃ ℤ - {0} because the strange function is a bijection
begin
  apply equiv.of_bijective strange_fun,
  split,
  exact strange_fun_inj,                                                      -- The injection part is proved above
  exact strange_fun_sur

end

-- def zero_int_n {n : nat} : int_n n.succ := (fun m, 0)                             -- ℤ⁰ = {0}
-- def zero_poly_n {n : nat} : poly_n n.succ := ⟨0, nat.succ_pos n⟩                  -- no polynomial in $ℤ[T]$ with degree < 0

def identify (n : nat) : (poly_n' n) -> (int_n' n) := λ p, 
⟨λ m, p.1.coeff m.1, λ rid, begin
  rw function.funext_iff at rid,
  simp only [pi.zero_apply, subtype.val_eq_coe] at rid,
  have contra : p.1 = 0,
    ext m, simp only [polynomial.coeff_zero, subtype.val_eq_coe],
    by_cases (m < n),
    replace rid := rid ⟨m, h⟩, simp only [] at rid, exact rid,

    simp only [not_lt] at h,
    rw polynomial.coeff_eq_zero_of_nat_degree_lt,
    have deg := p.2.2, simp only [subtype.val_eq_coe] at deg, linarith,
  exact p.2.1 contra,
end⟩

lemma m_mod_n_lt_n : ∀ n : nat, n ≠ 0 -> ∀ m : nat, m % n < n := 
  λ n hn m, @nat.mod_lt m n (zero_lt_iff_ne_zero.mpr hn)        


theorem sur_identify_n (n : nat) (hn : n ≠ 0) : function.surjective (identify n) :=
begin                                                                                                         
    intro q,
    -- we can define a polynomial whose non-zero coefficients are exact at non-zero elements of q;                                                                                                                     -- given an element q in ℤⁿ
    set p : polynomial ℤ := { support := finset.filter (λ m : nat, (q.1 (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n), 
      to_fun := (λ m : nat, ite (m ∈ (finset.filter (λ m : nat, (q.1 (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n))) (q.1 (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) 0),
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
        have g : ite (m ∈ (finset.filter (λ m : nat, (q.1 (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n))) (q.1 ⟨m % n, m_mod_n_lt_n n hn m⟩) 0 ≠ 0 -> (m ∈ (finset.filter (λ m : nat, (q.1 (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n))),
        {
          intro h,
          by_contra,
          split_ifs at h,
          have h' : (0 : ℤ) = 0 := rfl,
          exact h h',
        },
        exact g hm,
      end} with hp,
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
    have p_nonzero : p ≠ 0,
    {
      intro rid, rw polynomial.ext_iff at rid,
      have hq := q.2,
      replace hq : ∃ x, q.1 x ≠ 0, rw <-not_forall, intro rid, replace rid : q.1 = 0, ext m, exact rid m, exact hq rid,
      choose x hx using hq,
      rw hp at rid, simp only [not_and, ne.def, polynomial.coeff_zero, finset.mem_filter, finset.mem_range, finset.filter_congr_decidable,
 polynomial.coeff_mk, classical.not_not] at rid,
 replace rid := rid x.1, split_ifs at rid, exact h.2 rid,

      simp only [not_and, classical.not_not] at h,
      replace h := h _,
      have triv : x = ⟨x.val % n, _⟩, rw fin.eq_iff_veq, simp only [],
      rw nat.mod_eq_of_lt, exact x.2, rw <-triv at h, exact hx h, exact x.2,
    },
    use ⟨p, ⟨p_nonzero, hp_nat_deg⟩⟩,                                                          -- We claim that this polynomial is identified with q
    {
      ext m,
      simp only [identify, polynomial.coeff_mk, not_and, ne.def, finset.mem_filter, finset.mem_range,
 classical.not_not], simp only [not_and, ne.def, finset.mem_filter, finset.mem_range, subtype.coe_mk, polynomial.coeff_mk, classical.not_not,
 subtype.val_eq_coe],
      split_ifs,
      apply congr_arg,
      ext, simp only [], rw nat.mod_eq_of_lt, exact h.1,
      simp only [not_and, classical.not_not] at h,
      replace h := h m.2, rw <-h, apply congr_arg,
      ext, simp only [], rw nat.mod_eq_of_lt, exact m.2,
    },
end

theorem inj_identify_n (n : nat) (hn : n ≠ 0) : function.injective (identify n) := λ x1 x2 hx,
begin
    simp only [subtype.mk_eq_mk, identify, function.funext_iff, subtype.coe_mk, subtype.val_eq_coe] at hx, apply subtype.eq,
    ext m,
    have h1 := x1.2.2, have h2 := x2.2.2,
    by_cases (m ≥ n),
    rw [polynomial.coeff_eq_zero_of_nat_degree_lt, polynomial.coeff_eq_zero_of_nat_degree_lt],
    exact lt_of_lt_of_le h2 h, exact lt_of_lt_of_le h1 h, 
    
    replace h : m < n, exact not_le.mp h,
    exact hx ⟨m, h⟩,
end

theorem poly_n'_equiv_int_n' (n : nat) : (poly_n' n.succ) ≃ (int_n' n.succ) :=    -- We use the fact that identification is bijection to prove
begin                                                                             -- that non-zero polynomial of degree < n is equipotent to ℤⁿ for n ≥ 1
  apply equiv.of_bijective (identify n.succ),
  split,
  exact inj_identify_n n.succ (nat.succ_ne_zero n),
  exact sur_identify_n n.succ (nat.succ_ne_zero n),
end

def F (n : nat) : (int_n n.succ) -> (int_n' n.succ) := λ f,
⟨λ m, (strange_fun (f m)).1, λ rid, begin
  rw function.funext_iff at rid,
  replace rid := rid 0,
  simp only [pi.zero_apply] at rid,
  exact (strange_fun (f 0)).2 rid,
end⟩

theorem F_inj (n : nat) : function.injective (F n) := λ f1 f2 Hf,
begin
  simp only [F] at Hf, rw function.funext_iff at Hf ⊢,
  intro m,
  replace Hf := Hf m, rw <-subtype.ext_iff_val at Hf,
  exact strange_fun_inj Hf,
end

def G (n : nat) : (int_n' n.succ) -> (int_n n.succ) := λ f m, (f.1 m)

theorem G_inj (n : nat) : function.injective (G n) := λ f1 f2 Hf,
begin
  simp only [G] at Hf, rw function.funext_iff at Hf, ext m,
  exact Hf m,
end

theorem int_n_equiv_int_n' (n : nat) : (int_n n.succ) ≃ int_n' n.succ :=
begin
  choose B HB using function.embedding.schroeder_bernstein (F_inj n) (G_inj n),
  apply equiv.of_bijective B HB,
end

def fn (n : nat) : (int_n n.succ.succ) -> (int_n n.succ) × ℤ := λ r,                  -- This is an injection from ℤ^{n+1} to ℤⁿ × ℤ for n ≥ 1
⟨λ m, r (⟨m.1, nat.lt_trans m.2 (nat.lt_succ_self n.succ)⟩), r (⟨n.succ, nat.lt_succ_self n.succ⟩)⟩

theorem fn_inj (n : ℕ) : function.injective (fn n) := λ x1 x2 hx,
begin
    simp only [fn, id.def, prod.mk.inj_iff] at hx, cases hx with h1 h2, rw function.funext_iff at h1, ext,
    by_cases (x = ⟨n.succ, nat.lt_succ_self n.succ⟩), rw <-h at h2, assumption,
      simp only [fin.eq_iff_veq] at h, have h2 := x.2, replace h2 : x.1 ≤ n.succ := fin.le_last x,
      have h3 : x.1 < n.succ := lt_of_le_of_ne h2 h,
      have H := h1 ⟨x.1, h3⟩, simp only [fin.eta] at H, exact H,
end

def gn (n : nat) : (int_n n.succ) × ℤ -> (int_n n.succ.succ) := λ r m,                 -- This is an injection from ℤⁿ × ℤ to ℤ^{n+1} for n ≥ 1
begin
  by_cases (m.1 = n.succ),
    exact r.2,
    exact r.1 (⟨m.1, lt_of_le_of_ne (fin.le_last m) h⟩),
end

theorem gn_inj (n : nat) : function.injective (gn n) := λ x1 x2 hx,
begin
cases x1 with p1 x1, cases x2 with p2 x2,
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
end

theorem aux_int_n (n : nat) :                                                     -- So again using the two injections and Schröder-Berstein
  (int_n n.succ.succ) ≃ (int_n n.succ) × ℤ :=                       -- We know ℤⁿ × ℤ ≃ ℤ^{n+1} for n ≥ 1
begin
choose B HB using function.embedding.schroeder_bernstein (fn_inj n) (gn_inj n),
apply equiv.of_bijective B HB,
end

/--
- For any n ∈ ℕ_{≥1}, `algebraic_set'_n` is the set of all the roots of non-zero polynomials of degree less than n.
- `algebraic_set'` is the set of all the roots of all the non-zero polynomials with integer coefficient.
- Both of the definition is of the flavour of the second evaluation methods.
- The `algebraic_set'_eq_algebraic_set` asserts `algebraic_set' = algebraic_set`. LHS is using the second evaluation method; RHS is using
  the first method.
-/

def algebraic_set'_n (n : ℕ) : set ℝ := ⋃ p : (poly_n' n.succ), roots_real p.1
def algebraic_set' : set real := ⋃ n : ℕ, algebraic_set'_n n.succ

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
- countable means countably infinite or finite
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
  set.countable (algebraic_set'_n n) :=                                           -- being countable union of finite set.
    @set.countable_Union (poly_n' n.succ) ℝ (λ p, roots_real p.1) (poly_n'_denumerable n).1 
      (λ q, set.finite.countable (roots_finite q.1 q.2.1))


theorem algebraic_set'_countable : set.countable algebraic_set' :=                -- So the set of roots of non-zero polynomial is countable
  set.countable_Union (λ n, algebraic_set'_n_countable n.succ)                    -- being countable union of countable set

theorem algebraic_set_countable : set.countable algebraic_set :=                  -- So the set of algebraic numb
-- (no matter which evaluation method we are using)
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
