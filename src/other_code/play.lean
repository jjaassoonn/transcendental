import data.rat.basic
import data.rat.denumerable
import data.polynomial
import tactic.ext
import tactic.linarith
import tactic.norm_cast
import tactic.norm_num
import data.nat.cast
import data.set.countable
import tactic.fin_cases

noncomputable theory

def rat_n (n : nat) := fin n -> rat
def nat_n (n : nat) := fin n -> nat
def poly_n (n : nat) := {x : polynomial rat // x.nat_degree < n}

def identify (n : nat) : (poly_n n) -> (rat_n n) :=
begin
intro p,
intro m,
exact p.val.coeff m.val,
done
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

theorem sur_identify_n : ∀ n : nat, (n ≠ 0) -> function.surjective (identify n) :=
begin
intros n hn,
unfold function.surjective,
intro q,
let support : finset nat := finset.filter (λ m : nat, (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n),
have hsupport : support = finset.filter (λ m : nat, (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) (finset.range n) := rfl,
-- {
--   let range_n := finset.range n,
--   let range_n_qn_not_zero := finset.filter (λ m : nat, (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) ≠ 0) range_n,
--   exact range_n_qn_not_zero,
-- },

let to_fun : nat -> rat := (λ m : nat, ite (m ∈ support) (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) 0),
-- let to_fun : nat -> rat := (λ m : nat, ite (m ∈ support) (q (@nat.cast (fin n) _ _ _ m )) 0),
have hto_fun : to_fun = (λ m : nat, ite (m ∈ support) (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) 0) := rfl,
-- -- {
-- --   intro m,
-- --   exact ite (m ∈ support) (q (⟨m % n, m_mod_n_lt_n n hn m⟩ : fin n)) 0,
-- -- },

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

theorem bij1 : ∀ (n : nat), (n ≠ 0) -> ∃ f : (poly_n n) -> (rat_n n), function.bijective f :=
begin
intros n hn,
use identify n,
split,

-- injective (canno)
exact inj_identify_n n hn,

-- surjective
exact sur_identify_n n hn,

end

theorem poly_n_equiv_rat_n (n : nat) : (poly_n n.succ) ≃ (rat_n n.succ) :=
begin
let f := identify n.succ,
have f_bij : function.bijective f := ⟨inj_identify_n n.succ (nat.succ_ne_zero n), sur_identify_n n.succ (nat.succ_ne_zero n)⟩,
exact equiv.of_bijective f_bij,
done
end



-- theorem rat_n_infinite (n : nat) (Hn : n >= 1) : infinite (fin n -> rat) :=
-- begin
--   let f : rat -> (fin n -> rat),
--   {
--     intros q m,
--     exact q,
--   },
--   have h_f : f = λ (q : ℚ) (m : fin n), q := rfl,
--   have h_f_inj : function.injective f,
--   {
--     rw function.injective,
--     intros q1 q2 h_q1_q2,
--     rw h_f at h_q1_q2,
--     simp at h_q1_q2,
--     have zero : fin n := ⟨0, Hn⟩,
--     have h1 : q1 = (λ (m : fin n), q1) zero := rfl,
--     have h2 : q2 = (λ (m : fin n), q2) zero := rfl,
--     rw h_q1_q2 at h1,
--     rw <-h2 at h1,
--     exact h1,
--   },

--   exact infinite.of_injective f h_f_inj,
-- end

-- theorem nat_n_encodable (n : nat) : encodable (fin n -> nat) :=
-- begin
-- induction n with n hn,

-- sorry,
-- sorry,
-- end

-- theorem rat_n_denumerable (n : nat) (Hn : n >= 1) : denumerable (fin n -> rat) :=
-- begin
-- have h1 : infinite (fin n -> rat) := rat_n_infinite n Hn,
-- have h2 : encodable (fin n -> rat) := sorry,
-- exact @denumerable.of_encodable_of_infinite (fin n -> rat) h2 h1,

-- end


-- theorem rat_n_equiv_nat_n : ∀(n : nat), (rat_n n) ≃ (nat_n n) :=
-- begin
-- intro n,
-- /-
-- structure equiv (α : Sort*) (β : Sort*) :=
-- (to_fun    : α → β)
-- (inv_fun   : β → α)
-- (left_inv  : left_inverse inv_fun to_fun)
-- (right_inv : right_inverse inv_fun to_fun)
-- -/

-- let to_fun : (rat_n n) -> (nat_n n) := (λ (q_n : rat_n n), (λ (m : fin n), @encodable.encode rat _ (q_n m))),
-- let inv_fun : (nat_n n) -> (rat_n n) := (λ (a_n : nat_n n), (λ (m : fin n), @denumerable.of_nat rat _ (a_n m))),

-- -- let to_fun : (rat_n n) -> (nat_n n),
-- -- {
-- --   intros q_n m,
-- --   have q := q_n m,
-- --   have g' := denumerable.of_nat,
-- --   have g := rat.encodable.1,
-- --   have a := g q,
-- --   exact a,
-- -- },
-- have h_to_fun : to_fun = λ (q_n : rat_n n), (λ (m : fin n), encodable.encode (q_n m)) := rfl,


-- -- let inv_fun : (nat_n n) -> (rat_n n),
-- -- {
-- --   intros a_n m,
-- --   have a := a_n m,
-- --   have g := @denumerable.of_nat rat _ a,
-- --   /-
-- --   have q := g a,
-- --   by_cases (q = none),

-- --   exact 0,

  
-- --   have g' : q ≠ none := by exact h,
-- --   have g := (@option.ne_none_iff_is_some rat q).1 g',
-- --   exact option.get g,
-- --   -/
-- --   exact g,
-- -- },
-- have h_inv_fun : inv_fun = λ (a_n : nat_n n), (λ (m : fin n), denumerable.of_nat ℚ (a_n m)) := rfl,

-- let left_inv : function.left_inverse inv_fun to_fun,
-- {
--   rw function.left_inverse,
--   intro q_n,
--   rw h_inv_fun,
--   have h : (λ (a_n : nat_n n) (m : fin n), denumerable.of_nat ℚ (a_n m)) (to_fun q_n) = (λ (m : fin n), denumerable.of_nat ℚ (to_fun q_n m)) := rfl,
--   rw h,
--   rw h_to_fun,
--   have h : (λ (m : fin n), denumerable.of_nat ℚ ((λ (q_n : rat_n n) (m : fin n), encodable.encode (q_n m)) q_n m)) = (λ (m : fin n), @denumerable.of_nat rat _ (encodable.encode (q_n m))) := rfl,
--   rw h,
--   ext,
--   rename x m,
--   have h := @denumerable.of_nat_encode rat _ (q_n m),
--   exact h,
-- }


-- end