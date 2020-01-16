import data.rat.basic
import data.polynomial
import tactic.linarith
import tactic.find
import data.rat.denumerable
import tactic.fin_cases

/-
example (n : nat) : ∀ m : nat, m < n -> (↑m : fin n).val = m :=
begin

end

example : ∀ r : rat, r.denom = 1 -> (r + 1).denom = 1 :=
begin
    intros r hr,
    generalize hn : r.num = n,
    rw rat.add_num_denom, simp [hr, hn], 

end

example : ∀ z : int, (rat.mk z 1).denom = 1 :=
begin
    intro z,
    
end

def rat_2 := {f : fin 2 -> rat // f ≠ 0}
def rat_2_set := {x : rat_2 | true}
def poly_deg1 := { x : polynomial rat // x.nat_degree <= 1 ∧ x ≠ 0}
def poly_deg1_set := {x : poly_deg1 | true}


def q_n : nat -> Type
| 0 := fin 1
| 1 := rat
| (n + 1) := prod (q_n n) rat

-- theorem rat_equiv_nat : rat ≃ nat :=
-- begin
-- letI to_fun : rat -> nat := (λ (q : rat), @encodable.encode rat _ q),
-- haveI h_to_fun : to_fun = (λ (q : rat), @encodable.encode rat _ q) := rfl,
-- letI inv_fun : nat -> rat := (λ (n : nat), @denumerable.of_nat rat _ n),
-- haveI h_inv_fun : inv_fun =  (λ (n : nat), @denumerable.of_nat rat _ n) := rfl,

-- have left_inv : function.left_inverse inv_fun to_fun,
-- {
--   rw function.left_inverse,

-- }

-- end

example: ∀ m n : nat, m < n -> m < n.succ :=
begin
library_search,
end

theorem rat_n_equiv_nat_n (n : nat) : (fin n -> rat) ≃ (fin n -> nat) :=
begin
induction n with n hn,
sorry,

-- let to_fun : (fin (nat.succ n) → ℚ) -> (fin (nat.succ n) → ℕ),
-- {
--     intro f_succ_n,
--     -- let f : fin n -> rat,
--     -- {
--     --     intro m,
--     --     exact f_succ_n ⟨m.1, @nat.lt.step m.1 n m.2⟩,
--     -- },
--     -- have g := equiv.to_fun hn f,
--     intro m,
--     have hm := m.2,
--     by_cases (m.val < n),
    
    
-- }
constructor,
end


theorem rat_n_denumerable (n : nat) : (fin n.succ -> rat) ≃ nat :=
begin
induction n with n hn,

constructor,
swap 3,
{
  intro q1,
  have zero : fin 1 := ⟨0, lt_add_one 0⟩,
  exact @encodable.encode rat _ (q1 zero),
},

swap 3,
{
  intro n,
  exact fun (m : fin 1), @denumerable.of_nat rat _ n,
},

{
    rw function.left_inverse,
    intro q,
    ext, rename x m,
    have g := @denumerable.of_nat_encode rat _ (q ⟨0, lt_add_one 0⟩),
    have g2 : m = ⟨0, lt_add_one 0⟩,
    {
        rw fin.ext_iff, simp,
        have h := m.2,
        exact  (@nat.le_zero_iff m.1).1 (nat.lt_succ_iff.mp m.2),
    },
    rw g2,
    exact g,
},

end


-- another version
-- theorem bij2 : ∀ (n : nat), (n ≠ 0) -> ∃ f : {x : poly_n n | true} -> {q : rat_n n | true}, function.bijective f :=
-- begin
-- intros n hn,
-- let f : {x : poly_n n | true} -> {q : rat_n n | true},
-- {
--   intro p,
--   exact ⟨identify n p.val, p.2⟩,
-- },
-- have hf : f = λ (p : ↥{x : poly_n n | true}), ⟨identify n (p.val), _⟩ := rfl,

-- use f,
-- split,
-- rw function.injective,
-- intros p1 p2 h,
-- rw hf at h,
-- simp at h,
-- have inj := inj_identify_n n hn,
-- have inj' := @inj p1.val p2.val h,
-- rw <-set_coe.ext_iff,
-- rw subtype.ext,
-- have h1 : ↑p1 = p1.val := rfl,
-- have h2 : ↑p2 = p2.val := rfl,
-- rw [h1, h2, inj'],

-- unfold function.surjective,
-- intro q,


-- end


example (n : nat) (Hn : n < 1) : n = 0 :=
begin
exact (@nat.le_zero_iff n).1 (nat.lt_succ_iff.mp Hn),
end


example (n : nat) : (fin n.succ -> nat) ≃ nat :=
begin
induction n with n hn,

constructor,
swap 3,
{
    intro m,
    exact m ⟨0, lt_add_one 0⟩,
},

swap 3,
{
    intro m,
    exact fun (n : fin 1), m,
},

{
    intro m,
    ext,
    have h : x = ⟨0, lt_add_one 0⟩,
    {
        rw fin.ext_iff,
        simp,
        exact (@nat.le_zero_iff x.1).1 (nat.lt_succ_iff.mp x.2),
    },
    rw h,
},

{
    intro m, simp,
},


have h : (fin n.succ.succ -> nat) ≃ prod (fin n.succ -> nat) nat,
{
    constructor,
    swap 3,
    {
        intro f_n_succ_succ,
        let f_n_succ : fin n.succ -> nat,
        {
            intro m,
            exact f_n_succ_succ m,
        },
        exact (f_n_succ, f_n_succ_succ n.succ),
    },
    swap 3,
    {
        intro p,
        have f_n_succ := p.1,
        have f_at_n_succ_succ := p.2,
        have f : fin n.succ.succ -> nat,
        {
            intro m,
            by_cases (m < n.succ),
            exact f_n_succ m,

            exact f_at_n_succ_succ,            
        },
        exact f,
    },

    {
        intro f_n_succ_succ,
        simp,
    }
}
end


-/