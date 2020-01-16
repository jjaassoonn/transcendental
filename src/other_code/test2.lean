import data.rat.basic
import data.rat.denumerable
import tactic.fin_cases

theorem rat_equiv_nat : rat ≃ nat :=
begin
exact @denumerable.eqv rat  _,
done
end

theorem rat_1_equiv_rat : (fin 1 -> rat) ≃ rat :=
begin
constructor,
swap 3,
{
    intro f,
    exact f 0,
},

swap 3,
{
    intros q m,
    exact q,
},

{
    intro f,
    ext,
    have hx : x = 0,
    {
        fin_cases x,
        rw fin.ext_iff,
        simp,
        exact rfl,
    },
    rw hx,
},

{
    intros q, simp,
},

done
end

theorem nat_2_equiv_nat : nat × nat ≃ nat :=
begin
exact denumerable.eqv (ℕ × ℕ),
end

theorem aux (n : nat) : (fin n.succ.succ -> rat) ≃ (fin n.succ -> rat) × rat :=
begin
constructor,
swap 3,
{
    intro f,
    exact (fun m : fin n.succ, f ⟨m.1, lt.trans m.2 (lt_add_one n.succ)⟩, f ⟨n.succ, lt_add_one n.succ⟩),
},

swap 3,
{
    intro x,
    have f := x.1,
    have q := x.2,
    intro m,
    by_cases (m.val < n.succ),
    exact f ⟨m.val, h⟩,
    exact q,
},

{
    intro f,
    ext,
    split_ifs,
    simp,
    
    have hx := x.2,
    replace h := (not_lt.mp h),
    have g : x.1 = n.succ,
    {
        cases (nat.lt_trichotomy x.1 n.succ),
        linarith,
        cases h_1,
        linarith,
        replace h_1 : x.val ≥ n.succ.succ := by exact h_1,
        linarith,
    },
    have g' : x = (⟨n.succ, lt_add_one n.succ⟩) := (fin.ext_iff x ⟨nat.succ n, lt_add_one (nat.succ n)⟩).mpr g,
    rw g',
},

{
    intro x,
    ext;
    simp,

    rename x_1 m,
    split_ifs,
    refl,
    have h' := m.2,
    replace h : ¬m.val < n.succ := by exact h,
    linarith,
},

done,
end

theorem rat_n_equiv_nat (n : nat) : (fin n.succ -> rat) ≃ nat :=
begin
induction n with n Hn,
exact equiv.trans rat_1_equiv_rat rat_equiv_nat,
have h1 := aux n,
have h2 : (fin n.succ -> rat) × rat ≃ nat × nat,
{
    exact equiv.prod_congr Hn rat_equiv_nat,
},
have h3 : nat × nat ≃ nat := nat_2_equiv_nat,
exact equiv.trans (equiv.trans h1 h2) h3,
end

theorem rat_n_denumerable (n : nat) : denumerable (fin n.succ -> rat) :=
begin
exact denumerable.mk' (rat_n_equiv_nat n),
done
end

