import data.set.basic
import data.set.countable
import test2

noncomputable theory

def set_nat := @set.univ nat

theorem denumerable_countable (α : Type) (Hα : denumerable α) : set.countable (@set.univ α) :=
begin
rw set.countable_iff_exists_injective,
use (fun m, encodable.encode m.1),
intros x1 x2 h,
simp at h,
have g := @congr_arg nat α (encodable.encode x1.1) (encodable.encode x2.1) (denumerable.of_nat α) h,
rw [denumerable.of_nat_encode, denumerable.of_nat_encode] at g,
exact subtype.eq g,
done
end

theorem nat_countable : set.countable set_nat :=
begin
rw set.countable_iff_exists_injective,
use fun n, n.1,
intros n1 n2 h,
simp at h,
exact subtype.eq' h,
done
end

theorem countable_equiv_countable {α β : Type} (A : set α) (B : set β) (H1 : A ≃ B) (HA : A.countable) : B.countable :=
begin
have HA' := (@set.countable_iff_exists_injective α A).mp HA,
cases HA' with g hg,
let f := g ∘ H1.2,
have hf : f = g ∘ H1.2 := rfl,
rw set.countable_iff_exists_injective,
use f,
intros n1 n2 h,
rw hf at h,
simp at h,
replace h := @hg (H1.2 n1) (H1.2 n2) h,
replace h : H1.1 (H1.2 n1) = H1.1 (H1.2 n2) := congr_arg (H1.to_fun) h,
rw [(H1.4 n1), (H1.4 n2)] at h,
exact h,
done
end

def set_rat := @set.univ rat

theorem rat_countable : set.countable set_rat := 
begin
have h := countable_equiv_countable set_nat set_rat,
have h2 : set_rat ≃ set_nat,
{
    constructor,
    swap 3,
    have g := rat_equiv_nat.1,
    intro q, exact ⟨g q.1, trivial⟩,
    swap 3,
    have g := rat_equiv_nat.2,
    intro n, exact ⟨g n.1, trivial⟩,
    intro q,
    simp,
    rw rat_equiv_nat.3 q.val,
    simp,

    simp,
    intro n, simp,
    rw rat_equiv_nat.4 n.val, simp,
},
exact h h2.symm nat_countable,
done
end

def set_rat_n (n : nat) := @set.univ (fin n.succ -> rat)
theorem countable_rat_n (n : nat) : set.countable (set_rat_n n) := denumerable_countable (fin n.succ -> rat) (rat_n_denumerable n)



theorem bij_equiv (α β : Type) (f : α -> β) (hf : function.bijective f) : α ≃ β :=
begin
have h := (@function.bijective_iff_has_inverse _ _ f).mp hf,
choose g hg using h,

constructor,
swap 3,
exact f,

swap 3,
exact g,

exact hg.1,

exact hg.2,
done
end

