import data.real.basic
import data.polynomial
import data.mv_polynomial
import ring_theory.algebra
import ring_theory.algebraic
import play

noncomputable theory

def set1 : set real := {x | ∃ p : polynomial rat, p ≠ 0 ∧ polynomial.aeval rat real x p = 0 }
def set2 : set real := {x | ∃ n : nat, ∃ p : poly_n n.succ, p.1 ≠ 0 ∧ polynomial.aeval rat real x p.1 = 0}


theorem aaa : set1 = set2 :=
begin
ext,

split,
{
    intro hx,
    cases hx with p hp,
    cases hp with hp_ne0 hpx_0,
    constructor, swap, exact p.nat_degree,
    use p,
    exact lt_add_one (polynomial.nat_degree p),
    simp,
    exact  ⟨hp_ne0 , hpx_0⟩,
},

{
    intro hx,
    cases hx with deg hp,
    cases hp with p hp,
    cases hp with hp1 hp2,

    constructor, swap,
    exact p.1,
    exact ⟨hp1, hp2⟩,
},
done
end

