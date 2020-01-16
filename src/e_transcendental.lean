import data.real.basic
import data.complex.exponential
import ring_theory.algebraic

noncomputable theory

def e : real := real.exp 1

theorem e_transcendental : ¬ is_algebraic rat e :=
begin
  sorry
end