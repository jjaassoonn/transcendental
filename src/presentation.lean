import algebraic_countable_over_Z
import liouville_theorem
import e_transcendental




------------------------------------------------------------------------------------




/-# Formalisations of basic theorems of trascendental number theory
The main result in this project is the following:
- Countability of algebraic numbers;
- Liouville's theorem and Liouville's number;
- Transcendence of e^n for n ≥ 1;                                                 -/






------------------------------------------------------------------------------------





/-## The set of algebraic number is countable                                     -/

-- #print algebraic_set
-- #print algebraic_set_countable
-- #print transcendental_number_exists






------------------------------------------------------------------------------------

/- ## Liouville's theorem and Liouville's number                                  -/

-- #print liouville_number
-- #print liouville_numbers_transcendental

/- α is a Liouville's number hence it is transcendental                           -/

-- #print ten_pow_n_fact_inverse
-- #print α
-- #print liouville_α
-- #print transcendental_α


------------------------------------------------------------------------------------





/- ## e^n is transcendental for all n ≥ 1                                         -/

-- #print e
-- #print e_pow_transcendental







------------------------------------------------------------------------------------




/-# Basic dependent type theory 

- 0        : ℕ
- ℕ        : Type
- Type     : Type 1
- n |-> n! : ℕ -> ℕ
- (0, 1)   : ℕ × ℕ                                                                -/





------------------------------------------------------------------------------------

/- Let `𝓤` be a collection of types and `A` be a type, 
   for a family of types `B : A -> 𝓤`, 

- we can form a new Π-type:
          Π (x : A), B x.
  The terms of this type has the form `f : Π (x : A), B x` such that for any term `a` of type `A`, `f a` is of type `B a`. This is generalised function, if `B` is a constant family of types then this is just `A -> B`.

- we can form a new Σ-type:
          Σ (x : A), B x.
  The terms of this type has the form `⟨x, h⟩` where `x` has type `A` and `h` has type `B x`. This is generlised cartisean product, if `B` is a constant family of types then this is just `A × B`.                                                -/

------------------------------------------------------------------------------------






/-## Curry-Howard isomorphism : 
     propositions are types whose terms are proofs.                               -/








------------------------------------------------------------------------------------

/-### p -> q -/
theorem modus_ponens (p q : Prop) 
  (proof_of_p_imp_q : p -> q) (proof_of_p : p) : q := proof_of_p_imp_q proof_of_p

/-### p ∧ q -/
theorem proving_and (p q : Prop) (proof_of_p : p) (proof_of_q : q) : p ∧ q := 
  ⟨proof_of_p, proof_of_q⟩

/-### p ∨ q -/
theorem proving_or (p q : Prop) (proof_of_p : p) : p ∨ q := or.intro_left q proof_of_p

/-### ⊥ ; ¬p -/
theorem not_example : ¬(0 = 1) := λ p, by linarith

------------------------------------------------------------------------------------




/-# B : A -> Prop -/

/- `Π (a : A), B a` and `∀ a : A, B a` -/

/- `Σ (a : A), B a` and `∃ a : A, B a` -/








------------------------------------------------------------------------------------

/-Now let us have a taste of how proving a theorem feels like using `Lean`. -/
  
noncomputable theory
open_locale classical 

def mean (x y : ℝ) : ℝ := (x + y) / 2
  
theorem min_le_mean : ∀ x y : ℝ, min x y ≤ (mean x y) :=
begin
intros x y,
have ineq1 : min x y ≤ x := min_le_left x y,
have ineq2 : min x y ≤ y := min_le_right x y,
    
unfold mean, rw le_div_iff (show (0 < (2:ℝ)), by linarith),
rw mul_two, 
apply add_le_add, 
exact ineq1, exact ineq2,
end
  
theorem mean_le_max : ∀ x y : ℝ, (mean x y) ≤ max x y :=
begin
intros x y,
have ineq1 : x ≤ max x y := le_max_left x y,
have ineq2 : y ≤ max x y := le_max_right x y,
  
unfold mean, rw div_le_iff (show (0 < (2:ℝ)), by linarith),
rw mul_two,
apply add_le_add,
exact ineq1, exact ineq2,
end
  
theorem a_number_in_between : 
  ∀ x y : ℝ, x ≤ y -> ∃ z : ℝ, x ≤ z ∧ z ≤ y :=
begin
intros x y hxy,
have ineq1 := min_le_mean x y,
have ineq2 := mean_le_max x y,
have min_eq_x := min_eq_left hxy,
have max_eq_y := max_eq_right hxy,
use mean x y,
split,
  
{ conv_lhs {rw <-min_eq_x}, exact ineq1, },
{ conv_rhs {rw <-max_eq_y}, exact ineq2, },
end


-----------------------------------------------------------------------------------





/- # Conlusion
 - what is the long term goal?
 - what is the value of such approach in terms of pedagogy? 
 - what is the value of such approach in terms of researching?
    * Univalent axiom : (A = B) ≃ (A ≃ B)                                         -/




------------------------------------------------------------------------------------