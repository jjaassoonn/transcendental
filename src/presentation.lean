import algebraic_countable_over_Z
import liouville_theorem
import e_transcendental

/-
# Formalisations of basic theoreoms of trascendental number theory

The main result in this project is the following:
- The set of all algebraic number is countable, hence a transcendental number exists;
-/

-- #print algebraic_set
-- #print algebraic_set_countable
-- #print transcendental_number_exists

/-
- All Liouville numbers are transcendental;
-/

-- #print liouville_number
-- #print liouville_numbers_transcendental

/-
- α is a Liouville's number hence it is transcendental
-/

-- #print ten_pow_n_fact_inverse
-- #print α
-- #print liouville_α
-- #print transcendental_α

/-
- e^n is transcendental for all n ≥ 1.
-/

-- #print e
-- #print e_pow_transcendental

/-
As we can see, the proofs are quite unfathomable. But actually they are not that bad.

This is because, we use _tactic mode_. 
But before we talk about _tactics_, let us discuss how computers can understand proofs.

The answer is _dependent type theory_ as an alternative fundation of mathematics.

The ontology of _dependent type theory_ is that every term has a type:

- 0        : ℕ
- ℕ        : Type
- Type     : Type 1
- n |-> n! : ℕ -> ℕ
- (0, 1)   : ℕ × ℕ

(yes, even Type has a type `Type 1`.)

What makes dependent type theory expressive is the dependent types: let `𝓤` be a collection of types and `A` be a type, for a family of types `B : A -> 𝓤`, 

- we can form a new Π-type:
          Π (x : A), B x.
  The terms of this type has the form `f : Π (x : A), B x` such that for any term `a` of type `A`, f a is of type `B a`. This is generalised function, if `B` is a constant family of types then this is just `A -> B`.

- we can form a new Σ-type:
          Σ (x : A), B x.
  The terms of this type has the form `⟨x, h⟩` where `x` has type `A` and `h` has type `B x`. This is generlised cartisean product, if `B` is a constant family of types then this is just `A × B`

The magic is _Curry-Howard isomorphism_. Loosely meaning: propositions are types whose terms are proofs. 

Let me illustruate:

- The proposition `p -> q` under this interpretation is literally just a function which given any input term of type `p` returns a term of type `q`; equivalently given a proof of `p` returns a proof `q`. Then modus ponens is really a function application.
-/

-- theorem modus_ponens (p q : Prop) 
--   (proof_of_p_imp_q : p -> q) (proof_of_p : p) : q := proof_of_p_imp_q proof_of_p

/-
- The proposition `p ∧ q` is really `p × q`. So a term of `p ∧ q` is a pair `(h₁, h₂)` with `h₁ : p` and `h₂ : q`; using the above interpretation --- a proof of `p ∧ q` is a pair of proofs of `p` and `q` respectively.
-/

-- theorem proving_and (p q : Prop) (proof_of_p : p) (proof_of_q : q) : p ∧ q := 
--   ⟨proof_of_p, proof_of_q⟩

/-
- Similarly `p ∨ q` can be regarded as a coproduct type (disjoint union). So a term of `p ∨ q` can be constructed from a term of `p` or a term of `q`; using the above interpretation --- to prove `p ∨ q`, it suffices to prove `p` or to prove `q`.
-/
-- theorem proving_or (p q : Prop) (proof_of_p : p) : p ∨ q := or.intro_left q proof_of_p

/-
- `⊥` is the type without term, or equivalently, false. `¬p` is defined to be `p -> ⊥`.
So to prove `p` is false, we assume `p` and derive a contradiction.
- Suppose `B : A -> Prop`, 
  * then `Π (a : A), B a` can be interpreted as `∀ a : A, B a` because a term of 
  `h : Π (a : A), B a` satisfies `h a : B a` for any `a : A`;
  * then `Σ (a : A), B a` can be interpreted as `∃ a : A, B a` because a term of 
  `⟨a, h⟩ : Σ (a : A), B a` satisfies `h a : B a` and `a : A`.

Now let us have a taste of how proving a theorem feels like using `Lean`.
-/
  
-- noncomputable theory
-- open_locale classical 

-- def mean (x y : ℝ) : ℝ := (x + y) / 2
  
-- theorem min_le_mean : ∀ x y : ℝ, min x y ≤ (mean x y) :=
-- begin
-- intros x y,
-- have ineq1 : min x y ≤ x := min_le_left x y,
-- have ineq2 : min x y ≤ y := min_le_right x y,
    
-- unfold mean, rw le_div_iff (show (0 < (2:ℝ)), by linarith),
-- rw mul_two, 
-- apply add_le_add, 
-- exact ineq1, exact ineq2, 
-- end
  
-- theorem mean_le_max : ∀ x y : ℝ, (mean x y) ≤ max x y :=
-- begin
-- intros x y,
-- have ineq1 : x ≤ max x y := le_max_left x y,
-- have ineq2 : y ≤ max x y := le_max_right x y,
  
-- unfold mean, rw div_le_iff (show (0 < (2:ℝ)), by linarith),
-- rw mul_two,
-- apply add_le_add,
-- exact ineq1, exact ineq2,
-- end
  
-- theorem a_number_in_between : 
--   ∀ x y : ℝ, x ≤ y -> ∃ z : ℝ, x ≤ z ∧ z ≤ y :=
-- begin
-- intros x y hxy,
-- have ineq1 := min_le_mean x y,
-- have ineq2 := mean_le_max x y,
-- have min_eq_x := min_eq_left hxy,
-- have max_eq_y := max_eq_right hxy,
-- use mean x y,
-- split,
  
-- { conv_lhs {rw <-min_eq_x}, exact ineq1, },
-- { conv_rhs {rw <-max_eq_y}, exact ineq2, },
-- end