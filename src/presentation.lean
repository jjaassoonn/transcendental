import algebraic_countable_over_Z
import liouville_theorem
import e_transcendental

noncomputable theory
open_locale classical big_operators

variables (p q : Prop)



------------------------------------------------------------------------------------




/-# Formalisations of basic theorems of trascendental number theory

The main result in this project is the following:
- Countability of algebraic numbers;
- Liouville's theorem and Liouville's number;
- Transcendence of eⁿ for n ≥ 1;                                                 -/






------------------------------------------------------------------------------------




/- # Motivation
 - what is the long term goal?
 - what is the value of such approach in terms of pedagogy? 
 - what is the value of such approach in terms of researching?
    * example of Kepler conjecture;
    * automation;
    * Univalent axiom : (A = B) ≃ (A ≃ B).                                        -/




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





/- ## eⁿ is transcendental for all n ≥ 1                                         -/

-- #print e
-- #print e_pow_transcendental







------------------------------------------------------------------------------------


/-#                       Basic dependent type theory 

                                0        : ℕ
                                ℕ        : Type
                                Type     : Type 1
                                n ↦ n!   : ℕ -> ℕ
                                ⟨0,0⟩    : ℕ × ℕ                                  -/






------------------------------------------------------------------------------------

/- Let `𝓤` be a collection of types and `A` be a type, 
   for a family of types `B : A -> 𝓤`, 

- we can form a new Π-type:
          Π (x : A), B x.
  The terms of this type has the form `f : Π (x : A), B x` such that for any term `a` of type `A`, `f a` is of type `B a`.

- we can form a new Σ-type:
          Σ (x : A), B x.
  The terms of this type has the form `⟨x, h⟩` where `x` has type `A` and `h` has type `B x`.                                                                     -/

------------------------------------------------------------------------------------







/-## Curry-Howard isomorphism : 
     propositions are types whose terms are proofs.                               -/








------------------------------------------------------------------------------------

/-# p -> q 
- Implication is function application.
-/

example : p -> p := id
example (proof_p_imp_q : p -> q) (proof_p : p) : q := 
  proof_p_imp_q proof_p


/-# ⊥ ; ¬p
- false proposition (⊥) is a type without any term (like `∅`).
- negation of p is `p -> ⊥`.
-/
example : ¬ ⊥ := id

------------------------------------------------------------------------------------



/-# p ∧ q

- Conjunction is cartesian product.

-/

example (proof_p : p) (proof_q : q) : p ∧ q := 
  ⟨proof_p, proof_q⟩

example (proof_pq : p ∧ q) : p := proof_pq.1



------------------------------------------------------------------------------------
/-# p ∨ q

- Disjunction is the coproduct, like in category theory with the following universal property:
      f₁           f₂
  ┌--------> X <--------┐
  │          ↑          │
  │          | f        │
  │          |          │
  p -----> p ∨ q <----- q
     left         right
-/

example (proof_of_p : p) : p ∨ q := or.intro_left q proof_of_p

------------------------------------------------------------------------------------



--#                         Quantifiers (∀, ∃)                                    




-- Let B : A -> Prop                                                                




------------------------------------------------------------------------------------
/- 
# Universal Quantifier as Π-type
`Π (a : A), B a` and `∀ a : A, B a` 

# Existential Quantifier as Σ-type  

`Σ (a : A), B a` and `∃ a : A, B a`                                           -/ 




example : ∀ x : ℕ, x ≥ 0 := λ x, bot_le

example : ∃ x : ℕ, x > 0 := ⟨2, two_pos⟩


------------------------------------------------------------------------------------

theorem e_pow_transcendental' (n : ℕ) (hn : n ≥ 1) : transcendental (e^n) :=
begin
  intro alg,
  rcases alg with ⟨p, p_nonzero, hp⟩,
  have e_algebraic : is_algebraic ℤ e,
  {
    set q := ∑ i in finset.range (p.nat_degree + 1), polynomial.C (p.coeff i) * (polynomial.X ^ (i * n)),
    use q,
    split,
    
    -- q is non-zero
    {
      intro rid, 
      rw polynomial.ext_iff at rid,
      replace p_nonzero := (not_iff_not.2 (@polynomial.ext_iff ℤ _ p 0)).1 p_nonzero,
      simp only [not_forall, polynomial.coeff_zero] at p_nonzero,
      choose k hk using p_nonzero,
      replace rid := rid (k * n),
      simp only [polynomial.mul_coeff_zero, polynomial.finset_sum_coeff, polynomial.coeff_zero] at rid,
      simp_rw [polynomial.coeff_C_mul_X] at rid,
      rw finset.sum_eq_single k at rid,
      simp only [mul_one, if_true, true_or, eq_self_iff_true, nat.zero_eq_mul] at rid,
      exact hk rid,

      intros j hj1 hj2, split_ifs,
      replace h := (nat.mul_left_inj _).1 h,
      exfalso,
      exact hj2 (eq.symm h), exact hn, refl,

      intros hk, 
      simp only [not_lt, finset.mem_range] at hk,
      simp only [if_true, eq_self_iff_true],
      apply polynomial.coeff_eq_zero_of_nat_degree_lt,
      linarith, 
    },

    -- q(e) = 0
    {
      have H := polynomial.as_sum p,
      rw H at hp, rw aeval_sum' at hp ⊢, rw <-hp,
      apply finset.sum_congr rfl,
      intros i hi,
      simp only [polynomial.aeval_X, polynomial.aeval_C, alg_hom.map_pow, alg_hom.map_mul],
      
      refine congr rfl _,
      exact pow_mul' e i n,
    }
  },

  exact e_transcendental e_algebraic,
end


-----------------------------------------------------------------------------------
