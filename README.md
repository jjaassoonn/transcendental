
# Transcendental Numbers

This project is to prove several theorems in transcendental number theory:

1. [x] Countability argument: abstract existence of transcendental number;
2. [x] Liouvielle theorem and hence ![liouville number](https://latex.codecogs.com/gif.latex?\sum_{i=0}^\infty&space;\frac{1}{10^{n!}}) is transcendental;
3. [x] ![e](https://latex.codecogs.com/gif.latex?e) is transcendental;
4. [ ] ![pi](https://latex.codecogs.com/gif.latex?\pi) is transcendental.

## Part 1, countability argument

The main theorem is in [algebraic_countable_over_Z.lean](https://github.com/jjaassoonn/transcendental/blob/master/src/algebraic_countable_over_Z.lean#L731)

```lean
theorem transcendental_number_exists : ∃ x : real, ¬ (is_algebraic ℤ x)
```

The other version is in [algebraic_countable_over_Q.lean](https://github.com/jjaassoonn/transcendental/blob/master/src/algebraic_countable_over_Q.lean#L897)

```lean
theorem transcendental_number_exists : ∃ x : real, ¬ (is_algebraic ℚ x)
```

## Part 2, Liouville theorem and an explicit Liouville number

Definition of the explicit Liouville number is in [liouville_theorem.lean](https://github.com/jjaassoonn/transcendental/blob/master/src/liouville_theorem.lean#L1136)

```lean
def α := ∑' n, ten_pow_n_fact_inverse n
```

The main theorem is in [liouville_theorem.lean](https://github.com/jjaassoonn/transcendental/blob/master/src/liouville_theorem.lean#L863):

```lean
theorem liouville_numbers_transcendental : ∀ x : real, liouville_number x -> ¬(is_algebraic ℤ x)

theorem transcendental_α : transcendental α := liouville_numbers_transcendental α liouville_α
```

## Part 3, the transcendence of e

We defined e in [e_transcendental.lean](https://github.com/jjaassoonn/transcendental/blob/699e50a6d262ee73ab20bfa6362ed637d4e88c77/src/e_transcendental.lean#L15) as :

``` lean
def e : ℝ := real.exp 1
```

The main theorem is at [e_transcendental.lean](https://github.com/jjaassoonn/transcendental/blob/699e50a6d262ee73ab20bfa6362ed637d4e88c77/src/e_transcendental.lean#L1798):

```lean
theorem e_transcendental : ¬ is_algebraic ℤ e :=
```

Here is the catch. I used the following theorems directly without prove. But all the functions used were proved to be measurable and integrable on closed interval. Once ftc is in the `mathlib` I will change ftc to its correct form and prove the relevant assumption.

``` lean
axiom ftc (f: ℝ -> ℝ) (a b : ℝ) (h : b ≥ a) :  (∫ x in set.Icc a b, (deriv f) x) = f b - f a
axiom integrate_by_part (f g : ℝ -> ℝ) (a b : ℝ) (h : b ≥ a) :
    (∫ x in set.Icc a b, (f x)*(deriv g x)) = (f b) * (g b) - (f a) * (g a) - (∫ x in set.Icc a b, (deriv f x) * (g x))
```

Please see [this](https://jjaassoonn.github.io/transcendental/src/doc/e_transcendental_doc.html) for an explanation of the proof of transcendence of $e$ with reference to Lean code.

I haven't finished documentation (not even close), but you can click around the proves I documented so far
at [e_trans_helpers2.lean](https://jjaassoonn.github.io/transcendental/html/e_trans_helpers.html) and[e_transcendental.lean](https://jjaassoonn.github.io/transcendental/html/e_transcendental.html).
