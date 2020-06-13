

# Transcendental Numbers


This project is to prove several theorems in transcendental number theory:
1. [x] Countability argument: abstract existence of transcendental number;
2. [x] Liouvielly theorem and hence ![](https://latex.codecogs.com/gif.latex?\sum_{i=0}^\infty&space;\frac{1}{10^{n!}}) is transcendental;
3. [ ] ![](https://latex.codecogs.com/gif.latex?e) is transcendental;
4. [ ] ![](https://latex.codecogs.com/gif.latex?\pi) is transcendental.

## Part 1, countability argument:
The main theorem is in [algebraic_countable.lean](https://github.com/jjaassoonn/transcendental/blob/1d649f2e168383c5322cc96351b98447944a845c/src/algebraic_coutable.lean#L890)
```lean
theorem transcendental_number_exists : ∃ x : real, ¬ (is_algebraic ℚ x) 
```

## Part 2, Liouville theorem and an explicit Liouville number:
Definition of the explicit liouville number is in [liouville_theorem.lean](https://github.com/jjaassoonn/transcendental/blob/897722f8ed408607ec0a0d30e200e41aa49ed9e3/src/liouville_theorem.lean#L863)

```lean
def α := ∑' n, ten_pow_n_fact_inverse n
```

The main theorem is in [liouville_theorem.lean](https://github.com/jjaassoonn/transcendental/blob/897722f8ed408607ec0a0d30e200e41aa49ed9e3/src/liouville_theorem.lean#L694):
```lean
theorem liouville_numbers_transcendental : ∀ x : real, liouville_number x -> ¬(is_algebraic ℤ x)

theorem transcendental_α : transcendental α := liouville_numbers_transcendental α liouville_α
```
