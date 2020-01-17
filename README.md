

# Transcendental Numbers


This project is to prove several theorems in transcendental number theory:
1. [x] Countability argument: abstract existence of transcendental number;
2. [ ] Liouvielly theorem and hence $ \sum_{i=0}^{\infty}\frac{1}{10^{n!}} $ is transcendental;
3. [ ] $e$ is transcendental;
4. [ ] $\pi$ is transcendental.

## Part 1, countability argument:
The main theorem is in [algebraic_countable.lean](https://github.com/jjaassoonn/transcendental/blob/1d649f2e168383c5322cc96351b98447944a845c/src/algebraic_coutable.lean#L890)
```lean
theorem transcendental_number_exists : ∃ x : real, ¬ (is_algebraic rat x) 
```
