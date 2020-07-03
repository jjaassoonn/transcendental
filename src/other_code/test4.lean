-- import data.real.basic
-- import data.polynomial
-- import data.mv_polynomial
-- import ring_theory.algebra
-- import ring_theory.algebraic
-- import play

-- noncomputable theory

-- def set1 : set real := {x | ∃ p : polynomial rat, p ≠ 0 ∧ polynomial.aeval rat real x p = 0 }
-- def set2 : set real := {x | ∃ n : nat, ∃ p : poly_n n.succ, p.1 ≠ 0 ∧ polynomial.aeval rat real x p.1 = 0}


-- theorem aaa : set1 = set2 :=
-- begin
-- ext,

-- split,
-- {
--     intro hx,
--     cases hx with p hp,
--     cases hp with hp_ne0 hpx_0,
--     constructor, swap, exact p.nat_degree,
--     use p,
--     exact lt_add_one (polynomial.nat_degree p),
--     simp,
--     exact  ⟨hp_ne0 , hpx_0⟩,
-- },

-- {
--     intro hx,
--     cases hx with deg hp,
--     cases hp with p hp,
--     cases hp with hp1 hp2,

--     constructor, swap,
--     exact p.1,
--     exact ⟨hp1, hp2⟩,
-- },
-- done
-- end


-- -- [a-1, a+1] is compact, hence a continuous function attains a maximum and a minimum.
-- -- lemma closed_interval_compact (a : real) : compact $ set.Icc (a-1) (a+1) :=
-- -- begin
-- --   rw metric.compact_iff_closed_bounded, split,
-- --   {
-- --     -- closed
-- --     exact is_closed_Icc,
-- --   },
-- --   {
-- --     unfold metric.bounded,
-- --     use 2, intros x₁ x₂ h1 h2, simp only [set.mem_Icc] at h1 h2, unfold dist, rw abs_le, split,
-- --     {
-- --       have eq1 : a + 1 = -(-(a + 1)) := by norm_num,
-- --       have ineq1 := h2.2, conv_rhs at ineq1 {rw eq1}, rw le_neg at ineq1,
-- --       have ineq2 := h1.1, have ineq3 := add_le_add ineq1 ineq2,
-- --       have eq2 : -(a + 1) + (a - 1) = -2 := by ring,
-- --       have eq3 : -x₂ + x₁ = x₁ - x₂ := by ring,
-- --       conv_lhs at ineq3 {rw eq2},conv_rhs at ineq3 {rw eq3}, exact ineq3,
-- --     },
-- --     {
-- --       have ineq1 := h1.2,
-- --       have ineq2 := h2.1, have eq1 : x₂ = -(-x₂) := by norm_num,
-- --       rw [eq1, le_neg] at ineq2, have ineq3 := add_le_add ineq1 ineq2,
-- --       have eq2 : a + 1 + -(a - 1) = 2 := by ring, rw eq2 at ineq3,
-- --       have eq3 : x₁ + -x₂ = x₁ - x₂ := by ring, rw eq3 at ineq3, exact ineq3,
-- --     },
-- --   }
-- -- end

-- -- prove using induction on polynomial
-- theorem induction_on_degree {a : Type} {inst : comm_semiring a} (M : polynomial a -> Prop)
--     (deg_0 : ∀ p : polynomial a, (p.degree = 0) -> M p)
--     (inductive_hyp : ∀ n : ℕ, (∀ p : polynomial a, (p.degree ≤ n) -> M p) -> (∀ q : polynomial a, (q.degree = n.succ) -> M q)) :
--     ∀ f : polynomial a, M f :=

-- begin
--     classical,
--     -- let S be all polynomials not satisfying M,
--     generalize hS : {f : polynomial a | ¬ M f} = S,
--     suffices : S = ∅,
--     {
--         intro f, by_contra absurd, have rid : f ∈ S,
--         rw <-hS, simp, exact absurd, rw this at rid, simpa,
--     },
--     by_contra rid,
--     generalize hS_deg : S.image (λ f : polynomial a, f.degree) = S_deg,
--     -- then S_deg is non_empty
--     have S_deg_nonempty : S_deg ≠ ∅, rw [<-hS_deg],
--     {   
--         by_contra rid', simp at rid', exact rid rid',
--     },
--     replace S_deg_nonempty : S_deg.nonempty, exact set.nmem_singleton_empty.mp S_deg_nonempty,
--     -- then S_deg has min element
--     -- have H := @with_bot.well_founded_lt (with_bot ℕ) _ (<),
--     choose m hm using (@well_founded.has_min (with_bot ℕ) (<) (with_bot.well_founded_lt nat.lt_wf) S_deg S_deg_nonempty),
--     have hm1 := hm.1, have hm2 := hm.2,
--     rw [<-hS_deg, set.mem_image] at hm1,
--     choose f hf using hm1,
--     have M_g : ∀ g : polynomial a, (g.degree) < m -> M g, {
--         by_contra rid, simp at rid,
--         choose g hg using rid,
--         have rid' : g.degree ∈ S_deg, rw [<-hS_deg, set.mem_image],
--         use g, simp, rw [<-hS], simp, exact hg.2,
--         replace rid' := hm2 g.degree rid',
--         exact rid' hg.1,
--     },


-- end

-- -- prove using induction on polynomial
-- theorem induction_on_degree {a : Type} {inst : comm_semiring a} (M : polynomial a -> Prop)
--     (deg_0 : ∀ p : polynomial a, (p.degree = 0) -> M p)
--     (inductive_hyp : ∀ n : ℕ, (∀ p : polynomial a, (p.degree ≤ n) -> M p) -> (∀ q : polynomial a, (q.degree = n.succ) -> M q)) :
--     ∀ f : polynomial a, M f :=

-- begin
--     classical,
--     -- let S be all polynomials not satisfying M,
--     generalize hS : {f : polynomial a | ¬ M f} = S,
--     suffices : S = ∅,
--     {
--         intro f, by_contra absurd, have rid : f ∈ S,
--         rw <-hS, simp, exact absurd, rw this at rid, simpa,
--     },
--     by_contra rid,
--     generalize hS_deg : S.image (λ f : polynomial a, f.degree) = S_deg,
--     -- then S_deg is non_empty
--     have S_deg_nonempty : S_deg ≠ ∅, rw [<-hS_deg],
--     {   
--         by_contra rid', simp at rid', exact rid rid',
--     },
--     replace S_deg_nonempty : S_deg.nonempty, exact set.nmem_singleton_empty.mp S_deg_nonempty,
--     -- then S_deg has min element
--     -- have H := @with_bot.well_founded_lt (with_bot ℕ) _ (<),
--     choose m hm using (@well_founded.has_min (with_bot ℕ) (<) (with_bot.well_founded_lt nat.lt_wf) S_deg S_deg_nonempty),
--     have hm1 := hm.1, have hm2 := hm.2,
--     rw [<-hS_deg, set.mem_image] at hm1,
--     choose f hf using hm1,
--     have M_g : ∀ g : polynomial a, (g.degree) < m -> M g, {
--         by_contra rid, simp at rid,
--         choose g hg using rid,
--         have rid' : g.degree ∈ S_deg, rw [<-hS_deg, set.mem_image],
--         use g, simp, rw [<-hS], simp, exact hg.2,
--         replace rid' := hm2 g.degree rid',
--         exact rid' hg.1,
--     },


-- end