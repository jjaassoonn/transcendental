-- lemma poly_n'_1_equiv_rat' : poly_n' 1 ≃ rat' :=
-- begin
--   apply equiv.of_bijective, swap, use identify'_1,
--   split,
--   {
--     intros x1 x2 hx, simp [identify'_1] at hx, apply subtype.eq, ext, by_cases (n = 0), rw h, assumption,
--     rw polynomial.coeff_eq_zero_of_nat_degree_lt, rw polynomial.coeff_eq_zero_of_nat_degree_lt,
--     have h := x2.2, cases h with h1 h2,
--     suffices H : 1 ≤ n, linarith, replace h : n ≠ 0 := h, rw <-nat.lt_one_add_iff, norm_num, exact zero_lt_iff_ne_zero.mpr h,
--     have h := x1.2, cases h with h1 h2,
--     suffices H : 1 ≤ n, linarith, replace h : n ≠ 0 := h, rw <-nat.lt_one_add_iff, norm_num, exact zero_lt_iff_ne_zero.mpr h,
--   },

--   {
--     intro x1,
--     generalize hq : polynomial.C x1.1 = q,
--     have q_ne_0 : q ≠ 0, {intro absurd, rw polynomial.ext_iff at absurd, have absurd' := absurd 0, simp at absurd', rw <-hq at absurd', simp at absurd', exact x1.2 absurd'},
--     have q_deg : q.nat_degree < 1, rw <-hq, simp, 
--     generalize hq' : (⟨q, ⟨q_ne_0, q_deg⟩⟩ : poly_n' 1) = q',
--     use q',
--     simp [identify'_1], have h : q'.val = q, {rw <-hq'}, apply subtype.eq, simp, rw h, rw <-hq, simp,
--   },
--   done
-- end



-- theorem bij1 : ∀ (n : nat), (n ≠ 0) -> ∃ f : (poly_n n) -> (rat_n n), function.bijective f :=
-- begin
--   intros n hn,
--   use identify n,
--   split,

--   -- injective (canno)
--   exact inj_identify_n n hn,

--   -- surjective
--   exact sur_identify_n n hn,

-- end

-- theorem poly_n_equiv_rat_n (n : nat) : (poly_n n.succ) ≃ (rat_n n.succ) :=
-- begin
--   let f := identify n.succ,
--   have f_bij : function.bijective f := ⟨inj_identify_n n.succ (nat.succ_ne_zero n), sur_identify_n n.succ (nat.succ_ne_zero n)⟩,
--   exact equiv.of_bijective f_bij,
--   done
-- end



-- theorem roots_card (p : polynomial rat) (hp : p ≠ 0) : (poly_rat_to_poly_real p).roots.card <= p.nat_degree :=
-- begin
--   have g := @polynomial.card_roots _ _ (poly_rat_to_poly_real p) ((poly_rat_to_poly_real_ne_zero p).mp hp),
--   rw [<-(poly_rat_to_poly_real_preserve_deg p), polynomial.degree_eq_nat_degree, with_bot.coe_le_coe] at g; assumption,
--   done
-- end

-- theorem roots_real_countable (p : polynomial rat) (hp : p ≠ 0) : set.countable (roots_real p) := @set.countable_finite real (roots_real p) (roots_finite p hp)
