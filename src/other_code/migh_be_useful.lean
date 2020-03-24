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



-- def algebraic_set : set real := {x | is_algebraic rat x }
-- def poly_monic_irr : Type := {p : polynomial rat // irreducible p ∧ polynomial.monic p}

-- theorem minimal_polynomial_of_x : ∀ (x : real), (is_algebraic rat x) <-> ∃ (p : poly_monic_irr), polynomial.aeval rat real x p.1 = 0 :=
-- begin
--   intro x, split, intro hx,
--   have hx' : is_integral rat x, rw <-is_algebraic_iff_is_integral, exact hx,
--   cases hx with p hp,
--   generalize hq : minimal_polynomial hx' = q,
--   use q, split; rw <-hq, exact minimal_polynomial.irreducible hx', exact minimal_polynomial.monic hx', 
--   simp [hq], have g := minimal_polynomial.aeval hx', rwa hq at g,

--   intro hq, choose q hq using hq, use q.1,
--   exact ⟨(polynomial.monic.ne_zero_of_zero_ne_one (by simp) q.2.2), hq⟩,
-- end


-- theorem lcm_commutative : is_commutative nat nat.lcm :=
-- begin
--   apply is_commutative.mk, intros n1 n2, apply nat.lcm_comm,
-- end

-- theorem lcm_associatuve : is_associative nat nat.lcm :=
-- begin
--   apply is_associative.mk, intros n1 n2 n3, apply nat.lcm_assoc,
-- end

-- instance : is_commutative nat nat.lcm :=
-- begin
--   apply is_commutative.mk, intros n m, exact nat.lcm_comm n m,
-- end

-- instance : is_commutative nat nat.gcd :=
-- begin
--   apply is_commutative.mk, intros n m, exact nat.gcd_comm n m
-- end

-- instance : is_associative nat nat.lcm :=
-- begin
--   apply is_associative.mk, intros a b c, exact nat.lcm_assoc a b c,
-- end

-- instance : is_associative nat nat.gcd :=
-- begin
--   apply is_associative.mk, intros a b c, exact nat.gcd_assoc a b c,
-- end

-- def all_coprime (S : finset nat): Prop := ∀ (i j ∈ S), i ≠ j -> nat.coprime i j

-- def denom_of_finset_rat (S : finset rat) : finset nat := (finset.image (fun r : rat, r.denom) S)
-- def num_of_finset_rat (S : finset rat) : finset int := (finset.image (fun r : rat, r.num) S)
-- def abs_num_of_finset_rat (S : finset rat) : finset nat := (finset.image (fun r : rat, int.nat_abs r.num) S) 

-- def lcm_of_finset_nat (S : finset nat) : nat := finset.fold nat.lcm 1 id S
-- def gcd_of_finset_nat (S : finset nat) : nat := finset.fold nat.gcd 1 id S

-- def rat_to_nat_by_times (n : nat) (r : rat) := nat.div (r.num.nat_abs * n) r.denom
-- def finset_rat_to_finset_nat (S : finset rat) := finset.image (rat_to_nat_by_times $ (lcm_of_finset_nat (denom_of_finset_rat S))) S
-- def clear_denominator_finset_rat (S : finset rat) : finset nat := 
--   finset.image (rat_to_nat_by_times (nat.div (gcd_of_finset_nat (abs_num_of_finset_rat S)) (lcm_of_finset_nat (denom_of_finset_rat S)))) S

-- def finset_rat_finset_nat (S : finset rat) : finset nat :=




-- theorem clear_denominator_all_coprime (S : finset rat) : all_coprime (clear_denominator_finset_rat S) :=
-- begin
--   induction S using finset.induction_on with q S hq hS,
--   {
--     rw [clear_denominator_finset_rat, all_coprime],
--     intros i j hi hj H, destruct hi,
--   },
--   {
--     intros i j hi hj H, rw [clear_denominator_finset_rat, abs_num_of_finset_rat, denom_of_finset_rat] at hi hj,
--     repeat {rw [finset.image_insert] at hi hj},
--     -- rw [<-rat_to_nat_by_times] at hi,
    
    
--   },

-- end



-- @[simp] theorem denom_of_insert_r_S_eq_insert_r_denom_S (S : finset rat) (r : rat): denom_of_finset_rat (insert r S) = insert r.denom (denom_of_finset_rat S) :=
-- begin
--   apply finset.induction_on S,
--   conv_rhs {rw [denom_of_finset_rat, finset.image_empty]},
--   conv_lhs {rw [denom_of_finset_rat, finset.image_insert, finset.image_empty]},

--   intros r S' hr hS',
--   conv_lhs {rw [denom_of_finset_rat, finset.image_insert, <-denom_of_finset_rat]},
-- end

-- -- theorem S_subset_T_T_coprime_S_coprime (S T : finset nat) (h : S ⊆ T) (hT : all_coprime T) : all_coprime S :=
-- -- begin
-- --   intros x y h1 h2 h3, have h1': x ∈ T, exact h h1, have h2': y ∈ T, exact h h2, 
-- --   exact hT x y h1' h2' h3,
-- -- end

-- @[simp] theorem all_coprime_insert_a_S_iff_a_coprime_all_S (S : finset nat) : ∀ (a : nat), ¬ a ∈ S ->
--   (all_coprime (insert a S) -> ∀ s ∈ S, nat.coprime a s) :=
-- begin
--   intros a ha H s hs,
--   suffices H1 : s ∈ insert a S,
--   suffices H2 : a ≠ s,
--   exact H a s (finset.mem_insert_self _ _) H1 H2,
--     by_contra H2, simp at H2, rw H2 at ha, exact ha hs,
--     exact finset.mem_insert_of_mem hs,
-- end

-- variable (S : finset rat)
-- #check rat_to_nat_by_times
-- #check (rat_to_nat_by_times $ (lcm_of_finset_nat ∘ denom_of_finset_rat) S)

-- @[simp] theorem lcm_of_empty_eq_1 : lcm_of_finset_nat ∅ = 1 :=
-- begin
--   rw [lcm_of_finset_nat], refl,
-- end

-- @[simp] theorem lcm_of_singleton_n_eq_n (n : nat) : lcm_of_finset_nat (finset.singleton n) = n :=
-- begin
--   simp [lcm_of_finset_nat, finset.fold_singleton, nat.lcm_one_right],
-- end

-- @[simp] theorem gcd_a_lcm_a_b_eq_a (a b : nat) : nat.gcd a (nat.lcm a b) = a :=
-- begin
--   apply nat.gcd_eq_left, exact nat.dvd_lcm_left a b,
-- end

-- @[simp] theorem lcm_idempotent (a b : nat) : nat.lcm a (nat.lcm a b) = nat.lcm a b :=
-- begin
--   by_cases (a = 0); rename h ha; by_cases (b = 0); rename h hb,
--   rwa [ha, hb], simp [ha, nat.lcm_zero_left], simp [ha, nat.lcm_zero_left],
--   simp [hb, nat.lcm_zero_right],
--   rw nat.lcm, rw [gcd_a_lcm_a_b_eq_a, nat.mul_comm, nat.mul_div_left], exact zero_lt_iff_ne_zero.mpr ha,
-- end

-- theorem n_mem_S_n_dvd_lcm_S (S : finset nat) (n ∈ S) : n ∣ lcm_of_finset_nat S :=
-- begin
--   apply @finset.induction nat (fun S, ∀ n ∈ S, n ∣ lcm_of_finset_nat S),
--   intros n hn, exfalso, exact hn,
--   intros a S ha hS m hm, rw finset.mem_insert at hm, 
--   cases hm with hm hm, rw hm,
--     rw [lcm_of_finset_nat, finset.fold_insert], simp, exact nat.dvd_lcm_left a (finset.fold nat.lcm 1 (λ (x : ℕ), x) S),

--     assumption, rw [lcm_of_finset_nat, finset.fold_insert], simp,
--     have H := hS m hm, have i : (λ (x : ℕ), x) = id := rfl, rw [i, <-lcm_of_finset_nat],
--     apply dvd_trans H, exact nat.dvd_lcm_right a (lcm_of_finset_nat S), assumption, assumption,
-- end

-- theorem a_dvd_b_gcd_a_b_eq_a (a b : nat) (h : a ∣ b) : nat.gcd a b = a :=
-- begin
--   exact nat.gcd_eq_left h,
-- end

-- theorem a_dvd_b_lcm_a_b_eq_b (a b : nat) (h0 : a ≠ 0) (h : a ∣ b) : nat.lcm a b = b :=
-- begin
--   by_cases (b = 0); rename h hb,
--   rw [hb, nat.lcm_zero_right],
--   rw [nat.lcm, nat.gcd_eq_left h, nat.mul_comm, nat.mul_div_cancel], exact zero_lt_iff_ne_zero.mpr h0,
-- end

-- theorem lcm_lcm_of_finset_nat_assoc (a b : nat) (S : finset nat) :
--   nat.lcm a (nat.lcm b (lcm_of_finset_nat S)) = nat.lcm (nat.lcm a b) (lcm_of_finset_nat S) :=
-- begin
--   apply @finset.induction_on nat (fun S, ∀ a b : nat, nat.lcm a (nat.lcm b (lcm_of_finset_nat S)) = nat.lcm (nat.lcm a b) (lcm_of_finset_nat S)),
--   intros, rw [lcm_of_empty_eq_1], rwa [nat.lcm_comm, nat.lcm_one_right, nat.lcm_one_right, nat.lcm_comm],

--   intros c' S' hc' hS' a' b',
--   rw [lcm_of_finset_nat, finset.fold_insert, <-lcm_of_finset_nat], simp,
--   rw [(hS' b' c'), nat.lcm_assoc],
--   conv_rhs {rw nat.lcm_assoc}, assumption,
-- end

-- theorem n_mem_S_lcm_n_insert_S_eq_lcm_S (S : finset nat) (n ∈ S) : nat.lcm n (lcm_of_finset_nat S) = (lcm_of_finset_nat S) :=
-- begin
--   apply @finset.induction_on nat (fun S, ∀ n ∈ S, nat.lcm n (lcm_of_finset_nat S) = (lcm_of_finset_nat S)),
--   -- empty
--   intros m hm, exfalso, exact hm,
--   -- induction
--   intros m S' hm hS' a ha, cases (finset.mem_insert.mp ha) with ha ha,
--     rw [ha, lcm_of_finset_nat, finset.fold_insert, <-lcm_of_finset_nat], simp, assumption,
--     rw [lcm_of_finset_nat, finset.fold_insert, <-lcm_of_finset_nat], simp,
--     rw [lcm_lcm_of_finset_nat_assoc, nat.lcm_comm a m, <-lcm_lcm_of_finset_nat_assoc, hS' a ha], assumption, assumption,
-- end

-- theorem lcm_of_insert_finset_nat (S : finset nat) (n : nat) : lcm_of_finset_nat (insert n S) = nat.lcm n (lcm_of_finset_nat S) :=
-- begin
--   by_cases (n ∈ S),
--   rw [finset.insert_eq_of_mem, n_mem_S_lcm_n_insert_S_eq_lcm_S], assumption, assumption,
--   rw [lcm_of_finset_nat, finset.fold_insert, <-lcm_of_finset_nat], simp, assumption,
-- end

-- theorem n_div_lcm_of_finset_nat (S : finset nat) : ∀ (n ∈ S), n∣lcm_of_finset_nat S :=
-- begin
--   -- rw [nat.dvd_iff_mod_eq_zero, lcm_of_finset_nat],
--   apply @finset.induction_on nat (fun S : finset nat, ∀ (n ∈ S), n∣lcm_of_finset_nat S),

--   intros n hn, exfalso, simpa,

--   intros n S hn hS m hm, rw finset.mem_insert at hm,
--   cases hm with h1 h2, rw h1,
--   rw [lcm_of_finset_nat, finset.fold_insert, <-lcm_of_finset_nat], simp, exact nat.dvd_lcm_left n (lcm_of_finset_nat S),
--   rwa <-h1 at hn, rwa h1 at hn,
--   rw [lcm_of_finset_nat, finset.fold_insert, <-lcm_of_finset_nat], simp, have hm := hS m h2,
--   apply (dvd.trans hm), exact nat.dvd_lcm_right n (lcm_of_finset_nat S), assumption,
-- end


-- theorem coprime_if_no_prime_divide_both {n m : nat} : ¬(∃ p : nat, nat.prime p ∧ (p ∣ m) ∧ (p ∣ n)) -> nat.coprime n m :=
-- begin
--   intro H,
--   rw [not_exists] at H,
--   rw nat.coprime, by_contra gcd_pos,
--   generalize hg : nat.gcd n m = g,
--   generalize hp : nat.min_fac g = p,
--   have p_prime : nat.prime p, 
--   { have h := nat.min_fac_prime gcd_pos, rw [hg, hp] at h, exact h},
--   have p_dvd_n : p ∣ n,
--   { 
--     have h := nat.min_fac_dvd g, rw [<-hg] at h, conv_lhs at h {rw hg, rw hp},
--     apply dvd.trans h, exact nat.gcd_dvd_left n m,
--   },
--   have p_dvd_m : p ∣ m,
--   { 
--     have h := nat.min_fac_dvd g, rw [<-hg] at h, conv_lhs at h {rw hg, rw hp},
--     apply dvd.trans h, exact nat.gcd_dvd_right n m,
--   },
--   exact (H p) ⟨p_prime, ⟨p_dvd_m, p_dvd_n⟩⟩,
-- end

-- theorem finset_rat_to_finset_nat_all_coprime (S : finset rat) : all_coprime (finset_rat_to_finset_nat S) :=
-- begin
--   intros n1 n2 hn1 hn2 hn,
--   by_contra H,
--   -- rw [finset_rat_to_finset_nat, finset.mem_image] at hn1,
--   -- rw [finset_rat_to_finset_nat, finset.mem_image] at hn2,
--   -- choose q1 hq1 using hn1, cases hq1 with hq1 Hn1,
--   -- choose q2 hq2 using hn2, cases hq2 with hq2 Hn2,
--   -- apply coprime_if_no_prime_divide_both,
--   -- intro hp,
--   -- choose p hp using hp,
  
--   -- apply @finset.induction_on rat (fun S, all_coprime (finset_rat_to_finset_nat S)),
--   -- -- empty
--   -- intros i j hi hj hij, simp [finset_rat_to_finset_nat] at hi, exfalso, exact hi,

--   -- -- induction
--   -- intros a S' ha hS',
--   -- rw [finset_rat_to_finset_nat, denom_of_insert_r_S_eq_insert_r_denom_S, lcm_of_insert_finset_nat, finset.image_insert],
--   -- generalize hG : finset_rat_to_finset_nat S' = G,
--   -- rw [finset_rat_to_finset_nat] at hG,
  
--   -- intros n1 n2 hn1 hn2 hn12, simp [finset_rat_to_finset_nat] at hn1 hn2,
--   -- choose r1 hr1 using hn1, choose r2 hr2 using hn2,
--   -- cases hr1 with hr11 hr12, cases hr2 with hr21 hr22,
--   -- rw [rat_to_nat_by_times] at hr12 hr22,
--   -- generalize hN : lcm_of_finset_nat (denom_of_finset_rat S) = N,
--   -- rw hN at hr12 hr22,
--   -- type_check @nat.div_eq_iff_eq_mul_left N r2.denom r2.num.nat_abs r2.pos,
--   -- rw [<-hr12, <-hr22],


--   -- generalize hN1 : nat.div N r1.denom = N1,
--   -- generalize hN2 : nat.div N r2.denom = N2,
--   -- rw hN at hr22 hr12,
--   -- have H1 : n1 = N1 * r1.num.nat_abs,
--   -- rw <-hN1, rw <-hr12, rw nat.mul_div_assoc,
  
--   -- apply nat.div_mul_cancel,
--   -- delta nat.coprime,
--   -- rw [<-hr12, <-hr22],
-- end

-- -- variable S : finset rat
-- -- #check (rat_to_nat_by_times $ (lcm_of_finset_nat ∘ denom_of_finset_rat) S)
-- -- #eval int.div 6 3

-- def poly_rat_to_poly_int (p : polynomial rat) : polynomial int :=
-- begin
--   -- N is the lcm of numerator of coef of p
--   generalize hN : @finset.fold int _ (fun z1 z2, int.of_nat $ int.lcm z1 z2) sorry sorry 1 id
--     (finset.image (fun n : nat, (p.2 n).num) p.1) = N,

--     -- (finset.map (fun q : rat, q.num) (finset.image p.2)) = N,
--   constructor, swap, exact p.1, swap,
-- end

-- def zminimal_polynomial_of_x (x : real) (hx : is_algebraic rat x) :
--   ∃ (p : polynomial int), polynomial.aeval int real x p = 0 ∧ irreducible p :=
-- begin
--   choose p hp using (minimal_polynomial_of_x x).mp hx,
-- end