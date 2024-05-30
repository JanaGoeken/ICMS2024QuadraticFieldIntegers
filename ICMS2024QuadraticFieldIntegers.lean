import Mathlib

theorem SquarefreePartFactorizationNat (n : ℕ) : ∃ k : ℕ, ∃ l : ℕ, n = k^2*l ∧ Squarefree l := by
  by_cases h : n = 0
  · use 0,2
    constructor
    · rw [h]
      norm_num
    · exact Nat.squarefree_two
  · let factors := UniqueFactorizationMonoid.normalizedFactors n
    let distinct_factors := Multiset.dedup factors
    let odd_mult_factors := Multiset.filter (fun (p : ℕ) => Odd (Multiset.count p factors)) distinct_factors
    let even_part_factors := factors - odd_mult_factors
    let squarefree_part := Multiset.prod odd_mult_factors

    have exponents_even : (∀ (p : ℕ), (Even (Multiset.count p even_part_factors))) := by
      intro p
      rw [Multiset.count_sub]
      by_cases hp : p ∈ odd_mult_factors
      · rw [Multiset.count_filter_of_pos]
        · rw [Multiset.count_dedup]
          rw [Multiset.mem_filter] at hp
          rw [Multiset.mem_dedup] at hp
          rw [if_pos]
          let hodd := hp.2
          rw [Odd] at hodd
          rcases hodd with ⟨k,hk⟩
          rw [hk]
          simp
          exact hp.1
        · rw [Multiset.mem_filter] at hp
          exact hp.2
      · rw [Multiset.count_filter_of_neg]
        simp only [tsub_zero]
        apply Nat.even_iff_not_odd.2 _
        contrapose! hp
        rw [Multiset.mem_filter]
        constructor
        · contrapose! hp
          apply Nat.even_iff_not_odd.1 _
          rw [Multiset.mem_dedup] at hp
          rw [Multiset.count_eq_zero_of_not_mem hp]
          exact even_zero
        · exact hp

        contrapose! hp
        rw [Multiset.mem_filter]
        constructor
        · contrapose! hp
          apply Nat.even_iff_not_odd.1 _
          rw [Multiset.mem_dedup] at hp
          rw [Multiset.count_eq_zero_of_not_mem hp]
          exact even_zero
        · exact hp

    -- Union over p in distinct_primes of Multiset.replicate (Multiset.count p even_part_factors)/2 p
    let half_multiset : Multiset ℕ := Multiset.bind distinct_factors (fun p => Multiset.replicate ((Multiset.count p even_part_factors)/2) p)

    let sq_part := half_multiset.prod

    use sq_part, squarefree_part
    constructor
    · have double_lemma : half_multiset + half_multiset = even_part_factors := by
        rw [Multiset.ext]
        rintro p
        rw [Multiset.count_add, ← mul_two]
        rw [Multiset.count_bind]
        simp_rw [Multiset.count_replicate]
        -- sum(map f X) = f(p) and X is nodup where f(x) is zero for x =/= p
        set f : ℕ → ℕ := fun x => if p = x then Multiset.count x even_part_factors / 2 else 0 with f_def
        have f_supp : ∀ (q : ℕ), q ≠ p → (q ∈ distinct_factors) → f q = 0 := by
          rintro q hqp hq
          contrapose! hqp
          rw [f_def] at hqp
          simp at hqp
          exact hqp.1.symm
        rw [Multiset.sum_map_eq_nsmul_single p f_supp]
        rw [Multiset.count_dedup]
        by_cases hp0 : p ∈ factors
        · rw [if_pos hp0]
          simp
          by_cases hpodd : p ∈ odd_mult_factors
          · rw [f_def]
            simp
            exact Nat.div_two_mul_two_of_even (exponents_even p)
          · rw [f_def]
            simp
            exact Nat.div_two_mul_two_of_even (exponents_even p)

        · rw [if_neg hp0]
          rw [Multiset.count_sub,Multiset.count_eq_zero_of_not_mem]
          simp
          exact hp0

      have full_multiset_lemma : even_part_factors + odd_mult_factors = factors := by
        have sub_inter : factors ∩ odd_mult_factors = odd_mult_factors := by
          rw [← Multiset.inf_eq_inter]
          rw [inf_eq_right]
          exact le_trans (Multiset.filter_le (fun p => Odd (Multiset.count p factors)) distinct_factors) (Multiset.dedup_le factors)
        rw [← sub_inter]
        apply Multiset.sub_add_inter

      rw [pow_two]
      rw [← Multiset.prod_add]
      rw [← Multiset.prod_add]
      rw [double_lemma]
      rw [full_multiset_lemma]
      rw [← associated_iff_eq]
      apply Associated.symm
      exact UniqueFactorizationMonoid.normalizedFactors_prod h

    · have sqfree_nonzero : squarefree_part ≠ 0 := by
        intro h0
        rw [Multiset.prod_eq_zero_iff] at h0
        apply Multiset.mem_of_mem_filter at h0
        rw [Multiset.mem_dedup] at h0
        rw [← Multiset.prod_eq_zero_iff] at h0
        have fact_prod : factors.prod = n := by
          rw [← associated_iff_eq]
          exact UniqueFactorizationMonoid.normalizedFactors_prod h
        rw [fact_prod] at h0
        exact h h0

      rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors]
      rw [UniqueFactorizationMonoid.normalizedFactors_prod_of_prime]
      apply Multiset.Nodup.filter
      exact Multiset.nodup_dedup factors
      · rintro p hp
        apply Multiset.mem_of_mem_filter at hp
        rw [Multiset.mem_dedup] at hp
        exact UniqueFactorizationMonoid.prime_of_normalized_factor p hp
      · exact sqfree_nonzero

theorem SquarefreePartFactorizationRat (q : ℚ) : ∃ k : ℚ, ∃ l : ℤ, q = k^2*l ∧ Squarefree l := by
  by_cases hq : q = 0
  · use 0, 2
    constructor
    · simp
      exact hq
    · rw [← Int.squarefree_natAbs]
      exact Nat.squarefree_two
  · let a := q.num
    let b := q.den
    let q_int := a*b
    have q_frac : q = q_int/b^2 := by
      rw [← Rat.num_div_den q]
      unfold_let q_int a b
      have b_nonzero : q.den ≠ 0 := by
        exact Rat.den_nz q
      field_simp
      ring
    let q_nat := (a*b).natAbs
    have q_nat_sq := SquarefreePartFactorizationNat q_nat
    rcases q_nat_sq with ⟨ k, l_nat, h_nat⟩
    use k/b
    rw [q_frac]
    field_simp
    let h_fact := h_nat.1
    by_cases h_sign : a > 0
    · use l_nat
      constructor
      · have q_pos : 0 ≤ q_int := by positivity
        have q_abs : q_nat = q_int := by
          exact Int.natAbs_of_nonneg q_pos
        rw [← q_abs]
        exact_mod_cast h_fact
      · rw [← Int.squarefree_natAbs]
        exact_mod_cast h_nat.2
    · use -l_nat
      constructor
      · apply le_of_not_lt at h_sign
        have q_pos : q_int ≤ 0 := by
          rw [← neg_nonneg]
          have dumbing_it_down : -q_int = (-a)*b := by ring
          rw [← neg_nonneg] at h_sign
          rw [dumbing_it_down]
          positivity
        have q_abs : q_nat = -q_int := by
          exact Int.ofNat_natAbs_of_nonpos q_pos
        have q_nabs : q_int = -q_nat := by
          rw [q_abs]
          ring
        rw [q_nabs]
        simp
        exact_mod_cast h_fact
      · rw [← Int.squarefree_natAbs]
        rw [Int.natAbs_neg]
        exact_mod_cast h_nat.2

#print axioms SquarefreePartFactorizationRat