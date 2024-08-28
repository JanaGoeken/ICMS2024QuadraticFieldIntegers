import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Degree.Definitions


open FiniteDimensional Polynomial IntermediateField
--Theorem which states that every rational fieldextension of rank 2 is isomorphic to Q adjoint squareroot 2.
theorem PrimitiveElementsOfDimTwo {K : Type*}[Field K][Algebra ℚ K] -- Anne: we could replace this with any extension `K / L` which is separable
    (h : finrank ℚ K = 2) : -- Anne: this can become `0 < finrank ℚ K`
    ∃ (α : K),  ∃ _: K ≃+* ℚ⟮α⟯, true := by -- Anne: More commonly phrased as: `∃ α, Nonempty (K ≃+* ℚ⟮α⟯)`, and maybe replace the ring equiv with an algebra equiv.
  have : FiniteDimensional ℚ K := by exact Module.finite_of_finrank_eq_succ h
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  use α
  refine ⟨?_, rfl⟩
  let φ := (IntermediateField.topEquiv (F := ℚ) (E := K)).symm
  rw [hα] -- Anne: Nicer to use `IntermediateField.equivOfEq`.
  apply φ.toRingEquiv

--Theorem which states that for an extension field K of Q of rank 2, for an α in K, not in Q, the minimal polynomial
--for which α is a root is of degree 2.
theorem MinpolyDegreeIsTwo {K : Type u_3} [Field K] [Algebra ℚ K] (α : K)
    (h_2 : α ∉ (algebraMap ℚ K).range) (h : finrank ℚ K = 2) [FiniteDimensional ℚ K] :
    (minpoly ℚ α ).degree = 2 := by
  convert le_antisymm (minpoly.degree_le α) _
  · rw [h]
    norm_cast
  · assumption
  · rw[h, degree_eq_natDegree]
    norm_cast
    rw[minpoly.two_le_natDegree_iff]
    assumption
    exact Algebra.IsIntegral.isIntegral α
    exact minpoly.ne_zero_of_finite ℚ α

--A normcast lemma
-- Anne: generalize to any field extension (of characteristic 0?)
@[norm_cast]
lemma discrim_coe {K : Type u_3} [Field K] [Algebra ℚ K] (a b c : ℚ) :
    ↑(discrim a b c) = discrim (a: K) (b : K) (c : K) := by
  have h_charzero: CharZero K := algebraRat.charZero K
  unfold discrim
  norm_cast


/--theorem eraseLead_natDegree_lt [Semiring R] (f : Polynomial R) (f0 : 1 < f.natDegree) :
(eraseLead f).natDegree < f.natDegree :=
lt_of_le_of_ne eraseLead_natDegree_le_aux <| sorry

start with:
theorem eraseLead_degree_lt [Semiring R] (f : Polynomial R) (f0 : f ≠ 0) :
(eraseLead f).degree < f.degree :=
sorry

there also is theorem Polynomial.eq_X_add_C_of_degree_le_one, I should use that-/

--general form of a polynomial of degree at most two
-- Anne: Maybe we should have some induction principle here?
-- Of the form `p.degree ≤ n -> ∃ q, q.degree < n ∧ p = C (p.coeff n) * X ^ n + q`
-- then this can be three applications of that principle plus some rewriting.
 theorem Polynomial.exists_eq_X_sq_add_X_add_C_of_degree_le_two_2 [Semiring R] (p : Polynomial R)
    {n : ℕ} (h : p.degree ≤ n) :
     ∃ q, q.degree < (n : WithBot ℕ) ∧ p = C (p.coeff n) * X ^ n + q := by
     by_cases hp : p=0
     · rw[hp]                               --case p=0
       use 0
       simp only [degree_zero, coeff_zero, map_zero, zero_mul, add_zero, and_true]
       exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
     · by_cases hn : n = p.natDegree
       · refine ⟨p.erase n, ?_, ?_⟩           -- case p ≠ 0, n = p.degree
         · rw [hn, ←Polynomial.degree_eq_natDegree]
           apply degree_erase_lt hp
           exact hp
         · rw [Polynomial.X_pow_eq_monomial]
           simp only [C_mul_monomial, mul_one]
           apply Eq.symm (monomial_add_erase p n)
       · rw [← @Ne.eq_def, @ne_comm] at hn
         have hnlt : p.degree < ↑n := by
           rw [lt_iff_le_and_ne]
           refine ⟨h, ?_ ⟩
           apply degree_ne_of_natDegree_ne hn
         refine ⟨ p, hnlt, ?_ ⟩                -- case p ≠ 0, n = p.degree
         · have hcoeff : p.coeff n = 0 := by
             apply coeff_eq_zero_of_degree_lt
             exact hnlt
           rw [hcoeff]
           simp only [map_zero, zero_mul, zero_add]


 theorem Polynomial.exists_eq_X_sq_add_X_add_C_of_degree_le_two_2advanced [Semiring R] (p : Polynomial R)
    {n : ℕ} (h : p.degree ≤ n) :
     ∃ q, q.degree < (n : WithBot ℕ) ∧ p = C (p.coeff n) * X ^ n + q ∧ p.coeff (n - 1) = q.coeff (n - 1):= by
     by_cases hp : p=0
     · rw[hp]                               --case p=0
       use 0
       simp only [degree_zero, coeff_zero, map_zero, zero_mul, add_zero, and_true]
       exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
     · by_cases hn : n = p.natDegree
       · refine ⟨p.erase n, ?_, ?_⟩           -- case p ≠ 0, n = p.degree
         · rw [hn, ←Polynomial.degree_eq_natDegree]
           apply degree_erase_lt hp
           exact hp
         · have heq : p = C (p.coeff n) * X ^ n + erase n p := by
             rw [Polynomial.X_pow_eq_monomial]
             simp only [C_mul_monomial, mul_one]
             apply Eq.symm (monomial_add_erase p n)
           constructor
           · apply heq
           · rw[hn]
             nth_rewrite 1 [←monomial_add_erase p n]
             rw[hn]
             have lslsl : ((monomial p.natDegree) (p.coeff p.natDegree)).coeff (p.natDegree - 1) = 0 := by
               --rw [←coeff_zero (n := p.natDegree - 1)]
               rw [@coeff_monomial]
               rw [←hn]
               sorry
               have noShitSherlock : (n = n - 1) = false := by sorry
             rw[coeff_add, lslsl, zero_add]
       · rw [← @Ne.eq_def, @ne_comm] at hn
         have hnlt : p.degree < ↑n := by
           rw [lt_iff_le_and_ne]
           refine ⟨h, ?_ ⟩
           apply degree_ne_of_natDegree_ne hn
         refine ⟨ p, hnlt, ?_ ⟩                -- case p ≠ 0, n = p.degree
         · have hcoeff : p.coeff n = 0 := by
             apply coeff_eq_zero_of_degree_lt
             exact hnlt
           constructor
           · rw [hcoeff]
             simp only [map_zero, zero_mul, zero_add]
           · rfl
     done
--------------------------------------------test---------------------------------------------------------

---alternative theorem:
 --Pros:
 ------more information about the decomposition
 ------more fitting with the library
 ------shorter proof
 --Cons:
 ------not compatible for our project since it does not cover the cases when p is constant, especially 0
 ------less flexible in the choice of n and q
 theorem Polynomial.exists_eq_X_sq_add_X_add_C_of_degree_le_two_2_suggestion_1 [Semiring R] (p : Polynomial R)
     ( f0 : 2 ≤ Finset.card (Polynomial.support p)):
     ∃ q, q.natDegree < p.natDegree ∧  p = monomial p.natDegree p.leadingCoeff + q := by
     refine ⟨ p.eraseLead, ?_, ?_ ⟩
     · apply eraseLead_natDegree_lt f0
     · rw[add_comm]
       apply Eq.symm (eraseLead_add_monomial_natDegree_leadingCoeff p)
-------------------------------------------------test end ------------------------------------------------------------

theorem Polynomial.eq_X_sq_add_X_add_C_of_degree_le_two [Semiring R] {p : Polynomial R}
    (h : p.degree ≤ 2) :
    p = C (p.coeff 2) * X^2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  ext i
  match i with
  | 0
  | 1
  | 2 => simp
  | i + 3 =>
    simp
    apply coeff_eq_zero_of_natDegree_lt
    by_cases w : p.degree = ⊥
    · simp_all
    · simp_all [degree_eq_natDegree]
      omega

-- Replacement for `Polynomial.eq_X_sq_add_X_add_C_of_degree_le_two'`
theorem Polynomial.eq_X_sq_add_X_add_C_of_degree_le_two' [Semiring R] {p : Polynomial R}
    (h : p.degree ≤ 2) :
    p = C (p.coeff 2) * X^2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  obtain ⟨q, hdegq, p_eq ⟩ := Polynomial.exists_eq_X_sq_add_X_add_C_of_degree_le_two_2 p (n:=2) h
  obtain ⟨r, hdegr, q_eq⟩ := Polynomial.exists_eq_X_sq_add_X_add_C_of_degree_le_two_2 q (n:=1) (SuccOrder.le_of_lt_succ hdegq)
  obtain ⟨lezero, hzero, r_eq⟩ := Polynomial.exists_eq_X_sq_add_X_add_C_of_degree_le_two_2 r (n:=0) (SuccOrder.le_of_lt_succ hdegr)
  rw [lt_iff_not_le] at hzero
  norm_cast at hzero
  rw [zero_le_degree_iff, not_not] at hzero
  nth_rewrite 1 [p_eq, q_eq, r_eq, hzero]
  simp
  rw[add_assoc]

  theorem Polynomial.eq_X_sq_add_X_add_C_of_degree_le_two'h [Semiring R] {p : Polynomial R}
    (h : p.degree ≤ 2) :
    p = C (p.coeff 2) * X^2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  obtain ⟨q, hdegq, p_eq ⟩ := Polynomial.exists_eq_X_sq_add_X_add_C_of_degree_le_two_2 p (n:=2) h
  obtain ⟨r, hdegr, q_eq⟩ := Polynomial.exists_eq_X_sq_add_X_add_C_of_degree_le_two_2 q (n:=1) (SuccOrder.le_of_lt_succ hdegq)
  have q_coeff : q.coeff 1 = p.coeff 1 := by sorry
  have r_coeff : r = C (p.coeff 0) := by sorry
  nth_rewrite 1 [p_eq, q_eq, q_coeff, r_coeff]
  simp
  rw[add_assoc]



--Final theorem, showing that every element of the extension field K can be written in the form p+q*r where p,q are rationals
-- and r is squareroot of some squarefree natural number.
theorem Ednawashere3 {K : Type*}[Field K][Algebra ℚ K] (h : finrank ℚ K = 2) (α : K)
    (h_2 : α ∉ (algebraMap ℚ K).range): ∃  (p q s : ℚ)
    (r : K), α = p + q * r ∧ r^2 = s ∧ q ≠ 0 := by
  let h_charzero: CharZero K := algebraRat.charZero K
  let h_finite : FiniteDimensional ℚ K := Module.finite_of_finrank_eq_succ h
  let h_deg : (minpoly ℚ α ).degree = 2 := by
    apply MinpolyDegreeIsTwo α _ h
    assumption
  let minpoly_eq := Polynomial.eq_X_sq_add_X_add_C_of_degree_le_two h_deg.le
  set a := (minpoly ℚ α ).coeff 2
  set b := (minpoly ℚ α ).coeff 1
  set c := (minpoly ℚ α ).coeff 0
  have proofabc : a * α ^ 2 + b * α + c = 0 := by
    rw[← minpoly.aeval (A := ℚ) (x := α), minpoly_eq]
    simp only [map_add, map_mul, aeval_C, eq_ratCast, map_pow, aeval_X]
  set s := discrim a b c with s_def
  have hdiscrim : discrim ↑a ↑b ↑c = (2 * ↑a * α + ↑b) ^ 2 := by
    push_cast
    refine discrim_eq_sq_of_quadratic_eq_zero (a := (a : K)) (b := (b : K)) (c := (c : K)) (x := α) ?_
    convert proofabc using 1
    ring
  set r := 2 * a * α + b with r_def
  have h_rs : r^2 = ↑s := by
    rw[s_def]
    push_cast
    apply hdiscrim.symm
  by_cases ha : a = 0
  · by_cases hb : (b : K) = 0
    · exfalso
      rw[ha, hb] at proofabc
      simp at proofabc
      norm_cast at hb
      rw[ha, hb, proofabc] at minpoly_eq
      simp at minpoly_eq
      apply minpoly.ne_zero (A := ℚ) (x := α) _ minpoly_eq
      exact Algebra.IsIntegral.isIntegral α
    have hb' : b ≠ 0 := by exact_mod_cast hb
    rw[ha] at proofabc r_def
    simp at proofabc r_def
    set p := 0 with p_def
    set q := - c / (b ^ 2) with q_def
    have h_q : q ≠ 0 := by
      intro hq
      rw[hq] at q_def
      rw[eq_comm, _root_.div_eq_zero_iff] at q_def
      obtain (hc | hb) := q_def
      · rw [neg_eq_zero] at hc
        simp only [hc, Rat.cast_zero, add_zero, mul_eq_zero, Rat.cast_eq_zero, hb', false_or] at proofabc
        simp only [proofabc, RingHom.mem_range, eq_ratCast, Rat.cast_eq_zero, exists_eq, not_true_eq_false] at h_2
      · simp [hb'] at hb
    use p, q, s, r
    constructor
    · rw[p_def, q_def, r_def]
      push_cast
      simp only [zero_add]
      field_simp
      linear_combination ↑b * proofabc
    · constructor
      · exact h_rs
      · assumption
  · have h_roots : α = (-b + r) / (2 * a) ∨ α = (-b -r) / (2 * a) := by
      apply (quadratic_eq_zero_iff _ _ α).1
      · convert proofabc using 3
        ring
      · norm_cast
      · norm_cast
        rw[← s_def]
        convert h_rs.symm
        ring
    cases h_roots
    case neg.inl hroot =>
      set p := -b / (2 * a) with p_def
      set q := 1/(2 * a) with q_def ---Achtung plus oder Minus
      use p, q, s, r
      constructor
      · rw[p_def, q_def, r_def]
        have : (a : K) ≠ 0 := by exact_mod_cast ha
        field_simp
        ring
      · constructor
        · assumption
        · rw[q_def]
          simp
          assumption
    case neg.inr hroot =>
      set p := -b / (2 * a) with p_def
      set q := 1/(2 * a) with q_def ---Achtung plus oder Minus
      use p, q, s, r
      constructor
      · rw[p_def, q_def, r_def]
        have : (a : K) ≠ 0 := by exact_mod_cast ha
        field_simp
        ring
      · constructor
        · assumption
        · rw[q_def]
          simp
          assumption


#print axioms Ednawashere3
