import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Degree.Definitions


open FiniteDimensional Polynomial IntermediateField

theorem PrimitiveElementsOfDImTwo {K : Type*}[Field K][Algebra ℚ K](h : finrank ℚ K = 2) :
    ∃ (α : K),  ∃ φ: K ≃+* ℚ⟮α⟯, true := by
  have : FiniteDimensional ℚ K := by exact Module.finite_of_finrank_eq_succ h
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  use α
  refine ⟨?_, rfl⟩
  let φ := (IntermediateField.topEquiv (F := ℚ) (E := K)).symm
  rw [hα]
  apply φ.toRingEquiv

theorem MinpolyDegreeAtMostTwo {K : Type u_3} [Field K] [Algebra ℚ K] (α : K) (h : finrank ℚ K = 2)
[FiniteDimensional ℚ K] : (minpoly ℚ α ).degree ≤ 2 := by
  convert minpoly.degree_le α
  · rw [h]
    norm_cast
  · assumption

@[norm_cast]
lemma discrim_coe {K : Type u_3} [Field K] [Algebra ℚ K] (a b c : ℚ) :
    ↑(discrim a b c) = discrim (a: K) (b : K) (c : K) := by
  have h_charzero: CharZero K := algebraRat.charZero K
  unfold discrim
  norm_cast

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


theorem Ednawashere2 {K : Type*}[Field K][Algebra ℚ K](h : finrank ℚ K = 2) :
  ∃ (α : K) (p q s : ℚ) (r : K), α = p + q * r ∧ r^2 = s := by
  have h_charzero: CharZero K := algebraRat.charZero K
  choose α φ _ using PrimitiveElementsOfDImTwo h
  have h_finite : FiniteDimensional ℚ K := by exact Module.finite_of_finrank_eq_succ h
  have h_deg : (minpoly ℚ α ).degree ≤ 2 := by apply MinpolyDegreeAtMostTwo α h
  have minpoly_eq := Polynomial.eq_X_sq_add_X_add_C_of_degree_le_two h_deg
  set a := (minpoly ℚ α ).coeff 2
  set b := (minpoly ℚ α ).coeff 1
  set c := (minpoly ℚ α ).coeff 0
  have proofabc : a * α ^ 2 + b * α + c = 0 := by
    rw[← minpoly.aeval (A := ℚ) (x := α)]
    rw[minpoly_eq]
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
    · rw[ha] at proofabc r_def
      simp at proofabc r_def
      set p := 0 with p_def
      set q := - c / (b ^ 2) with q_def
      use α, p, q, s, r
      constructor
      · rw[p_def, q_def, r_def]
        push_cast
        simp only [zero_add]
        field_simp
        linear_combination ↑b * proofabc
      · exact h_rs
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
      use α, p, q, s, r
      constructor
      · rw[p_def, q_def, r_def]
        have : (a : K) ≠ 0 := by exact_mod_cast ha
        field_simp
        ring
      · assumption
    case neg.inr hroot =>
      set p := -b / (2 * a) with p_def
      set q := 1/(2 * a) with q_def ---Achtung plus oder Minus
      use α, p, q, s, r
      constructor
      · rw[p_def, q_def, r_def]
        have : (a : K) ≠ 0 := by exact_mod_cast ha
        field_simp
        ring
      · assumption

theorem Ednawashere3 {K : Type*}[Field K][Algebra ℚ K](h : finrank ℚ K = 2) (α : K) :
  ∃  (p q s : ℚ) (r : K), α = p + q * r ∧ r^2 = s := by
  have h_charzero: CharZero K := algebraRat.charZero K
  have h_finite : FiniteDimensional ℚ K := by exact Module.finite_of_finrank_eq_succ h
  have h_deg : (minpoly ℚ α ).degree ≤ 2 := by apply MinpolyDegreeAtMostTwo α h
  have minpoly_eq := Polynomial.eq_X_sq_add_X_add_C_of_degree_le_two h_deg
  set a := (minpoly ℚ α ).coeff 2
  set b := (minpoly ℚ α ).coeff 1
  set c := (minpoly ℚ α ).coeff 0
  have proofabc : a * α ^ 2 + b * α + c = 0 := by
    rw[← minpoly.aeval (A := ℚ) (x := α)]
    rw[minpoly_eq]
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
    · rw[ha] at proofabc r_def
      simp at proofabc r_def
      set p := 0 with p_def
      set q := - c / (b ^ 2) with q_def
      use p, q, s, r
      constructor
      · rw[p_def, q_def, r_def]
        push_cast
        simp only [zero_add]
        field_simp
        linear_combination ↑b * proofabc
      · exact h_rs
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
      · assumption
    case neg.inr hroot =>
      set p := -b / (2 * a) with p_def
      set q := 1/(2 * a) with q_def ---Achtung plus oder Minus
      use p, q, s, r
      constructor
      · rw[p_def, q_def, r_def]
        have : (a : K) ≠ 0 := by exact_mod_cast ha
        field_simp
        ring
      · assumption

#print axioms Ednawashere2
#print axioms Ednawashere3


/-
theorem isombetweenthethinkswewanthehe {K : Type*}[Field K][Algebra ℚ K](h : finrank ℚ K = 2) :
  ∃ (α : K) (p q s : ℚ) (r : K), α = p + q * r ∧ r^2 = s := by
-/
