import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.QuadraticDiscriminant

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

theorem Ednawashere {K : Type*}[Field K][Algebra ℚ K](h : finrank ℚ K = 2) :
    ∃ (α : K) (p q s : ℚ) (r : K), α = p + q * r ∧ r^2 = s := by
    have : CharZero K := algebraRat.charZero K
    choose α φ _ using PrimitiveElementsOfDImTwo h
    have : FiniteDimensional ℚ K := by exact Module.finite_of_finrank_eq_succ h
    have h_deg : (minpoly ℚ α ).degree ≤ 2 := by apply MinpolyDegreeAtMostTwo α h
    have h_poly : ∃ (a b c : ℚ), a * α^2 + b * α + c = 0 := by sorry
    choose a b c proofabc using h_poly
    let s := discrim a b c
    have : s = discrim (a : K) (b : K) (c : K) :=
      show ↑(discrim a b c) = discrim (a : K) (b : K) (c : K) by
        unfold discrim
        norm_cast
    have : s = (2 * a * α + b) ^ 2 := by
      rw [this]
      refine discrim_eq_sq_of_quadratic_eq_zero (a := (a : K)) (b := (b : K)) (c := (c : K)) (x := α) ?_
      convert proofabc using 1
      ring
    let r := 2 * a * α + b
    have h_roots : α = (-b + r) / (2 * a) ∨ α = (-b -r) / (2 * a) := by sorry
    use α
    let p := -b / (2 * a)
    let q := 1/(2 * a) ---Achtung plus oder Minus
    use p, q, s, r
    constructor
    · sorry
    · show (2 * ↑a * α + ↑b)^2 = ↑(discrim a b c)
      aesop
