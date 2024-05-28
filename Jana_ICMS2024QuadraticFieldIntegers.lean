import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Data.Real.Basic

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
    choose α φ using PrimitiveElementsOfDImTwo h
    have : FiniteDimensional ℚ K := by exact Module.finite_of_finrank_eq_succ h
    have h_deg : (minpoly ℚ α ).degree ≤ 2 := by apply MinpolyDegreeAtMostTwo α h
    have h_poly : ∃ (a b c : ℚ), a * α^2 + b * α + c = 0 := by sorry
    choose a b c using h_poly
    let s := b^2 - 4
    have h_roots : α = (-b + r) / (2 * a) ∨ α = (-b -r) / (2 * a) := by sorry
    use α
    let p := -b / (2 * a)
    --let q := +- 1/(2 * a)
    sorry
