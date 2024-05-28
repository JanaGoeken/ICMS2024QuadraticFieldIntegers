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

#check (2 : ℝ)
theorem MinpolyDegreeAtMostTwo {K : Type u_3} [Field K] [Algebra ℚ K] (α : K) (h : finrank ℚ K = 2)
[FiniteDimensional ℚ K] : (minpoly ℚ α ).degree ≤ 2 := by
  convert minpoly.degree_le α
  · rw [h]
    norm_cast
  · assumption
