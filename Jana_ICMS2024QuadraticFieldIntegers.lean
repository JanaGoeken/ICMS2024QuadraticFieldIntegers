import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.PrimitiveElement

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
