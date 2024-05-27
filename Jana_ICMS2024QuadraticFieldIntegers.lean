import Mathlib.NumberTheory.NumberField.Basic

theorem PrimitiveElementsOfDImTwo {K : Type*}[Field K][Algebra ℚ K](h : findim ℚ K = 2) : ∃ (α : K), K ≅ Q⟮α⟯
