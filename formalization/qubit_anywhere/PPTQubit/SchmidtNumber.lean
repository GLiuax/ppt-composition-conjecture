import PPTQubit.SchmidtRank
/-! The least product-decomposition bound agrees with the usual Schmidt number. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem schmidtBoundExists {a b : ℕ} (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hQ : Q.PosSemidef) : ∃ k : ℕ, SchmidtNumberAtMost k Q :=
  ⟨a,positive_schmidt_bound_reference Q hQ⟩

def schmidtNumber {a b : ℕ} (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hQ : Q.PosSemidef) : ℕ := by
  classical
  exact Nat.find (schmidtBoundExists Q hQ)

theorem schmidtNumber_spec {a b : ℕ} (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hQ : Q.PosSemidef) : SchmidtNumberAtMost (schmidtNumber Q hQ) Q := by
  classical
  exact Nat.find_spec (schmidtBoundExists Q hQ)

theorem schmidtNumber_le_iff {a b k : ℕ}
    (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hQ : Q.PosSemidef) :
    schmidtNumber Q hQ ≤ k ↔ SchmidtNumberAtMost k Q := by
  classical
  constructor
  · exact fun hk => schmidt_number_mono Q (schmidtNumber_spec Q hQ) hk
  · intro hk
    exact Nat.find_min' (schmidtBoundExists Q hQ) hk

theorem schmidtNumber_le_one_iff_separable {a b : ℕ}
    (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hQ : Q.PosSemidef) :
    schmidtNumber Q hQ ≤ 1 ↔ IsSeparable Q := by
  rw [schmidtNumber_le_iff,schmidt_one_iff_separable]

theorem schmidtNumber_zero {a b : ℕ} :
    schmidtNumber (0 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) Matrix.PosSemidef.zero = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (schmidtNumber_le_iff _ _).mpr
  refine ⟨0,fun x => Fin.elim0 x,?_,?_⟩
  · simp
  · intro t
    exact Fin.elim0 t
end PPTQubit
#print axioms PPTQubit.schmidtNumber_le_iff
#print axioms PPTQubit.schmidtNumber_le_one_iff_separable
