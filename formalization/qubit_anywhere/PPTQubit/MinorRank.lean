import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Rank and square minors for finite matrices over any field. -/

open Matrix
noncomputable section
namespace PPTQubit

variable {K : Type*} [Field K]

theorem submatrix_rank_le {r m n : ℕ}
    (A : Matrix (Fin r) (Fin m) K)
    (rows : Fin n → Fin r) (cols : Fin n → Fin m) :
    (A.submatrix rows cols).rank ≤ A.rank := by
  let M := A.submatrix rows id
  have hr : M.rank ≤ A.rank :=
    Matrix.rank_submatrix_le rows (Equiv.refl (Fin m)) A
  have hc := Matrix.rank_submatrix_le cols (Equiv.refl (Fin n)) M.transpose
  change (M.transpose.submatrix cols id).rank ≤ M.transpose.rank at hc
  have heq : (A.submatrix rows cols).transpose =
      M.transpose.submatrix cols id := by
    ext i j
    rfl
  rw [← heq, Matrix.rank_transpose, Matrix.rank_transpose] at hc
  exact le_trans hc hr

theorem large_minor_det_zero {r m n : ℕ}
    (A : Matrix (Fin r) (Fin m) K)
    (rows : Fin n → Fin r) (cols : Fin n → Fin m)
    (h : A.rank < n) : (A.submatrix rows cols).det = 0 := by
  by_contra hdet
  have hunit : IsUnit (A.submatrix rows cols) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hrank := Matrix.rank_of_isUnit (A.submatrix rows cols) hunit
  rw [Fintype.card_fin] at hrank
  have hle := submatrix_rank_le A rows cols
  omega

theorem exists_independent_columns {r m n : ℕ}
    (A : Matrix (Fin r) (Fin m) K) (hn : n ≤ A.rank) :
    ∃ c : Fin n → Fin m, LinearIndependent K (A.col ∘ c) := by
  classical
  obtain ⟨κ, c, hc, hspan, hind⟩ := exists_linearIndependent' K A.col
  letI : Fintype κ := Fintype.ofInjective c hc
  have hcard : Fintype.card κ = A.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hind]
  have hn' : n ≤ Fintype.card κ := by simpa only [hcard] using hn
  let a : Fin n → κ := (Fintype.equivFin κ).symm ∘ Fin.castLE hn'
  refine ⟨c ∘ a, ?_⟩
  have ha : Function.Injective a :=
    (Fintype.equivFin κ).symm.injective.comp (Fin.castLE_injective hn')
  exact hind.comp a ha

theorem exists_nonzero_minor_of_le_rank {r m n : ℕ}
    (A : Matrix (Fin r) (Fin m) K) (hn : n ≤ A.rank) :
    ∃ (rows : Fin n → Fin r) (cols : Fin n → Fin m),
      (A.submatrix rows cols).det ≠ 0 := by
  classical
  obtain ⟨cols, hcols⟩ := exists_independent_columns A hn
  let B : Matrix (Fin r) (Fin n) K := A.submatrix id cols
  have hB : LinearIndependent K B.col := hcols
  have hBrank : B.rank = n := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hB, Fintype.card_fin]
  have ht : n ≤ B.transpose.rank := by rw [Matrix.rank_transpose, hBrank]
  obtain ⟨rows, hrows⟩ := exists_independent_columns B.transpose ht
  refine ⟨rows, cols, ?_⟩
  have hrow : LinearIndependent K (A.submatrix rows cols).row := hrows
  have hunit : IsUnit (A.submatrix rows cols) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hrow
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

theorem rank_le_of_minors_zero {r m : ℕ}
    (A : Matrix (Fin r) (Fin m) K) (k : ℕ)
    (h : ∀ (rows : Fin (k + 1) → Fin r) (cols : Fin (k + 1) → Fin m),
      (A.submatrix rows cols).det = 0) : A.rank ≤ k := by
  by_contra hn
  have hlt : k + 1 ≤ A.rank := by omega
  obtain ⟨rows, cols, hdet⟩ := exists_nonzero_minor_of_le_rank A hlt
  exact hdet (h rows cols)

theorem le_rank_iff_exists_nonzero_minor {r m n : ℕ}
    (A : Matrix (Fin r) (Fin m) K) :
    n ≤ A.rank ↔ ∃ (rows : Fin n → Fin r) (cols : Fin n → Fin m),
      (A.submatrix rows cols).det ≠ 0 := by
  constructor
  · exact exists_nonzero_minor_of_le_rank A
  · rintro ⟨rows, cols, hdet⟩
    by_contra hn
    exact hdet (large_minor_det_zero A rows cols (by omega))

theorem rank_le_iff_minors_zero {r m : ℕ}
    (A : Matrix (Fin r) (Fin m) K) (k : ℕ) :
    A.rank ≤ k ↔
      ∀ (rows : Fin (k + 1) → Fin r) (cols : Fin (k + 1) → Fin m),
        (A.submatrix rows cols).det = 0 := by
  constructor
  · intro hk rows cols
    exact large_minor_det_zero A rows cols (by omega)
  · exact rank_le_of_minors_zero A k

end PPTQubit
#print axioms PPTQubit.exists_independent_columns
#print axioms PPTQubit.exists_nonzero_minor_of_le_rank
#print axioms PPTQubit.rank_le_of_minors_zero

#print axioms PPTQubit.le_rank_iff_exists_nonzero_minor
#print axioms PPTQubit.rank_le_iff_minors_zero
