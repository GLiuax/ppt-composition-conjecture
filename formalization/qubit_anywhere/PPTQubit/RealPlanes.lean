import PPTQubit.GeneralDecomposition
/-! Explicit real two-dimensional qutrit subspaces associated with nonzero real annihilators. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem real_qutrit_plane_factor {n : ℕ} (psi : Fin 3 × Fin n → ℂ)
    (alpha : Fin 3 → ℝ) (ha : alpha ≠ 0)
    (hrel : ∀ a, ∑ i, (alpha i : ℂ) * psi (i,a) = 0) :
    ∃ (U : Matrix (Fin 3) (Fin 2) ℝ) (C : Matrix (Fin 2) (Fin n) ℂ),
      Function.Injective U.mulVec ∧
      ∀ i a, psi (i,a) = ∑ t, (U i t : ℂ) * C t a := by
  by_cases h0 : alpha 0 = 0
  · by_cases h1 : alpha 1 = 0
    · have h2 : alpha 2 ≠ 0 := by
        intro h2
        apply ha
        funext i
        fin_cases i <;> assumption
      have hz (a : Fin n) : psi (2,a) = 0 := by
        have h := hrel a
        simp only [Fin.sum_univ_three, h0, h1, Complex.ofReal_zero, zero_mul, zero_add] at h
        exact (mul_eq_zero.mp h).resolve_left (Complex.ofReal_ne_zero.mpr h2)
      refine ⟨!![1,0;0,1;0,0], fun t a => ![psi (0,a), psi (1,a)] t, ?_, ?_⟩
      · intro x y h
        funext t
        fin_cases t
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h (0 : Fin 3)
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h (1 : Fin 3)
      · intro i a
        fin_cases i <;> simp [Fin.sum_univ_two, hz]
    · have hn : (alpha 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1
      have hz (a : Fin n) : psi (1,a) = ((-alpha 2 / alpha 1 : ℝ) : ℂ) * psi (2,a) := by
        have h := hrel a
        simp only [Fin.sum_univ_three, h0, Complex.ofReal_zero, zero_mul, zero_add] at h
        rw [Complex.ofReal_div, Complex.ofReal_neg, div_mul_eq_mul_div]
        apply (eq_div_iff hn).mpr
        linear_combination h
      refine ⟨!![1,0;0,-alpha 2 / alpha 1;0,1],
        fun t a => ![psi (0,a), psi (2,a)] t, ?_, ?_⟩
      · intro x y h
        funext t
        fin_cases t
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h (0 : Fin 3)
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h (2 : Fin 3)
      · intro i a
        fin_cases i <;> simp [Fin.sum_univ_two, hz]
  · have hn : (alpha 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
    have hz (a : Fin n) : psi (0,a) =
        ((-alpha 1 / alpha 0 : ℝ) : ℂ) * psi (1,a) +
        ((-alpha 2 / alpha 0 : ℝ) : ℂ) * psi (2,a) := by
      have h := hrel a
      simp only [Fin.sum_univ_three] at h
      simp only [Complex.ofReal_div, Complex.ofReal_neg, div_mul_eq_mul_div]
      rw [← add_div]
      apply (eq_div_iff hn).mpr
      linear_combination h
    refine ⟨!![-alpha 1 / alpha 0,-alpha 2 / alpha 0;1,0;0,1],
      fun t a => ![psi (1,a), psi (2,a)] t, ?_, ?_⟩
    · intro x y h
      funext t
      fin_cases t
      · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h (1 : Fin 3)
      · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h (2 : Fin 3)
    · intro i a
      fin_cases i <;> simp [Fin.sum_univ_two, hz]
end PPTQubit
#print axioms PPTQubit.real_qutrit_plane_factor
