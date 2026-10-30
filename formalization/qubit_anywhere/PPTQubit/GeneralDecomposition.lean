import PPTQubit.SingularDecomposition
import PPTQubit.MinimalGram

/-! The general real-hyperplane decomposition, with exactly rank Q nonzero terms. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

/-- No assumption on the marginal rank. If Q is zero the indexing type is empty. -/
theorem pt_invariant_real_hyperplane_decomposition {p m : ℕ}
    (Q : Matrix (Fin (p + 2) × Fin m) (Fin (p + 2) × Fin m) ℂ)
    (hQ : Q.PosSemidef) (hpt : partialTransposeFirst Q = Q) :
    ∃ (psi : Fin Q.rank → Fin (p + 2) × Fin m → ℂ)
      (alpha : Fin Q.rank → Fin (p + 2) → ℝ),
      (∀ i j, Q i j = ∑ s, psi s i * star (psi s j)) ∧
      (∀ s, psi s ≠ 0 ∧ alpha s ≠ 0 ∧
        ∀ a, ∑ i, (alpha s i : ℂ) * psi s (i, a) = 0) := by
  obtain ⟨r, F, hF, hinj, hr⟩ := psd_minimal_gram_factor Q hQ
  subst r
  let C : Fin (p + 2) → Matrix (Fin Q.rank) (Fin m) ℂ :=
    fun i s a => F s (i, a)
  have hgram : (gramBlockRow C).conjTranspose * gramBlockRow C = Q := hF
  have hc : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i := by
    apply gram_cross_of_partialTranspose_invariant C
    rw [hgram]
    exact hpt
  obtain ⟨psi, alpha, hsum, hrel⟩ := singular_real_hyperplane_decomposition C hc hinj
  refine ⟨psi, alpha, ?_, hrel⟩
  simpa only [hgram] using hsum

/-- Every finite rank-one expansion has at least rank Q summands. -/
theorem rank_le_number_of_rank_one_terms {n : Type*} [Fintype n]
    (Q : Matrix n n ℂ) (r : ℕ) (psi : Fin r → n → ℂ)
    (hsum : ∀ i j, Q i j = ∑ s, psi s i * star (psi s j)) : Q.rank ≤ r := by
  classical
  let C : Matrix (Fin r) n ℂ := fun s i => star (psi s i)
  have hC : C.conjTranspose * C = Q := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, C, star_star]
    exact (hsum i j).symm
  rw [← hC, Matrix.rank_conjTranspose_mul_self]
  simpa only [Fintype.card_fin] using Matrix.rank_le_card_height C

end PPTQubit
#print axioms PPTQubit.pt_invariant_real_hyperplane_decomposition

#print axioms PPTQubit.rank_le_number_of_rank_one_terms
