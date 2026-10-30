import PPTQubit.SingularSupport
/-! Real-hyperplane Gram decomposition without a marginal-invertibility hypothesis. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem singular_spectral_decomposition {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i) :
    ∃ u : Fin p → ℝ,
      ∀ v : Fin p → ℝ,
        ∃ (psi : Fin r → Fin p × Fin m → ℂ) (ell : Fin r → ℝ),
          (∀ i j, ((gramBlockRow C).conjTranspose * gramBlockRow C) i j =
              ∑ s, psi s i * star (psi s j)) ∧
          (∀ s a, (∑ i, (v i : ℂ) * psi s (i, a)) =
            (ell s : ℂ) * ∑ i, (u i : ℂ) * psi s (i, a)) ∧
          (Function.Injective (gramBlockRow C).conjTranspose.mulVec →
            ∀ s, psi s ≠ 0) := by
  obtain ⟨u, hmax⟩ := maximal_real_combination C
  have hcommon (x : Fin m → ℂ) (hx : (realCombination C u).mulVec x = 0) (i : Fin p) :
      (C i).mulVec x = 0 := by
    have hc : (realCombination C u).conjTranspose * C i =
        (C i).conjTranspose * realCombination C u := by
      simpa only [realCombination_single] using
        real_combinations_cross C hcross u (Pi.single i 1)
    apply kernel_inclusion_of_complex_pencil_rank (realCombination C u) (C i) hc _ x hx
    apply rank_le_of_minors_zero
    intro rows cols
    exact maximal_real_pencil_large_minors_zero C u hmax i (Nat.lt_succ_self _)
      rows cols Complex.I
  refine ⟨u, ?_⟩
  intro v
  have hker : ∀ x, (realCombination C u).mulVec x = 0 →
      (realCombination C v).mulVec x = 0 := by
    intro x hx
    simp only [realCombination, Matrix.sum_mulVec, Matrix.smul_mulVec, hcommon x hx,
      smul_zero, Finset.sum_const_zero]
  have hc : ((realCombination C u).conjTranspose * realCombination C v).IsHermitian := by
    change ((realCombination C u).conjTranspose * realCombination C v).conjTranspose = _
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact (real_combinations_cross C hcross u v).symm
  obtain ⟨K, hK, hKD⟩ :=
    singular_hermitian_extension (realCombination C u) (realCombination C v) hc hker
  have hEig (j : Fin r) :
      (realCombination C v).conjTranspose.mulVec (hK.eigenvectorBasis j).ofLp =
        (hK.eigenvalues j : ℂ) •
          (realCombination C u).conjTranspose.mulVec (hK.eigenvectorBasis j).ofLp := by
    apply real_eigenvalue_annihilator K (realCombination C u) (realCombination C v)
      _ (hK.eigenvalues j) hK hKD
    simpa only [RCLike.real_smul_eq_coe_smul] using hK.mulVec_eigenvectorBasis j
  let F := gramBlockRow C
  let U : Matrix (Fin r) (Fin r) ℂ := hK.eigenvectorUnitary
  let psi : Fin r → Fin p × Fin m → ℂ := fun s a => (F.conjTranspose * U) a s
  let ell : Fin r → ℝ := hK.eigenvalues
  have hU : U * U.conjTranspose = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hK.eigenvectorUnitary
  refine ⟨psi, ell, ?_, ?_, ?_⟩
  · intro i j
    exact congrFun (congrFun (gram_rank_one_expansion F U hU) i) j
  · intro s a
    have h := congrFun (hEig s) a
    simp only [Pi.smul_apply, smul_eq_mul, combination_adjoint_mulVec] at h
    change (∑ i, (v i : ℂ) * psi s (i, a)) =
      (ell s : ℂ) * ∑ i, (u i : ℂ) * psi s (i, a)
    simpa [psi, F, gramBlockRow, U, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      hK.eigenvectorUnitary_apply] using h
  · intro hinj s hzero
    have hxne : (hK.eigenvectorBasis s).ofLp ≠ 0 := by
      intro hz
      have hz' : hK.eigenvectorBasis s = 0 := by
        apply WithLp.ofLp_injective 2
        simpa using hz
      exact (hK.eigenvectorBasis.toBasis.ne_zero s) hz'
    have hpsi : F.conjTranspose.mulVec (hK.eigenvectorBasis s).ofLp = psi s := by
      ext i
      simp [psi, U, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    apply hxne
    apply hinj
    change F.conjTranspose.mulVec (hK.eigenvectorBasis s).ofLp =
      F.conjTranspose.mulVec 0
    rw [hpsi, hzero, Matrix.mulVec_zero]


theorem singular_real_hyperplane_decomposition {p r m : ℕ}
    (C : Fin (p + 2) → Matrix (Fin r) (Fin m) ℂ)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i)
    (hrow : Function.Injective (gramBlockRow C).conjTranspose.mulVec) :
    ∃ (psi : Fin r → Fin (p + 2) × Fin m → ℂ)
      (alpha : Fin r → Fin (p + 2) → ℝ),
      (∀ i j, ((gramBlockRow C).conjTranspose * gramBlockRow C) i j =
        ∑ s, psi s i * star (psi s j)) ∧
      (∀ s, psi s ≠ 0 ∧ alpha s ≠ 0 ∧
        ∀ a, ∑ i, (alpha s i : ℂ) * psi s (i, a) = 0) := by
  obtain ⟨u, hdecomp⟩ := singular_spectral_decomposition C hcross
  obtain ⟨v, hv⟩ := exists_real_nonparallel u
  obtain ⟨psi, ell, hsum, hrel, hnonzero⟩ := hdecomp v
  refine ⟨psi, fun s => v - ell s • u, hsum, ?_⟩
  intro s
  refine ⟨hnonzero hrow s, ?_, ?_⟩
  · intro ha
    exact hv (ell s) (sub_eq_zero.mp ha)
  · intro a
    have h := hrel s a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sub,
      Complex.ofReal_mul, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
    exact sub_eq_zero.mpr h

end PPTQubit
#print axioms PPTQubit.singular_spectral_decomposition
#print axioms PPTQubit.singular_real_hyperplane_decomposition
