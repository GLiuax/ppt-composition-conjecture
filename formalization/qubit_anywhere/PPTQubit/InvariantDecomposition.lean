import PPTQubit.GramDecomposition
import PPTQubit.PPTPairing
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem psd_gram_factor {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (hQ : Q.PosSemidef) :
    ∃ C : Matrix n n ℂ, C.conjTranspose * C = Q := by
  let hH := hQ.isHermitian
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let d : n → ℂ := fun i => (hH.eigenvalues i : ℂ)
  let f : n → ℂ := fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)
  let F := Matrix.diagonal f
  have hQd : Q = U * Matrix.diagonal d * U.conjTranspose := by
    simpa only [U, d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_apply] using hH.spectral_theorem
  have hF : F.conjTranspose = F := by
    simp [F, f]
  have hFF : F * F = Matrix.diagonal d := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    dsimp [f, d]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hQ.eigenvalues_nonneg i)]
  refine ⟨F * U.conjTranspose, ?_⟩
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hF]
  calc
    _ = U * (F * F) * U.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [hFF, ← hQd]


def partialTraceFirst {p m : Type*} [Fintype p]
    (Q : Matrix (p × m) (p × m) ℂ) : Matrix m m ℂ :=
  fun a b => ∑ i, Q (i, a) (i, b)

theorem gram_cross_of_partialTranspose_invariant {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ)
    (hpt : partialTransposeFirst ((gramBlockRow C).conjTranspose * gramBlockRow C) =
      (gramBlockRow C).conjTranspose * gramBlockRow C) :
    ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i := by
  intro i j
  ext a b
  exact (congrFun (congrFun hpt (i, a)) (j, b)).symm

theorem partialTraceFirst_gram {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ) :
    partialTraceFirst ((gramBlockRow C).conjTranspose * gramBlockRow C) =
      ∑ i, (C i).conjTranspose * C i := by
  ext a b
  simp only [partialTraceFirst, Matrix.sum_apply]
  rfl

/-- The positive-marginal operator form of the real-hyperplane expansion.
Zero summands are permitted because the square Gram factor is redundant. -/
theorem pt_invariant_real_hyperplane_expansion {p m : ℕ}
    (Q : Matrix (Fin (p + 2) × Fin m) (Fin (p + 2) × Fin m) ℂ)
    (hQ : Q.PosSemidef)
    (hpt : partialTransposeFirst Q = Q)
    (hmarg : (partialTraceFirst Q).PosDef) :
    ∃ (psi : Fin ((p + 2) * m) → Fin (p + 2) × Fin m → ℂ)
      (alpha : Fin ((p + 2) * m) → Fin (p + 2) → ℝ),
      (∀ i j, Q i j = ∑ s, psi s i * star (psi s j)) ∧
      (∀ s, alpha s ≠ 0 ∧
        ∀ a, ∑ i, (alpha s i : ℂ) * psi s (i, a) = 0) := by
  obtain ⟨S, hS⟩ := psd_gram_factor Q hQ
  let e : Fin ((p + 2) * m) ≃ Fin (p + 2) × Fin m := finProdFinEquiv.symm
  let F := S.submatrix e id
  let C : Fin (p + 2) → Matrix (Fin ((p + 2) * m)) (Fin m) ℂ :=
    fun i s a => F s (i, a)
  have hF : F.conjTranspose * F = Q := by
    dsimp only [F]
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hS]
    rfl
  have hgram : (gramBlockRow C).conjTranspose * gramBlockRow C = Q := hF
  have hc : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i := by
    apply gram_cross_of_partialTranspose_invariant C
    rw [hgram]
    exact hpt
  have hp : (∑ i, (C i).conjTranspose * C i).PosDef := by
    rw [← partialTraceFirst_gram C, hgram]
    exact hmarg
  obtain ⟨psi, alpha, hsum, hrel⟩ := real_hyperplane_expansion C hp hc
  refine ⟨psi, alpha, ?_, hrel⟩
  simpa only [hgram] using hsum

end PPTQubit
#print axioms PPTQubit.psd_gram_factor
#print axioms PPTQubit.gram_cross_of_partialTranspose_invariant
#print axioms PPTQubit.partialTraceFirst_gram
#print axioms PPTQubit.pt_invariant_real_hyperplane_expansion
