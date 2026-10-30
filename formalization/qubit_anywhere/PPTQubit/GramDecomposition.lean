import PPTQubit.HermitianExtension
import PPTQubit.RealCombination

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem gram_unit_of_injective {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℂ)
    (hinj : Function.Injective A.mulVec) :
    IsUnit (A.conjTranspose * A).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  have hk : (A.conjTranspose * A).mulVecLin.ker = ⊥ := by
    rw [Matrix.ker_mulVecLin_conjTranspose_mul_self]
    exact LinearMap.ker_eq_bot.mpr hinj
  have hlin := LinearMap.ker_eq_bot.mp hk
  exact hlin

theorem full_rank_hermitian_extensions {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i) :
    ∃ u : Fin p → ℝ, Function.Injective (realCombination C u).mulVec ∧
      ∀ v : Fin p → ℝ, ∃ K : Matrix (Fin r) (Fin r) ℂ,
        K.IsHermitian ∧ K * realCombination C u = realCombination C v := by
  obtain ⟨u, hu⟩ := full_rank_real_combination C hpos hcross
  refine ⟨u, hu, ?_⟩
  intro v
  apply explicit_hermitian_extension _ _ (gram_unit_of_injective _ hu)
  change ((realCombination C u).conjTranspose * realCombination C v).conjTranspose = _
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  exact (real_combinations_cross C hcross u v).symm

theorem full_rank_two_columns_hermitian_extensions {p r : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin 2) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i) :
    ∃ u : Fin p → ℝ, Function.Injective (realCombination C u).mulVec ∧
      ∀ v : Fin p → ℝ, ∃ K : Matrix (Fin r) (Fin r) ℂ,
        K.IsHermitian ∧ K * realCombination C u = realCombination C v :=
  full_rank_hermitian_extensions C hpos hcross

theorem combination_adjoint_mulVec {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ) (u : Fin p → ℝ)
    (x : Fin r → ℂ) (a : Fin m) :
    (realCombination C u).conjTranspose.mulVec x a =
      ∑ i, (u i : ℂ) * (C i).conjTranspose.mulVec x a := by
  simp only [realCombination, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

def gramBlockRow {p r m : ℕ} (C : Fin p → Matrix (Fin r) (Fin m) ℂ) :
    Matrix (Fin r) (Fin p × Fin m) ℂ := fun s a => C a.1 s a.2

theorem full_rank_spectral_decomposition {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i)
    (hfull : ∃ u : Fin p → ℝ, Function.Injective (realCombination C u).mulVec) :
    ∃ u : Fin p → ℝ, Function.Injective (realCombination C u).mulVec ∧
      ∀ v : Fin p → ℝ,
        ∃ (psi : Fin r → Fin p × Fin m → ℂ) (ell : Fin r → ℝ),
          (∀ i j, ((gramBlockRow C).conjTranspose * gramBlockRow C) i j =
              ∑ s, psi s i * star (psi s j)) ∧
          (∀ s a, (∑ i, (v i : ℂ) * psi s (i, a)) =
            (ell s : ℂ) * ∑ i, (u i : ℂ) * psi s (i, a)) ∧
          (Function.Injective (gramBlockRow C).conjTranspose.mulVec →
            ∀ s, psi s ≠ 0) := by
  obtain ⟨u, hu⟩ := hfull
  refine ⟨u, hu, ?_⟩
  intro v
  have hc : ((realCombination C u).conjTranspose * realCombination C v).IsHermitian := by
    change ((realCombination C u).conjTranspose * realCombination C v).conjTranspose = _
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact (real_combinations_cross C hcross u v).symm
  obtain ⟨K, hK, hKD, hEig⟩ :=
    gram_eigenbasis_relation (realCombination C u) (realCombination C v)
      (gram_unit_of_injective _ hu) hc
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


theorem exists_real_nonparallel {p : ℕ} (u : Fin (p + 2) → ℝ) :
    ∃ v : Fin (p + 2) → ℝ, ∀ t : ℝ, v ≠ t • u := by
  classical
  by_cases hu : u 0 = 0
  · refine ⟨Pi.single 0 1, ?_⟩
    intro t heq
    have h := congrFun heq (0 : Fin (p + 2))
    simp [hu] at h
  · refine ⟨Pi.single 1 1, ?_⟩
    intro t heq
    have h0 := congrFun heq (0 : Fin (p + 2))
    have ht : t = 0 := by
      simp at h0
      exact h0.resolve_right hu
    have h1 := congrFun heq (1 : Fin (p + 2))
    simp [ht] at h1

theorem real_hyperplane_decomposition_of_full_rank {p r m : ℕ}
    (C : Fin (p + 2) → Matrix (Fin r) (Fin m) ℂ)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i)
    (hrow : Function.Injective (gramBlockRow C).conjTranspose.mulVec)
    (hfull : ∃ u : Fin (p + 2) → ℝ, Function.Injective (realCombination C u).mulVec) :
    ∃ (psi : Fin r → Fin (p + 2) × Fin m → ℂ)
      (alpha : Fin r → Fin (p + 2) → ℝ),
      (∀ i j, ((gramBlockRow C).conjTranspose * gramBlockRow C) i j =
        ∑ s, psi s i * star (psi s j)) ∧
      (∀ s, psi s ≠ 0 ∧ alpha s ≠ 0 ∧
        ∀ a, ∑ i, (alpha s i : ℂ) * psi s (i, a) = 0) := by
  obtain ⟨u, hu, hdecomp⟩ := full_rank_spectral_decomposition C hcross hfull
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

theorem real_hyperplane_decomposition {p r m : ℕ}
    (C : Fin (p + 2) → Matrix (Fin r) (Fin m) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i)
    (hrow : Function.Injective (gramBlockRow C).conjTranspose.mulVec) :
    ∃ (psi : Fin r → Fin (p + 2) × Fin m → ℂ)
      (alpha : Fin r → Fin (p + 2) → ℝ),
      (∀ i j, ((gramBlockRow C).conjTranspose * gramBlockRow C) i j =
        ∑ s, psi s i * star (psi s j)) ∧
      (∀ s, psi s ≠ 0 ∧ alpha s ≠ 0 ∧
        ∀ a, ∑ i, (alpha s i : ℂ) * psi s (i, a) = 0) :=
  real_hyperplane_decomposition_of_full_rank C hcross hrow
    (full_rank_real_combination C hpos hcross)

/-- A redundant Gram factor may give zero summands. The real annihilators
remain nonzero without any row-rank assumption. -/
theorem real_hyperplane_expansion {p r m : ℕ}
    (C : Fin (p + 2) → Matrix (Fin r) (Fin m) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i) :
    ∃ (psi : Fin r → Fin (p + 2) × Fin m → ℂ)
      (alpha : Fin r → Fin (p + 2) → ℝ),
      (∀ i j, ((gramBlockRow C).conjTranspose * gramBlockRow C) i j =
        ∑ s, psi s i * star (psi s j)) ∧
      (∀ s, alpha s ≠ 0 ∧
        ∀ a, ∑ i, (alpha s i : ℂ) * psi s (i, a) = 0) := by
  obtain ⟨u, _, hdecomp⟩ := full_rank_spectral_decomposition C hcross
    (full_rank_real_combination C hpos hcross)
  obtain ⟨v, hv⟩ := exists_real_nonparallel u
  obtain ⟨psi, ell, hsum, hrel, _⟩ := hdecomp v
  refine ⟨psi, fun s => v - ell s • u, hsum, ?_⟩
  intro s
  constructor
  · intro ha
    exact hv (ell s) (sub_eq_zero.mp ha)
  · intro a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sub,
      Complex.ofReal_mul, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
    exact sub_eq_zero.mpr (hrel s a)

theorem two_column_real_hyperplane_decomposition {p r : ℕ}
    (C : Fin (p + 2) → Matrix (Fin r) (Fin 2) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i)
    (hrow : Function.Injective (gramBlockRow C).conjTranspose.mulVec) :
    ∃ (psi : Fin r → Fin (p + 2) × Fin 2 → ℂ)
      (alpha : Fin r → Fin (p + 2) → ℝ),
      (∀ i j, ((gramBlockRow C).conjTranspose * gramBlockRow C) i j =
        ∑ s, psi s i * star (psi s j)) ∧
      (∀ s, psi s ≠ 0 ∧ alpha s ≠ 0 ∧
        ∀ a, ∑ i, (alpha s i : ℂ) * psi s (i, a) = 0) :=
  real_hyperplane_decomposition C hpos hcross hrow

theorem real_hyperplane_decomposition_of_rank_from_minors {p r m : ℕ}
    (C : Fin (p + 2) → Matrix (Fin r) (Fin m) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i)
    (hrow : Function.Injective (gramBlockRow C).conjTranspose.mulVec)
    (hminors : ∀ (M : Matrix (Fin r) (Fin m) ℂ) (k : ℕ),
      (∀ (rows : Fin (k + 1) → Fin r) (cols : Fin (k + 1) → Fin m),
        (M.submatrix rows cols).det = 0) → M.rank ≤ k) :
    ∃ (psi : Fin r → Fin (p + 2) × Fin m → ℂ)
      (alpha : Fin r → Fin (p + 2) → ℝ),
      (∀ i j, ((gramBlockRow C).conjTranspose * gramBlockRow C) i j =
        ∑ s, psi s i * star (psi s j)) ∧
      (∀ s, psi s ≠ 0 ∧ alpha s ≠ 0 ∧
        ∀ a, ∑ i, (alpha s i : ℂ) * psi s (i, a) = 0) :=
  real_hyperplane_decomposition_of_full_rank C hcross hrow
    (full_rank_of_rank_from_minors C hpos hcross hminors)

end PPTQubit
#print axioms PPTQubit.gram_unit_of_injective
#print axioms PPTQubit.full_rank_two_columns_hermitian_extensions
#print axioms PPTQubit.full_rank_hermitian_extensions
#print axioms PPTQubit.combination_adjoint_mulVec
#print axioms PPTQubit.full_rank_spectral_decomposition
#print axioms PPTQubit.exists_real_nonparallel
#print axioms PPTQubit.real_hyperplane_decomposition_of_full_rank
#print axioms PPTQubit.two_column_real_hyperplane_decomposition
#print axioms PPTQubit.real_hyperplane_decomposition_of_rank_from_minors
#print axioms PPTQubit.real_hyperplane_decomposition
#print axioms PPTQubit.real_hyperplane_expansion
