import PPTQubit.SecondOperations
/-! Qubit reduction, Pauli components, and the PPT row-contraction inequality. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def qubitBlock {n : ℕ} (Q : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ)
    (i j : Fin 2) : Matrix (Fin n) (Fin n) ℂ := Q.submatrix (fun a => (i,a)) (fun b => (j,b))

def qubitComponents {n : ℕ} (Q : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ) :
    Fin 3 → Matrix (Fin n) (Fin n) ℂ :=
  ![qubitBlock Q 0 1 + qubitBlock Q 1 0,
    Complex.I • (qubitBlock Q 1 0 - qubitBlock Q 0 1),
    qubitBlock Q 0 0 - qubitBlock Q 1 1]

theorem qubitBlock_conjTranspose {n : ℕ} (Q : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ)
    (hQ : Q.IsHermitian) (i j : Fin 2) : (qubitBlock Q i j).conjTranspose = qubitBlock Q j i := by
  ext a b
  exact congrFun (congrFun hQ.eq (j,a)) (i,b)

theorem qubitComponents_hermitian {n : ℕ} (Q : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ)
    (hQ : Q.IsHermitian) : ∀ k, (qubitComponents Q k).IsHermitian := by
  intro k
  fin_cases k
  · change (qubitBlock Q 0 1 + qubitBlock Q 1 0).conjTranspose = _
    rw [Matrix.conjTranspose_add,qubitBlock_conjTranspose Q hQ,qubitBlock_conjTranspose Q hQ]
    exact add_comm _ _
  · change (Complex.I • (qubitBlock Q 1 0 - qubitBlock Q 0 1)).conjTranspose = Complex.I • (qubitBlock Q 1 0 - qubitBlock Q 0 1)
    rw [Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,
      qubitBlock_conjTranspose Q hQ,qubitBlock_conjTranspose Q hQ]
    ext a b
    simp [Matrix.smul_apply,Matrix.sub_apply]
    ring
  · change (qubitBlock Q 0 0 - qubitBlock Q 1 1).conjTranspose = _
    rw [Matrix.conjTranspose_sub,qubitBlock_conjTranspose Q hQ,qubitBlock_conjTranspose Q hQ]
    rfl

theorem qubit_reduction_identity {n : ℕ} (Q : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ) :
    localCongruence (!![0,-1;1,0] : Matrix (Fin 2) (Fin 2) ℂ) (partialTransposeFirst Q) =
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (partialTraceFirst Q) - Q := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases j <;>
    simp [localCongruence_entry,Fin.sum_univ_two,partialTransposeFirst,partialTraceFirst,
      Matrix.kronecker,Matrix.kroneckerMap_apply]

theorem qubit_normalized_contraction {n : ℕ}
    (Q : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ) (hQ : IsPPT Q)
    (hM : partialTraceFirst Q = 1) : (1-Q).PosSemidef := by
  have h := hQ.2.mul_mul_conjTranspose_same
    (localLift (!![0,-1;1,0] : Matrix (Fin 2) (Fin 2) ℂ) (n := n))
  change (localCongruence _ (partialTransposeFirst Q)).PosSemidef at h
  rw [qubit_reduction_identity,hM] at h
  simpa only [Matrix.kronecker,Matrix.one_kronecker_one] using h

theorem qubit_square_marginal {n : ℕ}
    (Q : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ) :
    partialTraceFirst (Q*Q) = qubitBlock Q 0 0 * qubitBlock Q 0 0 +
      qubitBlock Q 0 1 * qubitBlock Q 1 0 +
      qubitBlock Q 1 0 * qubitBlock Q 0 1 + qubitBlock Q 1 1 * qubitBlock Q 1 1 := by
  ext a b
  simp only [partialTraceFirst,Fin.sum_univ_two,Matrix.mul_apply,Fintype.sum_prod_type,
    qubitBlock,Matrix.submatrix_apply,Matrix.add_apply]
  ring

theorem qubitComponents_squares {n : ℕ}
    (Q : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ) :
    ∑ k, qubitComponents Q k * qubitComponents Q k =
      (2 : ℂ) • partialTraceFirst (Q*Q) - partialTraceFirst Q * partialTraceFirst Q := by
  have hm : partialTraceFirst Q = qubitBlock Q 0 0 + qubitBlock Q 1 1 := by
    ext a b; simp [partialTraceFirst,qubitBlock,Fin.sum_univ_two]
  rw [Fin.sum_univ_three,qubit_square_marginal,hm]
  change (qubitBlock Q 0 1 + qubitBlock Q 1 0) * (qubitBlock Q 0 1 + qubitBlock Q 1 0) +
    (Complex.I • (qubitBlock Q 1 0 - qubitBlock Q 0 1)) *
      (Complex.I • (qubitBlock Q 1 0 - qubitBlock Q 0 1)) +
    (qubitBlock Q 0 0 - qubitBlock Q 1 1) * (qubitBlock Q 0 0 - qubitBlock Q 1 1) = _
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Complex.I_mul_I,neg_one_smul,two_smul]
  noncomm_ring

theorem qubitComponents_row_contraction {n : ℕ}
    (Q : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ) (hQ : IsPPT Q)
    (hM : partialTraceFirst Q = 1) :
    (1 - ∑ k, qubitComponents Q k * qubitComponents Q k).PosSemidef := by
  have h := (partialTraceFirst_positive _
    (positive_contraction_sub_square Q hQ.1 (qubit_normalized_contraction Q hQ hM))).smul
    (show (0 : ℂ) ≤ 2 by exact Complex.nonneg_iff.mpr ⟨by norm_num,rfl⟩)
  have heq : 1 - ∑ k, qubitComponents Q k * qubitComponents Q k =
      (2 : ℂ) • partialTraceFirst (Q-Q*Q) := by
    rw [qubitComponents_squares,hM,Matrix.one_mul]
    have ht : partialTraceFirst (Q-Q*Q) = 1 - partialTraceFirst (Q*Q) := by
      rw [← hM]
      ext a b
      simp [partialTraceFirst,Finset.sum_sub_distrib]
    rw [ht]
    module
  rw [heq]
  exact h
end PPTQubit
#print axioms PPTQubit.qubitComponents_row_contraction
