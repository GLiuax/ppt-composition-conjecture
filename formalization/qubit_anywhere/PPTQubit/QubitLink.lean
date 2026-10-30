import PPTQubit.QubitRowContraction
import PPTQubit.RowContraction
import PPTQubit.QubitNormalization
/-! Separable link products for arbitrary PPT operators meeting at a qubit. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def qubitLink {a b : ℕ} (R : Matrix (Fin 2 × Fin a) (Fin 2 × Fin a) ℂ)
    (S : Matrix (Fin 2 × Fin b) (Fin 2 × Fin b) ℂ) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  ∑ i, ∑ j, Matrix.kronecker (qubitBlock R i j) (qubitBlock S i j)

def qubitLinkComponents {b : ℕ} (S : Matrix (Fin 2 × Fin b) (Fin 2 × Fin b) ℂ) :
    Fin 3 → Matrix (Fin b) (Fin b) ℂ :=
  ![qubitComponents S 0, -qubitComponents S 1, qubitComponents S 2]

theorem qubitLink_pauli {a b : ℕ} (R : Matrix (Fin 2 × Fin a) (Fin 2 × Fin a) ℂ)
    (S : Matrix (Fin 2 × Fin b) (Fin 2 × Fin b) ℂ) :
    qubitLink R S = (1/2 : ℂ) •
      (Matrix.kronecker (partialTraceFirst R) (partialTraceFirst S) +
        ∑ k, Matrix.kronecker (qubitComponents R k) (qubitLinkComponents S k)) := by
  ext ⟨i,c⟩ ⟨j,d⟩
  simp only [qubitLink,qubitLinkComponents,qubitComponents,Fin.sum_univ_three,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.sum_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.neg_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.kronecker,Matrix.kroneckerMap_apply,partialTraceFirst,
    qubitBlock,Matrix.submatrix_apply]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem qubitLink_normalized_separable {a b : ℕ}
    (R : Matrix (Fin 2 × Fin a) (Fin 2 × Fin a) ℂ)
    (S : Matrix (Fin 2 × Fin b) (Fin 2 × Fin b) ℂ)
    (hR : IsPPT R) (hS : IsPPT S)
    (hMR : partialTraceFirst R = 1) (hMS : partialTraceFirst S = 1) :
    IsSeparable (qubitLink R S) := by
  have hY : ∀ k, (qubitLinkComponents S k).IsHermitian := by
    intro k
    fin_cases k
    · exact qubitComponents_hermitian S hS.1.isHermitian 0
    · change (-qubitComponents S 1).IsHermitian
      exact (qubitComponents_hermitian S hS.1.isHermitian 1).neg
    · exact qubitComponents_hermitian S hS.1.isHermitian 2
  have hYY : (1 - ∑ k, qubitLinkComponents S k * qubitLinkComponents S k).PosSemidef := by
    have h := qubitComponents_row_contraction S hS hMS
    simpa only [qubitLinkComponents,Fin.sum_univ_three,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,neg_mul_neg] using h
  have h := hermitian_row_contraction_separable (qubitComponents R) (qubitLinkComponents S)
    (qubitComponents_hermitian R hR.1.isHermitian) hY
    (qubitComponents_row_contraction R hR hMR) hYY
  rw [qubitLink_pauli,hMR,hMS]
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
    separable_nonneg_smul _ h (1/2) (by norm_num)

theorem localCongruence_add {p q n : ℕ} (U : Matrix (Fin q) (Fin p) ℂ)
    (Q R : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    localCongruence U (Q+R) = localCongruence U Q + localCongruence U R := by
  simp only [localCongruence,Matrix.mul_add,Matrix.add_mul]

theorem localCongruence_tensor {p q n : ℕ} (U : Matrix (Fin q) (Fin p) ℂ)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    localCongruence U (Matrix.kronecker A B) =
      Matrix.kronecker (U*A*U.conjTranspose) B := by
  simp only [localCongruence,localLift,Matrix.kronecker,Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one,← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]

theorem qubitLink_first_congruence {a b : ℕ} (U : Matrix (Fin a) (Fin a) ℂ)
    (R : Matrix (Fin 2 × Fin a) (Fin 2 × Fin a) ℂ)
    (S : Matrix (Fin 2 × Fin b) (Fin 2 × Fin b) ℂ) :
    qubitLink (secondCongruence U R) S = localCongruence U (qubitLink R S) := by
  simp only [qubitLink,Fin.sum_univ_two,localCongruence_add,localCongruence_tensor,
    qubitBlock,secondCongruence_block]

theorem qubitLink_second_congruence {a b : ℕ} (V : Matrix (Fin b) (Fin b) ℂ)
    (R : Matrix (Fin 2 × Fin a) (Fin 2 × Fin a) ℂ)
    (S : Matrix (Fin 2 × Fin b) (Fin 2 × Fin b) ℂ) :
    qubitLink R (secondCongruence V S) = secondCongruence V (qubitLink R S) := by
  simp only [qubitLink,Fin.sum_univ_two,secondCongruence_add,secondCongruence_tensor,
    qubitBlock,secondCongruence_block]

/-- Two arbitrary PPT links sharing a qubit have a separable link product. -/
theorem qubitLink_ppt_separable {a b : ℕ}
    (R : Matrix (Fin 2 × Fin a) (Fin 2 × Fin a) ℂ)
    (S : Matrix (Fin 2 × Fin b) (Fin 2 × Fin b) ℂ)
    (hR : IsPPT R) (hS : IsPPT S) : IsSeparable (qubitLink R S) := by
  obtain ⟨B,R',hR',hMR',hBR⟩ := qubit_ppt_normalization R hR
  obtain ⟨C,S',hS',hMS',hCS⟩ := qubit_ppt_normalization S hS
  rw [← hBR,← hCS,qubitLink_first_congruence,qubitLink_second_congruence]
  exact localCongruence_separable B _ (secondCongruence_separable C _
    (qubitLink_normalized_separable R' S' hR' hS' hMR' hMS'))

end PPTQubit
#print axioms PPTQubit.qubitLink_ppt_separable
