import PPTQubit.SecondOperations
/-! Support normalization of arbitrary qubit PPT operators, including singular marginals. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem partialTraceFirst_add {p n : ℕ}
    (Q R : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    partialTraceFirst (Q+R) = partialTraceFirst Q + partialTraceFirst R := by
  ext a b
  simp [partialTraceFirst,Finset.sum_add_distrib]

theorem partialTraceFirst_smul {p n : ℕ}
    (Q : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) (t : ℂ) :
    partialTraceFirst (t • Q) = t • partialTraceFirst Q := by
  ext a b
  simp [partialTraceFirst,Finset.mul_sum]

theorem partialTraceFirst_qubit_identity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    partialTraceFirst (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) A) = (2 : ℂ) • A := by
  ext a b
  simp [partialTraceFirst,Matrix.kronecker,two_mul]

theorem qubit_identity_tensor_ppt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) : IsPPT (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) A) := by
  have h := tensor_positive (1 : Matrix (Fin 2) (Fin 2) ℂ) A Matrix.PosSemidef.one hA
  refine ⟨h,?_⟩
  have heq : partialTransposeFirst (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) A) =
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) A := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp [partialTransposeFirst,Matrix.kronecker,Matrix.one_apply,eq_comm]
  rw [heq]
  exact h

/-- Normalization on the support, with a harmless depolarizing completion on its kernel.
The restoration identity includes the zero marginal and every singular case. -/
theorem qubit_ppt_normalization {n : ℕ}
    (Q : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ) (hQ : IsPPT Q) :
    ∃ (B : Matrix (Fin n) (Fin n) ℂ)
      (R : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ),
      IsPPT R ∧ partialTraceFirst R = 1 ∧ secondCongruence B R = Q := by
  obtain ⟨B,J,P,hB,hJ,hP,hBB,hBJ,hJB,hPP,hMP,hJMJ,hBP,hK⟩ :=
    positive_support_square_roots (partialTraceFirst Q) (partialTraceFirst_positive Q hQ.1)
  let H := (1/2 : ℂ) • Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (1-P)
  have hhalf : (0 : ℂ) ≤ 1/2 := Complex.nonneg_iff.mpr ⟨by norm_num,by norm_num⟩
  have hH : IsPPT H := by
    have h := qubit_identity_tensor_ppt (1-P) hK
    refine ⟨h.1.smul hhalf,?_⟩
    dsimp only [H]
    rw [partialTransposeFirst_smul]
    exact h.2.smul hhalf
  let R := secondCongruence J Q + H
  refine ⟨B,R,?_,?_,?_⟩
  · have h := secondCongruence_ppt J Q hQ
    refine ⟨h.1.add hH.1,?_⟩
    change (partialTransposeFirst (secondCongruence J Q + H)).PosSemidef
    rw [partialTransposeFirst_add]
    exact h.2.add hH.2
  · dsimp only [R,H]
    rw [partialTraceFirst_add,partialTraceFirst_secondCongruence,hJ.eq,hJMJ,
      partialTraceFirst_smul,partialTraceFirst_qubit_identity]
    module
  · dsimp only [R]
    rw [secondCongruence_add,secondCongruence_comp,hBJ,secondCongruence_support Q hQ.1 P hP hMP]
    have hh : secondCongruence B H = 0 := by
      dsimp only [H]
      rw [secondCongruence_smul,secondCongruence_tensor,hB.eq]
      have hz : B * (1-P) * B = 0 := by
        rw [Matrix.mul_sub,Matrix.mul_one,hBP,sub_self,Matrix.zero_mul]
      rw [hz]
      ext i j
      simp [Matrix.kronecker]
    rw [hh,add_zero]
end PPTQubit
#print axioms PPTQubit.qubit_ppt_normalization
