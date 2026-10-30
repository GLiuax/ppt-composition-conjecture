import PPTQubit.SupportSquareRoots
import PPTQubit.SupportCompression
import PPTQubit.SeparableTensor
/-! Filtering the second subsystem and lossless restoration from marginal support. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def secondCongruence {p n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ := fun i j =>
  (U * Q.submatrix (fun a => (i.1,a)) (fun b => (j.1,b)) * U.conjTranspose) i.2 j.2

theorem secondCongruence_swap {p n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    secondCongruence U Q = swapFactors (localCongruence U (swapFactors Q)) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change (U * Q.submatrix (fun a => (i,a)) (fun b => (j,b)) * U.conjTranspose) a b =
    localCongruence U (swapFactors Q) (a,i) (b,j)
  simp only [localCongruence_entry,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Finset.sum_mul,Matrix.submatrix_apply,swapFactors,Prod.swap_prod_mk]
  rw [Finset.sum_comm]

theorem secondCongruence_ppt {p n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) (hQ : IsPPT Q) :
    IsPPT (secondCongruence U Q) := by
  rw [secondCongruence_swap]
  exact swapFactors_ppt _ (localCongruence_ppt U _ (swapFactors_ppt Q hQ))

theorem secondCongruence_separable {p n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) (hQ : IsSeparable Q) :
    IsSeparable (secondCongruence U Q) := by
  rw [secondCongruence_swap]
  exact swapFactors_separable _ (localCongruence_separable U _ (swapFactors_separable Q hQ))

theorem secondCongruence_block {p n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) (i j : Fin p) :
    (secondCongruence U Q).submatrix (fun a => (i,a)) (fun b => (j,b)) =
      U * Q.submatrix (fun a => (i,a)) (fun b => (j,b)) * U.conjTranspose := rfl

theorem secondCongruence_comp {p n : ℕ} (U V : Matrix (Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    secondCongruence U (secondCongruence V Q) = secondCongruence (U*V) Q := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change (U * (secondCongruence V Q).submatrix (fun a => (i,a)) (fun b => (j,b)) * U.conjTranspose) a b = _
  rw [secondCongruence_block]
  simp only [secondCongruence,Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem partialTraceFirst_sum_blocks {p n : ℕ}
    (Q : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    partialTraceFirst Q = ∑ i, Q.submatrix (fun a => (i,a)) (fun b => (i,b)) := by
  ext a b
  simp only [partialTraceFirst,Matrix.sum_apply,Matrix.submatrix_apply]

theorem partialTraceFirst_positive {p n : ℕ}
    (Q : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) (hQ : Q.PosSemidef) :
    (partialTraceFirst Q).PosSemidef := by
  rw [partialTraceFirst_sum_blocks]
  apply Finset.sum_induction
  · intro A B hA hB; exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro i _; exact hQ.submatrix _

theorem partialTraceFirst_secondCongruence {p n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    partialTraceFirst (secondCongruence U Q) = U * partialTraceFirst Q * U.conjTranspose := by
  simp only [partialTraceFirst_sum_blocks,secondCongruence_block,Matrix.mul_sum,Matrix.sum_mul]

theorem secondCongruence_add {p n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (Q R : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    secondCongruence U (Q+R) = secondCongruence U Q + secondCongruence U R := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [secondCongruence,Matrix.submatrix_add,Pi.add_apply,Matrix.mul_add,Matrix.add_mul,Matrix.add_apply]

theorem secondCongruence_smul {p n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) (t : ℂ) :
    secondCongruence U (t • Q) = t • secondCongruence U Q := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [secondCongruence,Matrix.submatrix_smul,Pi.smul_apply,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_apply]

theorem secondCongruence_tensor {p n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    secondCongruence U (Matrix.kronecker A B) = Matrix.kronecker A (U*B*U.conjTranspose) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  have hb : (Matrix.kronecker A B).submatrix (fun c => (i,c)) (fun d => (j,d)) = A i j • B := by
    ext c d; rfl
  change (U * (Matrix.kronecker A B).submatrix (fun c => (i,c)) (fun d => (j,d)) * U.conjTranspose) a b = _
  rw [hb,Matrix.mul_smul,Matrix.smul_mul]
  rfl

theorem secondCongruence_support {p n : ℕ}
    (Q : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) (hQ : Q.PosSemidef)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian)
    (hMP : partialTraceFirst Q * P = partialTraceFirst Q) : secondCongruence P Q = Q := by
  obtain ⟨r,F,hF,_,_⟩ := psd_minimal_gram_factor Q hQ
  let C : Fin p → Matrix (Fin r) (Fin n) ℂ := fun i s a => F s (i,a)
  have hgram : (gramBlockRow C).conjTranspose * gramBlockRow C = Q := hF
  have hm : partialTraceFirst Q = ∑ i, (C i).conjTranspose * C i := by
    rw [← hgram,partialTraceFirst_gram]
  have hs : ∀ i, C i * P = C i := by
    intro i
    have hz : partialTraceFirst Q * (1-P) = 0 := by
      rw [Matrix.mul_sub,Matrix.mul_one,hMP,sub_self]
    have hc : C i * (1-P) = 0 := by
      ext s a
      have hx : (∑ j, (C j).conjTranspose * C j).mulVec ((1-P).col a) = 0 := by
        rw [← hm]
        funext b
        exact congrFun (congrFun hz b) a
      exact congrFun (marginal_kernel_is_common C _ hx i) s
    rw [Matrix.mul_sub,Matrix.mul_one,sub_eq_zero] at hc
    exact hc.symm
  have hb (i j : Fin p) : Q.submatrix (fun a => (i,a)) (fun b => (j,b)) = (C i).conjTranspose * C j := by
    ext a b
    exact (congrFun (congrFun hgram (i,a)) (j,b)).symm
  ext ⟨i,a⟩ ⟨j,b⟩
  change (P * Q.submatrix (fun a => (i,a)) (fun b => (j,b)) * P.conjTranspose) a b = _
  rw [hb,hP.eq]
  have heq : P * ((C i).conjTranspose * C j) * P = (C i).conjTranspose * C j := by
    calc
      _ = (C i * P).conjTranspose * (C j * P) := by
        simp only [Matrix.conjTranspose_mul,hP.eq,Matrix.mul_assoc]
      _ = _ := by rw [hs i,hs j]
  rw [heq]
  exact congrFun (congrFun hgram (i,a)) (j,b)
end PPTQubit