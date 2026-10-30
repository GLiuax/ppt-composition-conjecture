import PPTQubit.SingularSupport
import PPTQubit.MinimalGram
/-! Lossless orthogonal support compression for positive operators, including singular marginals. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem psd_support_projection {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (hM : M.PosSemidef) :
    ∃ P : Matrix (Fin m) (Fin m) ℂ,
      P.IsHermitian ∧ P * P = P ∧ M * P = M ∧
      (∀ x, P.mulVec x = 0 ↔ M.mulVec x = 0) ∧
      (∀ x, P.mulVec x = x → x ≠ 0 → 0 < star x ⬝ᵥ M.mulVec x) := by
  obtain ⟨J, hJ, hJMJ, hMJM, hcomm⟩ := psd_commuting_generalized_inverse M hM
  let P := J * M
  have hP : P.IsHermitian := by
    change (J * M).conjTranspose = J * M
    rw [Matrix.conjTranspose_mul, hJ.isHermitian.eq, hM.isHermitian.eq, hcomm]
  have hPP : P * P = P := by
    change (J * M) * (J * M) = J * M
    rw [← Matrix.mul_assoc, hJMJ]
  have hMP : M * P = M := by
    change M * (J * M) = M
    rw [← Matrix.mul_assoc, hMJM]
  have hk (x : Fin m → ℂ) : P.mulVec x = 0 ↔ M.mulVec x = 0 := by
    constructor
    · intro hx
      rw [← hMP, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    · intro hx
      change (J * M).mulVec x = 0
      rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  refine ⟨P, hP, hPP, hMP, hk, ?_⟩
  intro x hx hxne
  obtain ⟨S, hS⟩ := psd_gram_factor M hM
  have hsne : S.mulVec x ≠ 0 := by
    intro hs
    have hm : M.mulVec x = 0 := by
      rw [← hS, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_zero]
    have hp := (hk x).mpr hm
    exact hxne (hx.symm.trans hp)
  rw [← hS, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  exact Matrix.dotProduct_star_self_pos_iff.mpr hsne

theorem marginal_kernel_is_common {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ) (x : Fin m → ℂ)
    (hx : (∑ i, (C i).conjTranspose * C i).mulVec x = 0) :
    ∀ i, (C i).mulVec x = 0 := by
  let H : Matrix (Fin p × Fin r) (Fin m) ℂ := fun i a => C i.1 i.2 a
  have hH : H.conjTranspose * H = ∑ i, (C i).conjTranspose * C i := by
    ext a b
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]
    rfl
  have hz : H.mulVec x = 0 := by
    apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero H x).mp
    rw [hH]
    exact hx
  intro i
  funext s
  exact congrFun hz (i, s)

theorem gram_support_compression {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ) :
    ∃ P : Matrix (Fin m) (Fin m) ℂ,
      P.IsHermitian ∧ P * P = P ∧
      (∀ i, C i * P = C i) ∧
      (∀ x, P.mulVec x = 0 ↔ (∑ i, (C i).conjTranspose * C i).mulVec x = 0) ∧
      (∀ x, P.mulVec x = x → x ≠ 0 →
        0 < star x ⬝ᵥ (∑ i, (C i).conjTranspose * C i).mulVec x) := by
  let M := ∑ i, (C i).conjTranspose * C i
  have hM : M.PosSemidef := by
    dsimp only [M]
    apply Finset.sum_induction
    · intro A B hA hB
      exact hA.add hB
    · exact Matrix.PosSemidef.zero
    · intro i _
      exact Matrix.posSemidef_conjTranspose_mul_self (C i)
  obtain ⟨P, hP, hPP, hMP, hk, hp⟩ := psd_support_projection M hM
  refine ⟨P, hP, hPP, ?_, hk, hp⟩
  intro i
  have hzero : M * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hMP, sub_self]
  have hc : C i * (1 - P) = 0 := by
    ext s a
    have hx : M.mulVec ((1 - P).col a) = 0 := by
      funext b
      exact congrFun (congrFun hzero b) a
    exact congrFun (marginal_kernel_is_common C _ hx i) s
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hc
  exact hc.symm


/-- Congruence on the other factor, written blockwise. -/
def secondFactorCompression {p m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ)
    (Q : Matrix (Fin p × Fin m) (Fin p × Fin m) ℂ) :
    Matrix (Fin p × Fin m) (Fin p × Fin m) ℂ := fun i j =>
  (P.conjTranspose * Q.submatrix (fun a => (i.1, a)) (fun b => (j.1, b)) * P) i.2 j.2

theorem secondFactorCompression_partialTranspose {p m : ℕ}
    (P : Matrix (Fin m) (Fin m) ℂ)
    (Q : Matrix (Fin p × Fin m) (Fin p × Fin m) ℂ) :
    partialTransposeFirst (secondFactorCompression P Q) =
      secondFactorCompression P (partialTransposeFirst Q) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rfl

/-- The support projection loses no part of Q. Its kernel equals that of the
marginal, and the marginal is strictly positive on its range. -/
theorem positive_operator_support_compression {p m : ℕ}
    (Q : Matrix (Fin p × Fin m) (Fin p × Fin m) ℂ) (hQ : Q.PosSemidef) :
    ∃ P : Matrix (Fin m) (Fin m) ℂ,
      P.IsHermitian ∧ P * P = P ∧ secondFactorCompression P Q = Q ∧
      (∀ x, P.mulVec x = 0 ↔ (partialTraceFirst Q).mulVec x = 0) ∧
      (∀ x, P.mulVec x = x → x ≠ 0 →
        0 < star x ⬝ᵥ (partialTraceFirst Q).mulVec x) := by
  obtain ⟨r, F, hF, _, _⟩ := psd_minimal_gram_factor Q hQ
  let C : Fin p → Matrix (Fin r) (Fin m) ℂ := fun i s a => F s (i, a)
  have hgram : (gramBlockRow C).conjTranspose * gramBlockRow C = Q := hF
  have hmarg : partialTraceFirst Q = ∑ i, (C i).conjTranspose * C i := by
    rw [← hgram, partialTraceFirst_gram]
  obtain ⟨P, hP, hPP, hs, hk, hp⟩ := gram_support_compression C
  refine ⟨P, hP, hPP, ?_, ?_, ?_⟩
  · have hb (i j : Fin p) :
        Q.submatrix (fun a => (i, a)) (fun b => (j, b)) = (C i).conjTranspose * C j := by
      ext a b
      exact (congrFun (congrFun hgram (i, a)) (j, b)).symm
    ext ⟨i, a⟩ ⟨j, b⟩
    change (P.conjTranspose * Q.submatrix (fun a => (i, a)) (fun b => (j, b)) * P) a b = _
    rw [hb]
    have heq : P.conjTranspose * ((C i).conjTranspose * C j) * P =
        (C i).conjTranspose * C j := by
      calc
        _ = (C i * P).conjTranspose * (C j * P) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hs i, hs j]
    rw [heq]
    exact congrFun (congrFun hgram (i, a)) (j, b)
  · simpa only [hmarg] using hk
  · simpa only [hmarg] using hp

end PPTQubit
#print axioms PPTQubit.psd_support_projection
#print axioms PPTQubit.marginal_kernel_is_common
#print axioms PPTQubit.gram_support_compression
#print axioms PPTQubit.secondFactorCompression_partialTranspose
#print axioms PPTQubit.positive_operator_support_compression
