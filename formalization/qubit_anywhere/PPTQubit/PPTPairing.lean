import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

/-! Partial transpose and the nonnegative pairing of PPT operators with decomposable witnesses. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def partialTransposeFirst {p m : Type*}
    (Q : Matrix (p × m) (p × m) ℂ) : Matrix (p × m) (p × m) ℂ :=
  fun i j => Q (j.1, i.2) (i.1, j.2)

@[simp] theorem partialTransposeFirst_involutive {p m : Type*}
    (Q : Matrix (p × m) (p × m) ℂ) :
    partialTransposeFirst (partialTransposeFirst Q) = Q := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rfl

theorem partialTransposeFirst_trace_pairing {p m : Type*} [Fintype p] [Fintype m]
    (X Y : Matrix (p × m) (p × m) ℂ) :
    (X * partialTransposeFirst Y).trace = (partialTransposeFirst X * Y).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    partialTransposeFirst]
  calc
    _ = ∑ a, ∑ i, ∑ j, ∑ b, X (i, a) (j, b) * Y (i, b) (j, a) :=
      Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, ∑ b, X (i, a) (j, b) * Y (i, b) (j, a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ i, ∑ b, X (i, a) (j, b) * Y (i, b) (j, a) :=
      Finset.sum_comm
    _ = _ := rfl

theorem psd_trace_mul_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  let hH := hB.isHermitian
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let d : n → ℂ := fun i => (hH.eigenvalues i : ℂ)
  have hBd : B = U * Matrix.diagonal d * U.conjTranspose := by
    simpa only [U, d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_apply] using hH.spectral_theorem
  have hC := hA.conjTranspose_mul_mul_same U
  have ht : (A * B).trace = ((U.conjTranspose * A * U) * Matrix.diagonal d).trace := by
    rw [hBd, ← Matrix.mul_assoc A, Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  rw [ht]
  change 0 ≤ ∑ i, ((U.conjTranspose * A * U) * Matrix.diagonal d) i i
  apply Finset.sum_nonneg
  intro i _
  rw [Matrix.mul_diagonal]
  apply mul_nonneg hC.diag_nonneg
  exact Complex.nonneg_iff.mpr ⟨hB.eigenvalues_nonneg i, rfl⟩

def IsPPT {p m : Type*} [Fintype p] [Fintype m]
    (X : Matrix (p × m) (p × m) ℂ) : Prop :=
  X.PosSemidef ∧ (partialTransposeFirst X).PosSemidef

def IsDecomposableWitness {p m : Type*} [Fintype p] [Fintype m]
    (W : Matrix (p × m) (p × m) ℂ) : Prop :=
  ∃ A B : Matrix (p × m) (p × m) ℂ,
    A.PosSemidef ∧ B.PosSemidef ∧ W = A + partialTransposeFirst B

theorem ppt_decomposable_trace_nonneg {p m : Type*}
    [Fintype p] [Fintype m] [DecidableEq p] [DecidableEq m]
    (X W : Matrix (p × m) (p × m) ℂ)
    (hX : IsPPT X) (hW : IsDecomposableWitness W) :
    0 ≤ (X * W).trace := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hW
  rw [Matrix.mul_add, Matrix.trace_add, partialTransposeFirst_trace_pairing]
  exact add_nonneg (psd_trace_mul_nonneg X A hX.1 hA)
    (psd_trace_mul_nonneg (partialTransposeFirst X) B hX.2 hB)

end PPTQubit
#print axioms PPTQubit.ppt_decomposable_trace_nonneg
#print axioms PPTQubit.partialTransposeFirst_trace_pairing
#print axioms PPTQubit.psd_trace_mul_nonneg
