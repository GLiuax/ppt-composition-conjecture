import PPTQubit.QubitSeparability
/-! Direct dual pairing from qubit PT-invariant separability. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def IsBlockPositive {p m : Type*} [Fintype p] [Fintype m]
    (W : Matrix (p × m) (p × m) ℂ) : Prop :=
  ∀ (v : p → ℂ) (w : m → ℂ),
    let z : p × m → ℂ := fun i => v i.1 * w i.2
    0 ≤ star z ⬝ᵥ W.mulVec z

def pureProjector {n : Type*} (z : n → ℂ) : Matrix n n ℂ :=
  fun i j => z i * star (z j)

theorem rank_one_trace_pairing {n : Type*} [Fintype n]
    (z : n → ℂ) (W : Matrix n n ℂ) :
    (pureProjector z * W).trace = star z ⬝ᵥ W.mulVec z := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureProjector, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem separable_block_positive_trace_nonneg {p m : Type*} [Fintype p] [Fintype m]
    (Q W : Matrix (p × m) (p × m) ℂ)
    (hQ : IsSeparable Q) (hW : IsBlockPositive W) : 0 ≤ (Q * W).trace := by
  obtain ⟨r, v, w, hsum⟩ := hQ
  let z : Fin r → p × m → ℂ := fun s i => v s i.1 * w s i.2
  have hmat : Q = ∑ s, pureProjector (z s) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simpa only [Matrix.sum_apply, pureProjector, z] using hsum i a j b
  rw [hmat, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_nonneg
  intro s _
  rw [rank_one_trace_pairing]
  exact hW (v s) (w s)

@[simp] theorem partialTransposeFirst_add {p m : Type*}
    (X Y : Matrix (p × m) (p × m) ℂ) :
    partialTransposeFirst (X + Y) = partialTransposeFirst X + partialTransposeFirst Y := rfl

@[simp] theorem partialTransposeFirst_smul {p m : Type*} (c : ℂ)
    (X : Matrix (p × m) (p × m) ℂ) :
    partialTransposeFirst (c • X) = c • partialTransposeFirst X := rfl

def symmetrizeFirst {p m : Type*} (X : Matrix (p × m) (p × m) ℂ) :
    Matrix (p × m) (p × m) ℂ := (1 / 2 : ℂ) • (X + partialTransposeFirst X)

theorem ppt_symmetrizeFirst_positive {p m : Type*} [Fintype p] [Fintype m]
    (X : Matrix (p × m) (p × m) ℂ) (hX : IsPPT X) :
    (symmetrizeFirst X).PosSemidef := by
  exact (hX.1.add hX.2).smul (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩ : (0 : ℂ) ≤ 1 / 2)

theorem symmetrizeFirst_invariant {p m : Type*}
    (X : Matrix (p × m) (p × m) ℂ) :
    partialTransposeFirst (symmetrizeFirst X) = symmetrizeFirst X := by
  simp only [symmetrizeFirst, partialTransposeFirst_smul, partialTransposeFirst_add,
    partialTransposeFirst_involutive, add_comm]

/-- The dual pairing consequence of qubit PT-invariant separability.
This is proved directly, without assuming a cone-duality theorem. -/
theorem qubit_invariant_block_positive_ppt_pairing {m : ℕ}
    (X W : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ)
    (hX : IsPPT X) (hW : IsBlockPositive W)
    (hpt : partialTransposeFirst W = W) : 0 ≤ (X * W).trace := by
  have hsep : IsSeparable (symmetrizeFirst X) :=
    qubit_pt_invariant_separable _ (ppt_symmetrizeFirst_positive X hX)
      (symmetrizeFirst_invariant X)
  have heq : (symmetrizeFirst X * W).trace = (X * W).trace := by
    rw [symmetrizeFirst, Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add]
    rw [← partialTransposeFirst_trace_pairing, hpt]
    simp only [smul_eq_mul]
    ring
  rw [← heq]
  exact separable_block_positive_trace_nonneg _ W hsep hW

end PPTQubit
#print axioms PPTQubit.separable_block_positive_trace_nonneg
#print axioms PPTQubit.qubit_invariant_block_positive_ppt_pairing
