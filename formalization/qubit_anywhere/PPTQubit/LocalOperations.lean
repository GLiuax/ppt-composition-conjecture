import PPTQubit.MatrixMaps
import Mathlib.LinearAlgebra.Matrix.Kronecker
/-! Local congruences preserve PPT and separability and commute with the relevant symmetrization. -/

open Matrix
open scoped BigOperators ComplexOrder Matrix
noncomputable section
namespace PPTQubit

def localLift {p q n : ℕ} (U : Matrix (Fin q) (Fin p) ℂ) :
    Matrix (Fin q × Fin n) (Fin p × Fin n) ℂ := Matrix.kroneckerMap (· * ·) U (1 : Matrix (Fin n) (Fin n) ℂ)

def localCongruence {p q n : ℕ} (U : Matrix (Fin q) (Fin p) ℂ)
    (X : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    Matrix (Fin q × Fin n) (Fin q × Fin n) ℂ := localLift U * X * (localLift U).conjTranspose

theorem localCongruence_entry {p q n : ℕ} (U : Matrix (Fin q) (Fin p) ℂ)
    (X : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) (i j : Fin q) (a b : Fin n) :
    localCongruence U X (i,a) (j,b) =
      ∑ s, ∑ t, U i s * X (s,a) (t,b) * star (U j t) := by
  simp [localCongruence, localLift, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.one_apply, apply_ite,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]


def conjugateMatrix {p q : ℕ} (U : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin q) ℂ :=
  U.map star

theorem localCongruence_partialTranspose {p q n : ℕ}
    (U : Matrix (Fin q) (Fin p) ℂ) (X : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    partialTransposeFirst (localCongruence U X) =
      localCongruence (conjugateMatrix U) (partialTransposeFirst X) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change localCongruence U X (j,a) (i,b) = _
  simp only [localCongruence_entry, conjugateMatrix, Matrix.map_apply, star_star,
    partialTransposeFirst]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem localCongruence_ppt {p q n : ℕ}
    (U : Matrix (Fin q) (Fin p) ℂ) (X : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ)
    (hX : IsPPT X) : IsPPT (localCongruence U X) := by
  constructor
  · exact hX.1.mul_mul_conjTranspose_same (localLift U)
  · rw [localCongruence_partialTranspose]
    exact hX.2.mul_mul_conjTranspose_same (localLift (conjugateMatrix U))

theorem separable_finite_sum {ι : Type*} [Fintype ι] {p n : ℕ}
    (X : ι → Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ)
    (hX : ∀ i, IsSeparable (X i)) : IsSeparable (∑ i, X i) := by
  classical
  choose r v w hsum using hX
  let κ := (i : ι) × Fin (r i)
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ, fun s => v (e s).1 (e s).2,
    fun s => w (e s).1 (e s).2, ?_⟩
  intro i a j b
  simp only [Matrix.sum_apply, hsum]
  calc
    _ = ∑ s : κ, (v s.1 s.2 i * w s.1 s.2 a) * star (v s.1 s.2 j * w s.1 s.2 b) :=
      (Fintype.sum_sigma _).symm
    _ = _ := (e.sum_comp _).symm

theorem ppt_finite_sum {ι : Type*} [Fintype ι] {p n : ℕ}
    (X : ι → Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ)
    (hX : ∀ i, IsPPT (X i)) : IsPPT (∑ i, X i) := by
  classical
  apply Finset.sum_induction
  · intro A B hA hB
    exact ⟨hA.1.add hB.1, by rw [partialTransposeFirst_add]; exact hA.2.add hB.2⟩
  · exact ⟨Matrix.PosSemidef.zero, Matrix.PosSemidef.zero⟩
  · intro i _
    exact hX i

theorem localCongruence_product {p q n : ℕ} (U : Matrix (Fin q) (Fin p) ℂ)
    (v : Fin p → ℂ) (w : Fin n → ℂ) :
    localCongruence U (pureProjector (fun i => v i.1 * w i.2)) =
      pureProjector (fun i => U.mulVec v i.1 * w i.2) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [localCongruence_entry, pureProjector, Matrix.mulVec, dotProduct,
    StarMul.star_mul, star_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem localCongruence_sum {ι : Type*} [Fintype ι] {p q n : ℕ}
    (U : Matrix (Fin q) (Fin p) ℂ) (X : ι → Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    localCongruence U (∑ s, X s) = ∑ s, localCongruence U (X s) := by
  simp only [localCongruence, Matrix.mul_sum, Matrix.sum_mul]

theorem localCongruence_separable {p q n : ℕ} (U : Matrix (Fin q) (Fin p) ℂ)
    (X : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) (hX : IsSeparable X) :
    IsSeparable (localCongruence U X) := by
  obtain ⟨r, v, w, hsum⟩ := hX
  have heq : X = ∑ s, pureProjector (fun i => v s i.1 * w s i.2) := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simpa only [Matrix.sum_apply, pureProjector] using hsum i a j b
  refine ⟨r, fun s => U.mulVec (v s), w, ?_⟩
  intro i a j b
  rw [heq, localCongruence_sum]
  simp only [Matrix.sum_apply, localCongruence_product, pureProjector]

theorem localCongruence_real_symmetrize {p q n : ℕ}
    (U : Matrix (Fin q) (Fin p) ℝ) (X : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    symmetrizeFirst (localCongruence (realMatrix U) X) =
      localCongruence (realMatrix U) (symmetrizeFirst X) := by
  have hreal : conjugateMatrix (realMatrix U) = realMatrix U := by
    ext i j
    simp [conjugateMatrix, realMatrix, Matrix.map_apply]
  simp only [symmetrizeFirst]
  rw [localCongruence_partialTranspose, hreal]
  simp only [localCongruence, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]

/-- A positive matrix is a finite sum of pure projectors. -/
theorem positive_pure_expansion {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (hQ : Q.PosSemidef) :
    ∃ (r : ℕ) (psi : Fin r → n → ℂ), Q = ∑ s, pureProjector (psi s) := by
  obtain ⟨r, C, hC, _, _⟩ := psd_minimal_gram_factor Q hQ
  refine ⟨r, fun s i => star (C s i), ?_⟩
  rw [← hC]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    pureProjector, star_star]

end PPTQubit
#print axioms PPTQubit.localCongruence_ppt
#print axioms PPTQubit.localCongruence_separable
#print axioms PPTQubit.separable_finite_sum
