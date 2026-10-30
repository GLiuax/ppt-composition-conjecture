import PPTQubit.LocalOperations
/-! Positive maps and Choi block positivity, and the complete PPT Choi criterion. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem choi_transpose_invariant {p q : ℕ} (T : MatrixMap p q)
    (hT : IsTransposeInvariantMap T) : partialTransposeFirst (choi T) = choi T := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change T (Matrix.single j i 1) a b = T (Matrix.single i j 1) a b
  have ht : (Matrix.single i j (1 : ℂ)).transpose = Matrix.single j i 1 := by
    simp
  rw [← ht, hT]

theorem pureProjector_positive {n : Type*} [Fintype n] [DecidableEq n] (v : n → ℂ) :
    (pureProjector v).PosSemidef := by
  let C : Matrix (Fin 1) n ℂ := fun _ i => star (v i)
  have hC : C.conjTranspose * C = pureProjector v := by
    ext i j
    simp [C, pureProjector, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← hC]
  exact Matrix.posSemidef_conjTranspose_mul_self C

theorem choi_block_positive {p q : ℕ} (T : MatrixMap p q) (hT : IsPositiveMap T) :
    IsBlockPositive (choi T) := by
  intro v w
  let z : Fin p × Fin q → ℂ := fun i => v i.1 * w i.2
  have heq : star z ⬝ᵥ (choi T).mulVec z =
      star w ⬝ᵥ (T (pureProjector (star v))).mulVec w := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Pi.star_apply,
      z, choi, StarMul.star_mul, map_entry_expansion T (pureProjector (star v)), pureProjector, star_star,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; arg 2; ext i; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change 0 ≤ star z ⬝ᵥ (choi T).mulVec z
  rw [heq]
  exact (hT _ (pureProjector_positive (star v))).dotProduct_mulVec_nonneg w

theorem applySecond_localCongruence {p q n m : ℕ} (T : MatrixMap p q)
    (U : Matrix (Fin m) (Fin n) ℂ) (X : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ) :
    applySecond T (localCongruence U X) = localCongruence U (applySecond T X) := by
  have hblock (i j : Fin m) :
      (localCongruence U X).submatrix (fun a => (i,a)) (fun b => (j,b)) =
      ∑ s, ∑ t, (U i s * star (U j t)) • X.submatrix (fun a => (s,a)) (fun b => (t,b)) := by
    ext a b
    simp only [Matrix.submatrix_apply, localCongruence_entry, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  ext ⟨i,a⟩ ⟨j,b⟩
  change T ((localCongruence U X).submatrix (fun a => (i,a)) (fun b => (j,b))) a b = _
  rw [hblock]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    localCongruence_entry]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  change U i s * star (U j t) * T (X.submatrix _ _) a b =
    U i s * T (X.submatrix _ _) a b * star (U j t)
  ring

def vectorize {p n : ℕ} (C : Matrix (Fin p) (Fin n) ℂ) : Fin n × Fin p → ℂ :=
  fun i => C i.2 i.1

theorem applySecond_pure_choi {p q n : ℕ} (T : MatrixMap p q)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    applySecond T (pureProjector (vectorize C)) = localCongruence C.transpose (choi T) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change T ((pureProjector (vectorize C)).submatrix _ _) a b = _
  rw [map_entry_expansion]
  simp only [Matrix.submatrix_apply, pureProjector, vectorize, localCongruence_entry,
    Matrix.transpose_apply, choi]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem applySecond_partialTranspose {p q n : ℕ} (T : MatrixMap p q)
    (X : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ) :
    applySecond T (partialTransposeFirst X) = partialTransposeFirst (applySecond T X) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  rfl

theorem applySecond_symmetrize {p q n : ℕ} (T : MatrixMap p q)
    (X : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ) :
    applySecond T (symmetrizeFirst X) = symmetrizeFirst (applySecond T X) := by
  simp only [symmetrizeFirst, map_smul, map_add, applySecond_partialTranspose]


def IsPPTMap {p q : ℕ} (T : MatrixMap p q) : Prop := IsPPT (choi T)

/-- The Choi PPT condition implies PPT output for every positive bipartite input. -/
theorem ppt_map_applySecond {p q n : ℕ} (T : MatrixMap p q) (hT : IsPPTMap T)
    (X : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ) (hX : X.PosSemidef) :
    IsPPT (applySecond T X) := by
  obtain ⟨r, psi, hsum⟩ := positive_pure_expansion X hX
  rw [hsum, map_sum]
  apply ppt_finite_sum
  intro s
  let C : Matrix (Fin p) (Fin n) ℂ := fun i a => psi s (a,i)
  change IsPPT (applySecond T (pureProjector (vectorize C)))
  rw [applySecond_pure_choi]
  exact localCongruence_ppt C.transpose (choi T) hT

theorem localCongruence_identity {p n : ℕ}
    (X : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    localCongruence (1 : Matrix (Fin p) (Fin p) ℂ) X = X := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp [localCongruence_entry, Matrix.one_apply, apply_ite]

theorem ppt_map_iff_complete_ppt {p q : ℕ} (T : MatrixMap p q) :
    IsPPTMap T ↔ ∀ (n : ℕ) (X : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ),
      X.PosSemidef → IsPPT (applySecond T X) := by
  constructor
  · intro h n X hX
    exact ppt_map_applySecond T h X hX
  · intro h
    have hh := h p (pureProjector (vectorize (1 : Matrix (Fin p) (Fin p) ℂ)))
      (pureProjector_positive _)
    rw [applySecond_pure_choi, Matrix.transpose_one, localCongruence_identity] at hh
    exact hh

end PPTQubit
#print axioms PPTQubit.choi_block_positive
#print axioms PPTQubit.applySecond_pure_choi
#print axioms PPTQubit.ppt_map_iff_complete_ppt
