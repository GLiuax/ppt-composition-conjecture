import PPTQubit.SchmidtConsequences
/-! k-positivity and Schmidt-rank block positivity of Choi operators. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def IsKPositiveMap {p q : ℕ} (k : ℕ) (T : MatrixMap p q) : Prop :=
  ∀ Q : Matrix (Fin k × Fin p) (Fin k × Fin p) ℂ,
    Q.PosSemidef → (applySecond T Q).PosSemidef

def IsKBlockPositive {p q : ℕ} (k : ℕ)
    (W : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ) : Prop :=
  ∀ z : Fin p × Fin q → ℂ, SchmidtRankAtMost k z → 0 ≤ star z ⬝ᵥ W.mulVec z

theorem localLift_conjTranspose_mulVec {p k q : ℕ} (U : Matrix (Fin k) (Fin p) ℂ)
    (w : Fin k × Fin q → ℂ) (i : Fin p) (a : Fin q) :
    (localLift U).conjTranspose.mulVec w (i,a) = ∑ j, star (U j i) * w (j,a) := by
  simp [Matrix.mulVec,dotProduct,Matrix.conjTranspose_apply,localLift,
    Fintype.sum_prod_type,Matrix.one_apply,apply_ite]

theorem localCongruence_quadratic {p k q : ℕ} (U : Matrix (Fin k) (Fin p) ℂ)
    (W : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)
    (w : Fin k × Fin q → ℂ) :
    star w ⬝ᵥ (localCongruence U W).mulVec w =
      star ((localLift U).conjTranspose.mulVec w) ⬝ᵥ
        W.mulVec ((localLift U).conjTranspose.mulVec w) := by
  change star w ⬝ᵥ ((localLift U) * W * (localLift U).conjTranspose).mulVec w = _
  have hs := Matrix.star_mulVec (localLift U).conjTranspose w
  simp only [Matrix.conjTranspose_conjTranspose] at hs
  rw [Matrix.mul_assoc,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,
    ← hs,← Matrix.mulVec_mulVec]

theorem kpositive_implies_choi_kblock {p q k : ℕ} (T : MatrixMap p q)
    (hT : IsKPositiveMap k T) : IsKBlockPositive k (choi T) := by
  intro z hz
  obtain ⟨v,w,hz⟩ := hz
  let U : Matrix (Fin k) (Fin p) ℂ := fun t i => star (v t i)
  let C : Matrix (Fin p) (Fin k) ℂ := U.transpose
  let x : Fin k × Fin q → ℂ := fun a => w a.1 a.2
  have hx : (localLift U).conjTranspose.mulVec x = z := by
    funext ⟨i,a⟩
    rw [localLift_conjTranspose_mulVec]
    simp only [U,x,star_star]
    exact (hz i a).symm
  have hh := hT (pureProjector (vectorize C)) (pureProjector_positive _)
  rw [applySecond_pure_choi,Matrix.transpose_transpose] at hh
  have ht := hh.dotProduct_mulVec_nonneg x
  rw [localCongruence_quadratic,hx] at ht
  exact ht

/-- The converse uses Hermiticity, required by the matrix PSD definition. -/
theorem choi_kblock_implies_kpositive {p q k : ℕ} (T : MatrixMap p q)
    (hH : (choi T).IsHermitian) (hW : IsKBlockPositive k (choi T)) : IsKPositiveMap k T := by
  intro Q hQ
  obtain ⟨r,z,hQ⟩ := positive_pure_expansion Q hQ
  rw [hQ,map_sum]
  apply Finset.sum_induction
  · intro A B hA hB; exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro t _
    let C : Matrix (Fin p) (Fin k) ℂ := fun i a => z t (a,i)
    change (applySecond T (pureProjector (vectorize C))).PosSemidef
    rw [applySecond_pure_choi]
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · change ((localLift C.transpose) * choi T * (localLift C.transpose).conjTranspose).IsHermitian
      change ((localLift C.transpose) * choi T * (localLift C.transpose).conjTranspose).conjTranspose = _
      rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hH.eq]
      simp only [Matrix.mul_assoc]
    · intro w
      rw [localCongruence_quadratic]
      apply hW
      refine ⟨fun t i => star (C i t),fun t a => w (t,a),?_⟩
      intro i a
      simpa only [Matrix.transpose_apply] using localLift_conjTranspose_mulVec C.transpose w i a
theorem kpositive_iff_choi_kblock {p q k : ℕ} (T : MatrixMap p q)
    (hH : (choi T).IsHermitian) : IsKPositiveMap k T ↔ IsKBlockPositive k (choi T) :=
  ⟨kpositive_implies_choi_kblock T,choi_kblock_implies_kpositive T hH⟩

theorem kpositive_mono {p q j k : ℕ} (T : MatrixMap p q)
    (hH : (choi T).IsHermitian) (hT : IsKPositiveMap k T) (hjk : j ≤ k) :
    IsKPositiveMap j T := by
  apply choi_kblock_implies_kpositive T hH
  have hW := kpositive_implies_choi_kblock T hT
  intro z hz
  exact hW z (schmidt_rank_mono z hz hjk)

/-- The algebraic dual of the Schmidt-number-k cone consists exactly of
operators nonnegative on pure vectors of Schmidt rank at most k. -/
theorem kblock_iff_schmidt_pairing_nonnegative {p q k : ℕ}
    (W : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ) :
    IsKBlockPositive k W ↔
      ∀ Q : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ,
        SchmidtNumberAtMost k Q → 0 ≤ (Q * W).trace := by
  constructor
  · intro hW Q hQ
    obtain ⟨r,z,hQ,hz⟩ := hQ
    rw [hQ,Matrix.sum_mul,Matrix.trace_sum]
    apply Finset.sum_nonneg
    intro t _
    rw [rank_one_trace_pairing]
    exact hW (z t) (hz t)
  · intro h z hz
    have hQ : SchmidtNumberAtMost k (pureProjector z) := by
      refine ⟨1,fun _ => z,?_,fun _ => hz⟩
      simp only [Fin.sum_univ_one]
    have hh := h (pureProjector z) hQ
    rwa [rank_one_trace_pairing] at hh
end PPTQubit
#print axioms PPTQubit.kpositive_implies_choi_kblock
#print axioms PPTQubit.choi_kblock_implies_kpositive
#print axioms PPTQubit.kblock_iff_schmidt_pairing_nonnegative
