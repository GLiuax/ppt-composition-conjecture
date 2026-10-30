import PPTQubit.SchmidtRank
import PPTQubit.SchmidtCone
import Mathlib.Analysis.Matrix.PosDef
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem schmidt_rank_closed {a b k : ℕ} :
    IsClosed {z : Fin a × Fin b → ℂ | SchmidtRankAtMost k z} := by
  have hset : {z : Fin a × Fin b → ℂ | SchmidtRankAtMost k z} =
    ⋂ (r : Fin (k+1) → Fin a) (c : Fin (k+1) → Fin b),
      {z | (show Matrix (Fin (k+1)) (Fin (k+1)) ℂ from fun i j => z (r i,c j)).det = 0} := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_iInter]
    rw [schmidt_rank_iff_matrix_rank,rank_le_iff_minors_zero]
    rfl
  rw [hset]
  apply isClosed_iInter
  intro r
  apply isClosed_iInter
  intro c
  apply isClosed_eq _ continuous_const
  simp only [Matrix.det_apply]
  fun_prop

def SchmidtUnitVectors {a b : ℕ} (k : ℕ) : Set (Fin a × Fin b → ℂ) :=
  Metric.sphere 0 1 ∩ {z | SchmidtRankAtMost k z}

theorem schmidt_unit_vectors_compact {a b k : ℕ} :
    IsCompact (SchmidtUnitVectors (a := a) (b := b) k) := by
  exact (isCompact_sphere (0 : Fin a × Fin b → ℂ) 1).inter_right schmidt_rank_closed

theorem pure_projector_continuous {a b : ℕ} :
    Continuous (fun z : Fin a × Fin b → ℂ => pureProjector z) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun z : Fin a × Fin b → ℂ => z i * star (z j))
  fun_prop

theorem schmidt_unit_projectors_compact {a b k : ℕ} :
    IsCompact (pureProjector '' SchmidtUnitVectors (a := a) (b := b) k) :=
  schmidt_unit_vectors_compact.image pure_projector_continuous
end PPTQubit
#print axioms PPTQubit.schmidt_rank_closed
#print axioms PPTQubit.schmidt_unit_projectors_compact
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem schmidt_projector_normalize {a b k : ℕ} (z : Fin a × Fin b → ℂ)
    (hz : SchmidtRankAtMost k z) :
    ∃ (c : ℝ) (u : Fin a × Fin b → ℂ), 0 ≤ c ∧
      (u ∈ SchmidtUnitVectors k ∨ u = 0 ∧ c = 0) ∧ pureProjector z = c • pureProjector u := by
  by_cases hz0 : z = 0
  · refine ⟨0,0,le_refl _,Or.inr ⟨rfl,rfl⟩,?_⟩
    subst z
    ext i j
    simp [pureProjector]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    let u : Fin a × Fin b → ℂ := ((‖z‖⁻¹ : ℝ) : ℂ) • z
    let c : ℝ := ‖z‖ ^ 2
    refine ⟨c,u,sq_nonneg _,Or.inl ⟨?_,?_⟩,?_⟩
    · change dist u 0 = 1
      rw [dist_zero_right]
      dsimp [u]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ (ne_of_gt hn)]
    · change SchmidtRankAtMost k u
      change SchmidtRankAtMost k (fun x => ((‖z‖⁻¹ : ℝ) : ℂ) * z x)
      exact schmidt_rank_scale z _ hz
    · ext i j
      simp only [Matrix.smul_apply,pureProjector]
      dsimp [u,c]
      change z i * star (z j) = ((‖z‖^2 : ℝ) : ℂ) *
        (((‖z‖⁻¹ : ℝ) : ℂ) * z i * star (((‖z‖⁻¹ : ℝ) : ℂ) * z j))
      simp only [StarMul.star_mul, Complex.star_def, Complex.conj_ofReal]
      have hi : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
      push_cast
      field_simp
theorem schmidt_number_normalized_expansion {a b k : ℕ}
    (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hQ : SchmidtNumberAtMost k Q) :
    ∃ (r : ℕ) (c : Fin r → ℝ) (u : Fin r → Fin a × Fin b → ℂ),
      (∀ t, 0 ≤ c t) ∧
      (∀ t, u t ∈ SchmidtUnitVectors k ∨ u t = 0 ∧ c t = 0) ∧
      Q = ∑ t, (c t) • pureProjector (u t) := by
  obtain ⟨r,z,hQ,hz⟩ := hQ
  choose c u hc hu heq using (fun t => schmidt_projector_normalize (z t) (hz t))
  refine ⟨r,c,u,hc,hu,?_⟩
  rw [hQ]
  apply Finset.sum_congr rfl
  intro t ht
  exact heq t
end PPTQubit
#print axioms PPTQubit.schmidt_number_normalized_expansion
#print axioms PPTQubit.schmidt_projector_normalize
open Matrix
noncomputable section
namespace PPTQubit

theorem schmidtCone_zero_eq_singleton {a b : ℕ} :
    SchmidtCone (a := a) (b := b) 0 = {0} := by
  ext Q
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨r,z,hQ,hz⟩
    have hz0 (t : Fin r) : z t = 0 := by
      obtain ⟨v,w,hv⟩ := hz t
      funext ⟨i,j⟩
      simpa using hv i j
    rw [hQ]
    apply Finset.sum_eq_zero
    intro t ht
    rw [hz0 t]
    ext i j
    simp [pureProjector]
  · intro hQ
    subst Q
    exact schmidtCone_zero

theorem schmidtCone_zero_closed {a b : ℕ} :
    IsClosed (SchmidtCone (a := a) (b := b) 0) := by
  rw [schmidtCone_zero_eq_singleton]
  exact isClosed_singleton
end PPTQubit
#print axioms PPTQubit.schmidtCone_zero_closed

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem matrix_psd_closed {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsClosed {Q : Matrix (ι) (ι) ℂ | Q.PosSemidef} := by
  have heq : {Q : Matrix (ι) (ι) ℂ | Q.PosSemidef} =
      {Q | Qᴴ = Q} ∩ ⋂ x : ι → ℂ, {Q | 0 ≤ (star x ⬝ᵥ Q *ᵥ x).re} := by
    ext Q
    simp only [Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_iInter]
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · rintro ⟨hQ,h⟩
      exact ⟨hQ,fun x => (Complex.nonneg_iff.mp (h x)).1⟩
    · rintro ⟨hQ,h⟩
      refine ⟨hQ,fun x => Complex.nonneg_iff.mpr ⟨h x,?_⟩⟩
      exact ((show Q.IsHermitian from hQ).im_star_dotProduct_mulVec_self x).symm
  rw [heq]
  apply IsClosed.inter
  · apply isClosed_eq ?_ continuous_id
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun Q : Matrix (ι) (ι) ℂ => star (Q j i))
    fun_prop
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    simp only [dotProduct,Matrix.mulVec]
    fun_prop
theorem schmidtCone_eq_psd_of_dim_le {a b k : ℕ} (h : a ≤ k ∨ b ≤ k) :
    SchmidtCone (a := a) (b := b) k = {Q | Q.PosSemidef} := by
  ext Q
  simp only [Set.mem_setOf_eq]
  constructor
  · exact schmidt_number_positive Q
  · intro hQ
    rcases h with ha | hb
    · exact schmidt_number_mono Q (positive_schmidt_bound_reference Q hQ) ha
    · exact schmidt_number_mono Q (positive_schmidt_bound_system Q hQ) hb

theorem schmidtCone_closed_of_dim_le {a b k : ℕ} (h : a ≤ k ∨ b ≤ k) :
    IsClosed (SchmidtCone (a := a) (b := b) k) := by
  rw [schmidtCone_eq_psd_of_dim_le h]
  exact matrix_psd_closed
end PPTQubit
#print axioms PPTQubit.schmidtCone_closed_of_dim_le
#print axioms PPTQubit.matrix_psd_closed
