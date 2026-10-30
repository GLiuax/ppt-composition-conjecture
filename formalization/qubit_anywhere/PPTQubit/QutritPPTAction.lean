import PPTQubit.ChoiTensor
import PPTQubit.RealPlanes
/-! A PPT map sends every PT-invariant qutrit-reference positive input to a separable output. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem localCongruence_pure {p q n : ℕ} (U : Matrix (Fin q) (Fin p) ℂ)
    (z : Fin p × Fin n → ℂ) :
    localCongruence U (pureProjector z) =
      pureProjector (fun i => ∑ s, U i.1 s * z (s,i.2)) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [localCongruence_entry, pureProjector, star_sum, StarMul.star_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem symmetrizeFirst_fixed {p n : ℕ}
    (X : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ)
    (hX : partialTransposeFirst X = X) : symmetrizeFirst X = X := by
  rw [symmetrizeFirst,hX]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

theorem symmetrizeFirst_sum {ι : Type*} [Fintype ι] {p n : ℕ}
    (X : ι → Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) :
    symmetrizeFirst (∑ i, X i) = ∑ i, symmetrizeFirst (X i) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [symmetrizeFirst,Matrix.smul_apply,Matrix.add_apply,Matrix.sum_apply,
    partialTransposeFirst,smul_eq_mul,Finset.mul_sum,Finset.sum_add_distrib,mul_add]

theorem ppt_map_qutrit_invariant_separable {n d : ℕ} (T : MatrixMap n d)
    (hT : IsPPTMap T) (Q : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ)
    (hQ : Q.PosSemidef) (hpt : partialTransposeFirst Q = Q) :
    IsSeparable (applySecond T Q) := by
  classical
  obtain ⟨psi,alpha,hsum,hrel⟩ := pt_invariant_real_hyperplane_decomposition (p := 1) Q hQ hpt
  have hmat : Q = ∑ s, pureProjector (psi s) := by
    ext i j
    simpa only [Matrix.sum_apply,pureProjector] using hsum i j
  have hs (s : Fin Q.rank) :
      IsSeparable (symmetrizeFirst (applySecond T (pureProjector (psi s)))) := by
    obtain ⟨U,C,_,hf⟩ := real_qutrit_plane_factor (psi s) (alpha s) (hrel s).2.1 (hrel s).2.2
    let z : Fin 2 × Fin n → ℂ := fun i => C i.1 i.2
    have heq : localCongruence (realMatrix U) (pureProjector z) = pureProjector (psi s) := by
      rw [localCongruence_pure]
      congr 1
      funext ⟨i,a⟩
      exact (hf i a).symm
    rw [← heq,applySecond_localCongruence,localCongruence_real_symmetrize]
    apply localCongruence_separable
    apply qubit_pt_invariant_separable
    · exact ppt_symmetrizeFirst_positive _ (ppt_map_applySecond T hT _ (pureProjector_positive z))
    · exact symmetrizeFirst_invariant _
  have hfixed : partialTransposeFirst (applySecond T Q) = applySecond T Q := by
    rw [← applySecond_partialTranspose,hpt]
  rw [← symmetrizeFirst_fixed _ hfixed,hmat,map_sum,symmetrizeFirst_sum]
  exact separable_finite_sum _ hs

end PPTQubit
#print axioms PPTQubit.ppt_map_qutrit_invariant_separable
