import PPTQubit.StructuredTrimming
/-! Principal-block entanglement detects every entangled pure state. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem separable_ppt {a b : ℕ} (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hQ : IsSeparable Q) : IsPPT Q := by
  refine ⟨separable_positive Q hQ,?_⟩
  obtain ⟨r,v,w,hsum⟩ := hQ
  have he : partialTransposeFirst Q = ∑ s, pureProjector (fun x => star (v s x.1) * w s x.2) := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp only [partialTransposeFirst,Matrix.sum_apply,pureProjector,hsum,StarMul.star_mul,star_star]
    apply Finset.sum_congr rfl; intro s _; ring
  rw [he]
  apply Finset.sum_induction
  · intro A B hA hB; exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro s _; exact pureProjector_positive _

set_option maxHeartbeats 4000000 in
theorem pure_qubit_pt_zero_det (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : (partialTransposeFirst (pureProjector (fun x : Fin 2 × Fin 2 => A x.1 x.2))).PosSemidef) :
    A.det = 0 := by
  let w : Fin 2 × Fin 2 → ℂ := fun x =>
    (!![star (A 0 1), -star (A 0 0); star (A 1 1), -star (A 1 0)] : Matrix (Fin 2) (Fin 2) ℂ) x.1 x.2
  have hw00 : w (0,0) = star (A 0 1) := by simp [w]
  have hw01 : w (0,1) = -star (A 0 0) := by simp [w]
  have hw10 : w (1,0) = star (A 1 1) := by simp [w]
  have hw11 : w (1,1) = -star (A 1 0) := by simp [w]
  have he : star w ⬝ᵥ (partialTransposeFirst (pureProjector (fun x : Fin 2 × Fin 2 => A x.1 x.2))).mulVec w =
      -(2 : ℂ) * A.det * star A.det := by
    simp only [dotProduct,Matrix.mulVec,Fintype.sum_prod_type,Fin.sum_univ_two,
      Pi.star_apply,partialTransposeFirst,pureProjector,Matrix.det_fin_two,
      hw00,hw01,hw10,hw11,star_neg,star_star,StarMul.star_mul,star_sub]
    ring
  have hp := hA.dotProduct_mulVec_nonneg w
  rw [he] at hp
  have hr := (Complex.nonneg_iff.mp hp).1
  have hr' : 0 ≤ -2 * Complex.normSq A.det := by
    have he' : (-(2 : ℂ) * A.det * star A.det).re = -2 * Complex.normSq A.det := by
      rw [show -(2 : ℂ) * A.det * star A.det = -(2 : ℂ) * (A.det * star A.det) by ring]
      rw [Complex.star_def,Complex.mul_conj]
      simp [Complex.mul_re]
    rwa [he'] at hr
  have hz : Complex.normSq A.det = 0 := by nlinarith [Complex.normSq_nonneg A.det]
  exact Complex.normSq_eq_zero.mp hz
/-- For a pure input, separability of every two-row principal block forces
Schmidt rank at most one. No global block-structure theorem is assumed. -/
theorem pure_principal_blocks_rank_one {n m : ℕ} (z : Fin n × Fin m → ℂ)
    (hblocks : PrincipalTwoBlocksSeparable (pureProjector z)) : SchmidtRankAtMost 1 z := by
  apply schmidt_rank_of_matrix_rank
  let A : Matrix (Fin n) (Fin m) ℂ := fun i j => z (i,j)
  apply rank_le_one_of_two_minors_zero A
  intro f g
  by_cases hf : Function.Injective f
  · have hsep : IsSeparable (pureProjector (fun x : Fin 2 × Fin 2 => z (f x.1,g x.2))) := by
      obtain ⟨r,v,w,h⟩ := hblocks f hf
      refine ⟨r,v,fun s a => w s (g a),?_⟩
      intro i a j b
      simpa only [principalTwoBlock,Matrix.submatrix_apply,pureProjector] using h i (g a) j (g b)
    have hp := (separable_ppt _ hsep).2
    exact pure_qubit_pt_zero_det (A.submatrix f g) hp
  · have he : f 0 = f 1 := by
      by_contra hn
      apply hf
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    simp [Matrix.det_fin_two,Matrix.submatrix_apply,he]
    ring

theorem pure_principal_blocks_separable {n m : ℕ} (z : Fin n × Fin m → ℂ)
    (hblocks : PrincipalTwoBlocksSeparable (pureProjector z)) : IsSeparable (pureProjector z) := by
  apply (schmidt_one_iff_separable _).mp
  refine ⟨1,fun _ => z,?_,fun _ => pure_principal_blocks_rank_one z hblocks⟩
  simp only [Fin.sum_univ_one]

theorem positive_rank_one_is_pure {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (hQ : Q.PosSemidef) (hRank : Q.rank ≤ 1) :
    ∃ z : n → ℂ, Q = pureProjector z := by
  obtain ⟨r,C,hC,_,hr⟩ := psd_minimal_gram_factor Q hQ
  have hrle : r ≤ 1 := by omega
  interval_cases r
  · refine ⟨0,?_⟩
    rw [← hC]
    ext i j
    simp [Matrix.mul_apply,pureProjector]
  · refine ⟨fun i => star (C 0 i),?_⟩
    rw [← hC]
    ext i j
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,pureProjector]

theorem rank_one_principal_blocks_separable {n m : ℕ}
    (Q : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ)
    (hQ : Q.PosSemidef) (hRank : Q.rank ≤ 1) (hblocks : PrincipalTwoBlocksSeparable Q) :
    IsSeparable Q := by
  obtain ⟨z,rfl⟩ := positive_rank_one_is_pure Q hQ hRank
  exact pure_principal_blocks_separable z hblocks

theorem maximal_block_structure_rank_one {n m : ℕ}
    (Q : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ)
    (hn : 2 ≤ n) (hQ : Q.PosSemidef) (hRank : Q.rank ≤ 1)
    (hblocks : PrincipalTwoBlocksSeparable Q) : SchmidtNumberAtMost (n-1) Q := by
  have hsep := rank_one_principal_blocks_separable Q hQ hRank hblocks
  exact schmidt_number_mono Q ((schmidt_one_iff_separable Q).mpr hsep) (by omega)

end PPTQubit
#print axioms PPTQubit.pure_qubit_pt_zero_det

#print axioms PPTQubit.pure_principal_blocks_rank_one

#print axioms PPTQubit.rank_one_principal_blocks_separable

#print axioms PPTQubit.maximal_block_structure_rank_one
