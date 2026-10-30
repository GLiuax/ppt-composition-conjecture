import PPTQubit.SchmidtRank
/-! Schmidt-number decrease for operators fixed by partial transposition. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem schmidt_rank_lt_of_left_kernel {n m : ℕ} (z : Fin n × Fin m → ℂ)
    (alpha : Fin n → ℝ) (ha : alpha ≠ 0)
    (hrel : ∀ a, ∑ i, (alpha i : ℂ) * z (i,a) = 0) : SchmidtRankAtMost (n-1) z := by
  apply schmidt_rank_of_matrix_rank
  let A : Matrix (Fin n) (Fin m) ℂ := fun i j => z (i,j)
  let v : Fin n → ℂ := fun i => (alpha i : ℂ)
  have hv : v ≠ 0 := by
    intro h
    apply ha
    funext i
    apply Complex.ofReal_injective
    exact congrFun h i
  have hker : A.transpose.mulVecLin v = 0 := by
    funext j
    change ∑ i, A.transpose j i * v i = 0
    simpa only [A,v,Matrix.transpose_apply,mul_comm] using hrel j
  have hkne : A.transpose.mulVecLin.ker ≠ ⊥ := by
    intro h
    exact hv ((LinearMap.ker_eq_bot'.mp h) v hker)
  have hpos : 0 < Module.finrank ℂ A.transpose.mulVecLin.ker := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hkne (Submodule.finrank_eq_zero.mp h)
  have hdim := LinearMap.finrank_range_add_finrank_ker A.transpose.mulVecLin
  change A.transpose.rank + Module.finrank ℂ A.transpose.mulVecLin.ker = _ at hdim
  rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,Matrix.rank_transpose] at hdim
  change A.rank ≤ n-1
  omega

theorem pt_invariant_schmidt_bound {p m : ℕ}
    (Q : Matrix (Fin (p+2) × Fin m) (Fin (p+2) × Fin m) ℂ)
    (hQ : Q.PosSemidef) (hpt : partialTransposeFirst Q = Q) :
    SchmidtNumberAtMost (p+1) Q := by
  obtain ⟨psi,alpha,hsum,hrel⟩ := pt_invariant_real_hyperplane_decomposition Q hQ hpt
  refine ⟨Q.rank,psi,?_,?_⟩
  · ext i j
    simpa only [Matrix.sum_apply,pureProjector] using hsum i j
  · intro s
    have hs := schmidt_rank_lt_of_left_kernel (psi s) (alpha s) (hrel s).2.1 (hrel s).2.2
    simpa only [Nat.add_sub_cancel] using hs
end PPTQubit
#print axioms PPTQubit.pt_invariant_schmidt_bound
