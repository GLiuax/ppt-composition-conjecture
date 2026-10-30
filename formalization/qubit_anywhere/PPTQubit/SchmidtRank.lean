import PPTQubit.Schmidt
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem schmidt_rank_of_matrix_rank {a b k : ℕ} (z : Fin a × Fin b → ℂ)
    (hz : Matrix.rank (show Matrix (Fin a) (Fin b) ℂ from fun i j => z (i,j)) ≤ k) :
    SchmidtRankAtMost k z := by
  let A : Matrix (Fin a) (Fin b) ℂ := fun i j => z (i,j)
  let W := Submodule.span ℂ (Set.range A.col)
  let r := Module.finrank ℂ W
  have hr : r ≤ k := by
    change Module.finrank ℂ (Submodule.span ℂ (Set.range A.col)) ≤ k
    rw [← Matrix.rank_eq_finrank_span_cols]
    exact hz
  let B := Module.finBasis ℂ W
  let c : Fin b → W := fun j => ⟨A.col j, Submodule.subset_span ⟨j,rfl⟩⟩
  have hk : SchmidtRankAtMost r z := by
    refine ⟨fun t i => (B t).val i,fun t j => B.repr (c j) t,?_⟩
    intro i j
    have he := congrArg (fun x : W => x.val i) (B.sum_repr (c j))
    simp only [Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,
      smul_eq_mul,c,A,Matrix.col_apply] at he
    simpa only [mul_comm] using he.symm
  exact schmidt_rank_mono z hk hr

theorem schmidt_rank_iff_matrix_rank {a b k : ℕ} (z : Fin a × Fin b → ℂ) :
    SchmidtRankAtMost k z ↔
      Matrix.rank (show Matrix (Fin a) (Fin b) ℂ from fun i j => z (i,j)) ≤ k :=
  ⟨schmidt_rank_matrix_bound z,schmidt_rank_of_matrix_rank z⟩
end PPTQubit
#print axioms PPTQubit.schmidt_rank_iff_matrix_rank
