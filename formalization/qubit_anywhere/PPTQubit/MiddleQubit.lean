import PPTQubit.QubitLink
/-! The middle-qubit branch and the complete qubit-anywhere PPT-composition theorem. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem qubitLink_choi_comp {m d : ℕ} (S : MatrixMap m 2) (T : MatrixMap 2 d) :
    qubitLink (swapFactors (choi S)) (choi T) = choi (T.comp S) := by
  ext ⟨a,c⟩ ⟨b,d⟩
  change (∑ i, ∑ j, Matrix.kronecker (qubitBlock (swapFactors (choi S)) i j)
    (qubitBlock (choi T) i j)) (a,c) (b,d) = _
  simp only [Matrix.sum_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,qubitBlock,
    Matrix.submatrix_apply,swapFactors,choi,Prod.swap_prod_mk,LinearMap.comp_apply]
  exact (map_entry_expansion T (S (Matrix.single a b 1)) c d).symm

/-- The middle-qubit branch. Both endpoints are unrestricted; no trace,
unitality, invertibility, or rank assumptions are needed. -/
theorem ppt_composition_qubit_middle {m d : ℕ} (S : MatrixMap m 2) (T : MatrixMap 2 d)
    (hS : IsPPTMap S) (hT : IsPPTMap T) : IsEntanglementBreaking (T.comp S) := by
  apply (entanglementBreaking_iff_choi_separable (T.comp S)).mpr
  rw [← qubitLink_choi_comp]
  exact qubitLink_ppt_separable _ _ (swapFactors_ppt _ hS) hT

/-- The complete qubit-anywhere PPT-composition main theorem. -/
theorem ppt_composition_qubit_anywhere {m n d : ℕ} (S : MatrixMap m n) (T : MatrixMap n d)
    (hS : IsPPTMap S) (hT : IsPPTMap T) (hqubit : m = 2 ∨ n = 2 ∨ d = 2) :
    IsEntanglementBreaking (T.comp S) := by
  rcases hqubit with hm | hn | hd
  · subst m
    exact ppt_composition_qubit_input S T hS hT
  · subst n
    exact ppt_composition_qubit_middle S T hS hT
  · subst d
    exact ppt_composition_qubit_output S T hS hT
end PPTQubit
#print axioms PPTQubit.ppt_composition_qubit_middle
#print axioms PPTQubit.ppt_composition_qubit_anywhere
