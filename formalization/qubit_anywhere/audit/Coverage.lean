import PPTQubit
import audit.Semantics

/-! Boundary checks for the newly completed manuscript coverage. -/
open Matrix PPTQubit
open scoped ComplexOrder
noncomputable section
namespace PPTAudit

/-- An odd-length chain uses the smaller output dimension, with all
intermediate dimensions different and larger than two. -/
theorem odd_chain_output_endpoint
    (S : MatrixMap 5 7) (T : MatrixMap 7 8) (U : MatrixMap 8 2)
    (hS : IsPPTMap S) (hT : IsPPTMap T) (hU : IsPPTMap U) :
    IsEntanglementBreaking (U.comp (T.comp S)) := by
  let C : PPTChain 3 5 2 := .snoc (.snoc (.snoc (.nil 5) S hS) T hT) U hU
  have h := C.entanglement_breaking_rectangular (by decide)
  simpa [C,PPTChain.toMap,LinearMap.comp_assoc] using h

/-- Zero effect is included even when none of the four local dimensions is two. -/
theorem zero_effect_no_qubit
    (R : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ)
    (S : Matrix (Fin 6 × Fin 7) (Fin 6 × Fin 7) ℂ)
    (hR : IsPPT R) (hS : IsPPT S) :
    IsSeparable (swappingOutcome R S (0 : Matrix (Fin 5 × Fin 6) (Fin 5 × Fin 6) ℂ)) := by
  apply swapping_schmidt_two_effect R S _ hR hS
  exact schmidtCone_zero

/-- A three-dimensional principal block in a four-dimensional reference
is covered by the general theorem, beyond the previous two-block case. -/
theorem general_three_by_three_block
    (Q : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ) (hQ : Q.PosSemidef)
    (hs : 3 ≤ schmidtNumber Q hQ) :
    ¬ SchmidtNumberAtMost (schmidtNumber Q hQ - 3 + 1)
      (principalBlock (Fin.castLE (by decide : 3 ≤ 4)) Q) := by
  exact principal_block_structure 4 6 Q hQ 3 3 (by decide) (by decide) hs (by decide)
    _ (Fin.castLE_injective _)

end PPTAudit
#print axioms PPTAudit.odd_chain_output_endpoint
#print axioms PPTAudit.zero_effect_no_qubit
#print axioms PPTAudit.general_three_by_three_block
