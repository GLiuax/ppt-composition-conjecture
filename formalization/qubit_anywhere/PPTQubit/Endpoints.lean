import PPTQubit.QutritPPTAction
import PPTQubit.AuxiliaryInterface
import PPTQubit.ChoiCorrespondence

/-! The input- and output-qubit endpoint cases of PPT composition. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

/-- Every PPT map sends every qubit-reference PPT input to a separable output. -/
theorem qubit_ppt_state_endpoint {n d : ℕ} (T : MatrixMap n d) (hT : IsPPTMap T)
    (R : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ) (hR : IsPPT R) :
    IsSeparable (applySecond T R) := by
  obtain ⟨Q,hQ,hpt,hrec⟩ := qubit_ppt_auxiliary R hR
  rw [← hrec,applySecond_localCongruence]
  apply localCongruence_separable
  exact ppt_map_qutrit_invariant_separable T hT Q hQ hpt

theorem ppt_composition_qubit_input {n d : ℕ}
    (S : MatrixMap 2 n) (T : MatrixMap n d) (hS : IsPPTMap S) (hT : IsPPTMap T) :
    IsEntanglementBreaking (T.comp S) := by
  apply (entanglementBreaking_iff_choi_separable _).mpr
  rw [choi_comp]
  exact qubit_ppt_state_endpoint T hT (choi S) hS

theorem ppt_composition_qubit_output {m n : ℕ}
    (S : MatrixMap m n) (T : MatrixMap n 2) (hS : IsPPTMap S) (hT : IsPPTMap T) :
    IsEntanglementBreaking (T.comp S) := by
  apply (entanglementBreaking_iff_choi_separable _).mpr
  have hsep := qubit_ppt_state_endpoint (transposeDual S) (transposeDual_ppt S hS)
    (swapFactors (choi T)) (swapFactors_ppt (choi T) hT)
  rw [← choi_comp_transposeDual] at hsep
  simpa only [swapFactors_involutive] using swapFactors_separable _ hsep

theorem ppt_composition_endpoint {m n d : ℕ}
    (S : MatrixMap m n) (T : MatrixMap n d) (hS : IsPPTMap S) (hT : IsPPTMap T)
    (hqubit : m = 2 ∨ d = 2) : IsEntanglementBreaking (T.comp S) := by
  rcases hqubit with h | h
  · subst m
    exact ppt_composition_qubit_input S T hS hT
  · subst d
    exact ppt_composition_qubit_output S T hS hT

theorem applySecond_comp {p q r n : ℕ} (T : MatrixMap q r) (S : MatrixMap p q)
    (X : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ) :
    applySecond (T.comp S) X = applySecond T (applySecond S X) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  rfl

def IsTwoEntanglementBreaking {p q : ℕ} (T : MatrixMap p q) : Prop :=
  ∀ X : Matrix (Fin 2 × Fin p) (Fin 2 × Fin p) ℂ,
    X.PosSemidef → IsSeparable (applySecond T X)

/-- No qubit restriction on the maps. Every two-map PPT composition is 2-EB. -/
theorem ppt_composition_two_entanglement_breaking {p q r : ℕ}
    (S : MatrixMap p q) (T : MatrixMap q r) (hS : IsPPTMap S) (hT : IsPPTMap T) :
    IsTwoEntanglementBreaking (T.comp S) := by
  intro X hX
  rw [applySecond_comp]
  exact qubit_ppt_state_endpoint T hT (applySecond S X) (ppt_map_applySecond S hS X hX)

end PPTQubit
#print axioms PPTQubit.qubit_ppt_state_endpoint
#print axioms PPTQubit.ppt_composition_qubit_input
#print axioms PPTQubit.ppt_composition_qubit_output
#print axioms PPTQubit.ppt_composition_endpoint
#print axioms PPTQubit.ppt_composition_two_entanglement_breaking
