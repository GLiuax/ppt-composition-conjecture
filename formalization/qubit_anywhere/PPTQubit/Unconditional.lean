import PPTQubit.SchmidtFiniteCone
import PPTQubit.WitnessClosed
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Closedness removes the witness assumption from the PPT-pair descent and its iterates. -/
open Matrix
open scoped ComplexOrder
noncomputable section
namespace PPTQubit

theorem schmidtCone_closed {a b k : ℕ} :
    IsClosed (SchmidtCone (a := a) (b := b) k) := by
  rw [schmidtCone_eq_finiteConicHull]
  apply finiteConicHull_closed _ schmidt_unit_projectors_compact realTrace
  rintro z ⟨u,hu,rfl⟩
  exact unit_projector_realTrace_lower hu.1

theorem allSchmidtConesClosed : ∀ a b k : ℕ,
    IsClosed (SchmidtCone (a := a) (b := b) k) :=
  fun _ _ _ => schmidtCone_closed

theorem schmidt_witness_complete : SchmidtWitnessCompleteness :=
  schmidt_witness_complete_of_closed_cones allSchmidtConesClosed

theorem maximal_schmidt_block_criterion : MaximalSchmidtBlockCriterion :=
  block_structure_from_schmidt_witness schmidt_witness_complete

theorem ppt_pair_trimming {p q r : ℕ} (S : MatrixMap p q) (T : MatrixMap q r)
    (hS : IsPPTMap S) (hT : IsPPTMap T) : SchmidtTrimming (T.comp S) :=
  ppt_pair_trimming_of_closed_schmidt_cones allSchmidtConesClosed S T hS hT

theorem PPTPairChain.schmidt_iteration
    {l p q : ℕ} (C : PPTPairChain l p q)
    (n k : ℕ) (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ)
    (hQ : SchmidtNumberAtMost k Q) :
    SchmidtNumberAtMost (max (k-l) 1) (applySecond C.toMap Q) :=
  C.schmidt_iteration_of_closed_cones allSchmidtConesClosed n k Q hQ

theorem PPTPairChain.schmidt_number_decay
    {l p q n : ℕ} (C : PPTPairChain l p q)
    (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ) (hQ : Q.PosSemidef) :
    ∃ hOut : (applySecond C.toMap Q).PosSemidef,
      schmidtNumber (applySecond C.toMap Q) hOut ≤ max (schmidtNumber Q hQ-l) 1 := by
  have h := C.schmidt_iteration n (schmidtNumber Q hQ) Q (schmidtNumber_spec Q hQ)
  exact ⟨schmidt_number_positive _ h, (schmidtNumber_le_iff _ _).mpr h⟩

theorem PPTPairChain.entanglement_breaking
    {l p q : ℕ} (C : PPTPairChain l p q) (hbound : p ≤ l+1) :
    IsEntanglementBreaking C.toMap :=
  C.entanglement_breaking_of_closed_cones allSchmidtConesClosed hbound

theorem PPTPairChain.ancilla_bound
    {l p q : ℕ} (C : PPTPairChain l p q) :
    IsKEntanglementBreaking (l+1) C.toMap := by
  have h := (C.toTrimChain allSchmidtConesClosed).ancilla_bound
  rwa [C.toTrimChain_toMap allSchmidtConesClosed] at h

theorem ppt_power_entanglement_breaking {d : ℕ} (T : MatrixMap d d)
    (hT : IsPPTMap T) (hd : 2 ≤ d) :
    IsEntanglementBreaking (T ^ (2*(d-1))) :=
  square_power_entanglement_breaking_of_trimming T (ppt_pair_trimming T T hT hT) hd

theorem ppt_index_bound {d : ℕ} (T : MatrixMap d d) (hT : IsPPTMap T)
    (hd : 2 ≤ d) :
    ∃ h : ∃ n, 0 < n ∧ IsEntanglementBreaking (T^n),
      entanglementBreakingIndex T h ≤ 2*(d-1) :=
  ppt_index_of_closed_schmidt_cones allSchmidtConesClosed T hT hd

end PPTQubit
#print axioms PPTQubit.schmidtCone_closed
#print axioms PPTQubit.maximal_schmidt_block_criterion
#print axioms PPTQubit.ppt_pair_trimming
#print axioms PPTQubit.PPTPairChain.schmidt_iteration
#print axioms PPTQubit.PPTPairChain.schmidt_number_decay
#print axioms PPTQubit.PPTPairChain.entanglement_breaking
#print axioms PPTQubit.PPTPairChain.ancilla_bound
#print axioms PPTQubit.ppt_power_entanglement_breaking
#print axioms PPTQubit.ppt_index_bound
