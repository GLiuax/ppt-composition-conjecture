import PPTQubit.StructuredTrimming
/-! A precise formal target for the block-structure result and its maximal case. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def principalBlock {n q k : ℕ} (f : Fin k → Fin n)
    (Q : Matrix (Fin n × Fin q) (Fin n × Fin q) ℂ) :
    Matrix (Fin k × Fin q) (Fin k × Fin q) ℂ :=
  Q.submatrix (fun x => (f x.1,x.2)) (fun x => (f x.1,x.2))

/-- The nonvacuous l ≥ 2 cases of the block-structure theorem A.2.
This declaration is a proposition to be proved, not a Lean axiom. -/
def PrincipalBlockStructure : Prop :=
  ∀ (n q : ℕ) (Q : Matrix (Fin n × Fin q) (Fin n × Fin q) ℂ)
    (hQ : Q.PosSemidef) (l k : ℕ), n ≤ q → 2 ≤ l → l ≤ schmidtNumber Q hQ → k + l = n + 2 →
    ∀ (f : Fin k → Fin n), Function.Injective f →
      ¬ SchmidtNumberAtMost (schmidtNumber Q hQ - l + 1) (principalBlock f Q)

theorem block_structure_implies_maximal_criterion
    (hBlock : PrincipalBlockStructure) : MaximalSchmidtBlockCriterion := by
  intro n q hn hnq Q hQ hblocks
  by_contra hnot
  have hge : n ≤ schmidtNumber Q hQ := by
    by_contra hn'
    have hh : schmidtNumber Q hQ ≤ n-1 := by omega
    exact hnot ((schmidtNumber_le_iff Q hQ).mp hh)
  have hle : schmidtNumber Q hQ ≤ n :=
    (schmidtNumber_le_iff Q hQ).mpr (positive_schmidt_bound_reference Q hQ)
  have he : schmidtNumber Q hQ = n := by omega
  let f : Fin 2 → Fin n := fun i => ⟨i.val, by have h := i.isLt; omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg (fun (x : Fin n) => x.val) hij
    exact hv
  have hsep := hblocks f hf
  have hgen : ∀ (g : Fin 2 → Fin n), Function.Injective g →
      ¬ SchmidtNumberAtMost (schmidtNumber Q hQ - n + 1) (principalBlock g Q) := by
    exact hBlock n q Q hQ n 2 hnq (by omega) (by omega) (by omega)
  apply hgen f hf
  rw [he,Nat.sub_self,Nat.zero_add,schmidt_one_iff_separable]
  exact hsep

/-- Once the published block theorem is proved, PPT pairs trim unconditionally
with respect to all other hypotheses. -/
theorem ppt_pair_trimming_of_block_structure {p q r : ℕ}
    (S : MatrixMap p q) (T : MatrixMap q r) (hS : IsPPTMap S) (hT : IsPPTMap T)
    (hBlock : PrincipalBlockStructure) : SchmidtTrimming (T.comp S) :=
  ppt_pair_schmidt_trimming_of_block_criterion S T hS hT (block_structure_implies_maximal_criterion hBlock)

theorem ppt_index_of_block_structure {d : ℕ} (T : MatrixMap d d)
    (hT : IsPPTMap T) (hd : 2 ≤ d) (hBlock : PrincipalBlockStructure) :
    ∃ h : ∃ n, 0 < n ∧ IsEntanglementBreaking (T^n),
      entanglementBreakingIndex T h ≤ 2*(d-1) :=
  ppt_index_of_block_criterion T hT hd (block_structure_implies_maximal_criterion hBlock)

end PPTQubit
#print axioms PPTQubit.block_structure_implies_maximal_criterion

#print axioms PPTQubit.ppt_index_of_block_structure
