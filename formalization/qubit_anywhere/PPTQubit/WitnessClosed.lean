import PPTQubit.RealDualWitness
import PPTQubit.BlockWitness
/-! Closedness of each Schmidt-number cone supplies the missing witness. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem schmidt_witness_of_closed_cone {n q k : ℕ}
    (hclosed : IsClosed (SchmidtCone (a := n) (b := q) k))
    (Q : Matrix (Fin n × Fin q) (Fin n × Fin q) ℂ)
    (hQ : Q.PosSemidef) (hnot : ¬ SchmidtNumberAtMost k Q) :
    ∃ W : Matrix (Fin n × Fin q) (Fin n × Fin q) ℂ,
      W.IsHermitian ∧ IsKBlockPositive k W ∧ (Q*W).trace.re < 0 := by
  letI : LocallyConvexSpace ℝ (Matrix (Fin n × Fin q) (Fin n × Fin q) ℂ) := by
    change LocallyConvexSpace ℝ ((Fin n × Fin q) → (Fin n × Fin q) → ℂ)
    infer_instance
  have hscale : ∀ (c : ℝ), 0 ≤ c → ∀ Y ∈ SchmidtCone (a := n) (b := q) k,
      c • Y ∈ SchmidtCone k := by
    intro c hc Y hY
    exact schmidt_number_real_smul Y hY c hc
  obtain ⟨f,hneg,hpos⟩ := closed_cone_strict_separation (SchmidtCone k)
    schmidtCone_convex hclosed schmidtCone_zero hscale Q hnot
  obtain ⟨W,hWH,hpair⟩ := real_linear_hermitian_witness f.toLinearMap
  refine ⟨W,hWH,?_,?_⟩
  · intro z hz
    have hzQ : SchmidtNumberAtMost k (pureProjector z) := by
      refine ⟨1,fun _ => z,?_,fun _ => hz⟩
      simp only [Fin.sum_univ_one]
    have hp := hpos (pureProjector z) hzQ
    change 0 ≤ f.toLinearMap (pureProjector z) at hp
    rw [hpair _ (pureProjector_positive z).isHermitian,rank_one_trace_pairing] at hp
    exact Complex.nonneg_iff.mpr ⟨hp,(hWH.im_star_dotProduct_mulVec_self z).symm⟩
  · change f.toLinearMap Q < 0 at hneg
    rwa [← hpair Q hQ.isHermitian]

theorem schmidt_witness_complete_of_closed_cones
    (hclosed : ∀ n q k : ℕ, IsClosed (SchmidtCone (a := n) (b := q) k)) :
    SchmidtWitnessCompleteness := by
  intro n q k Q hQ hnot
  exact schmidt_witness_of_closed_cone (hclosed n q k) Q hQ hnot

theorem ppt_index_of_closed_schmidt_cones
    (hclosed : ∀ n q k : ℕ, IsClosed (SchmidtCone (a := n) (b := q) k))
    {d : ℕ} (T : MatrixMap d d) (hT : IsPPTMap T) (hd : 2 ≤ d) :
    ∃ h : ∃ n, 0 < n ∧ IsEntanglementBreaking (T^n),
      entanglementBreakingIndex T h ≤ 2*(d-1) :=
  ppt_index_of_schmidt_witness T hT hd (schmidt_witness_complete_of_closed_cones hclosed)
end PPTQubit
#print axioms PPTQubit.schmidt_witness_of_closed_cone
#print axioms PPTQubit.ppt_index_of_closed_schmidt_cones
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem ppt_pair_trimming_of_closed_schmidt_cones
    (hclosed : ∀ n q k : ℕ, IsClosed (SchmidtCone (a := n) (b := q) k))
    {p q r : ℕ} (S : MatrixMap p q) (T : MatrixMap q r)
    (hS : IsPPTMap S) (hT : IsPPTMap T) : SchmidtTrimming (T.comp S) :=
  ppt_pair_trimming_of_schmidt_witness S T hS hT
    (schmidt_witness_complete_of_closed_cones hclosed)

inductive PPTPairChain : ℕ → ℕ → ℕ → Type where
  | nil (p : ℕ) : PPTPairChain 0 p p
  | snoc {l p q r s : ℕ} (C : PPTPairChain l p q)
      (S : MatrixMap q r) (T : MatrixMap r s)
      (hS : IsPPTMap S) (hT : IsPPTMap T) : PPTPairChain (l+1) p s

def PPTPairChain.toTrimChain
    (hclosed : ∀ n q k : ℕ, IsClosed (SchmidtCone (a := n) (b := q) k)) :
    {l p q : ℕ} → PPTPairChain l p q → TrimChain l p q
  | _, _, _, .nil p => .nil p
  | _, _, _, .snoc C S T hS hT =>
      .snoc (C.toTrimChain hclosed) (T.comp S)
        (ppt_pair_trimming_of_closed_schmidt_cones hclosed S T hS hT)

def PPTPairChain.toMap : {l p q : ℕ} → PPTPairChain l p q → MatrixMap p q
  | _, _, _, .nil _ => LinearMap.id
  | _, _, _, .snoc C S T _ _ => (T.comp S).comp C.toMap

theorem PPTPairChain.toTrimChain_toMap
    (hclosed : ∀ n q k : ℕ, IsClosed (SchmidtCone (a := n) (b := q) k))
    {l p q : ℕ} (C : PPTPairChain l p q) : (C.toTrimChain hclosed).toMap = C.toMap := by
  induction C with
  | nil => rfl
  | snoc C S T hS hT ih =>
      change (T.comp S).comp (C.toTrimChain hclosed).toMap = (T.comp S).comp C.toMap
      rw [ih]

theorem PPTPairChain.schmidt_iteration_of_closed_cones
    (hclosed : ∀ n q k : ℕ, IsClosed (SchmidtCone (a := n) (b := q) k))
    {l p q : ℕ} (C : PPTPairChain l p q)
    (n k : ℕ) (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ)
    (hQ : SchmidtNumberAtMost k Q) :
    SchmidtNumberAtMost (max (k-l) 1) (applySecond C.toMap Q) := by
  have h := (C.toTrimChain hclosed).schmidt_iteration n k Q hQ
  rwa [C.toTrimChain_toMap hclosed] at h

theorem PPTPairChain.entanglement_breaking_of_closed_cones
    (hclosed : ∀ n q k : ℕ, IsClosed (SchmidtCone (a := n) (b := q) k))
    {l p q : ℕ} (C : PPTPairChain l p q) (hbound : p ≤ l+1) :
    IsEntanglementBreaking C.toMap := by
  have h := (C.toTrimChain hclosed).entanglement_breaking hbound
  rwa [C.toTrimChain_toMap hclosed] at h
end PPTQubit
#print axioms PPTQubit.PPTPairChain.schmidt_iteration_of_closed_cones
