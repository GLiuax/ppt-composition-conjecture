import PPTQubit.ChoiIterated
import PPTQubit.StructuredTrimming
/-! Reduction of maximal Schmidt block structure to the remaining witness separation. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

/-- The missing separation direction for the cone of Schmidt-number-k operators. -/
def SchmidtWitnessCompleteness : Prop :=
  ∀ (n q k : ℕ) (Q : Matrix (Fin n × Fin q) (Fin n × Fin q) ℂ),
    Q.PosSemidef → ¬ SchmidtNumberAtMost k Q →
      ∃ W : Matrix (Fin n × Fin q) (Fin n × Fin q) ℂ,
        W.IsHermitian ∧ IsKBlockPositive k W ∧ (Q*W).trace.re < 0

theorem kblock_one_is_block_positive {p q : ℕ}
    (W : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)
    (hW : IsKBlockPositive 1 W) : IsBlockPositive W := by
  intro v w
  apply hW
  refine ⟨fun _ => v,fun _ => w,?_⟩
  intro i a
  simp only [Fin.sum_univ_one]

theorem block_structure_from_schmidt_witness
    (hWitness : SchmidtWitnessCompleteness) : MaximalSchmidtBlockCriterion := by
  intro n q hn hnq Q hQ hblocks
  by_contra hnot
  obtain ⟨W,hWH,hW,hnegative⟩ := hWitness n q (n-1) Q hQ hnot
  let f : Fin 2 → Fin n := fun i => ⟨i.val,by have h := i.isLt; omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun (x : Fin n) => x.val) hij
  let s0 : Fin n := f 0
  let s1 : Fin n := f 1
  have h01 : s0 ≠ s1 := by
    intro h
    have hh := hf h
    exact Fin.zero_ne_one hh
  let S : Finset (Fin n) := (Finset.univ.erase s0).erase s1
  let L : List (Fin n) := S.toList
  have hlen : L.length = n-2 := by
    simp [L,S,h01.symm]
    omega
  have hmem (i : Fin n) (hi0 : i ≠ s0) (hi1 : i ≠ s1) : i ∈ L := by
    simp [L,S,hi0,hi1]
  let T : MatrixMap n q := mapFromChoi W
  have hTH : (choi T).IsHermitian := by simpa [T] using hWH
  have hT : IsKPositiveMap ((n-2)+1) T := by
    apply choi_kblock_implies_kpositive T hTH
    change IsKBlockPositive ((n-2)+1) (choi (mapFromChoi W))
    rw [choi_mapFromChoi]
    have he : n-2+1 = n-1 := by omega
    rwa [he]
  obtain ⟨F,hF,hR,hzero⟩ := choi_decomposition_list L (n-2) T hT hTH (by omega)
  let R := T-F
  have hR1 : IsKPositiveMap 1 R := by
    have he : n-2+1-L.length = 1 := by rw [hlen]; omega
    simpa only [R,he] using hR
  have hW1 := kpositive_implies_choi_kblock R hR1
  have hblock := kblock_one_is_block_positive (choi R) hW1
  let U : Matrix (Fin n) (Fin 2) ℂ := fun i j => if i=f j then 1 else 0
  let Qf := principalTwoBlock f Q
  let Q' := localCongruence U Qf
  have hsep : IsSeparable Q' := localCongruence_separable U Qf (hblocks f hf)
  have hposF : 0 ≤ (Q * choi F).trace := psd_trace_mul_nonneg Q (choi F) hQ
    (completely_positive_choi F hF)
  have hposR : 0 ≤ (Q' * choi R).trace := separable_block_positive_trace_nonneg Q' (choi R) hsep hblock
  have htrace : (Q * choi R).trace = (Q' * choi R).trace := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type,choi]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro b _
    by_cases hi : i = s0 ∨ i = s1
    · by_cases hj : j = s0 ∨ j = s1
      · rcases hi with hi | hi <;> rcases hj with hj | hj <;> subst i <;> subst j <;>
          simp [Q',localCongruence_entry,U,Qf,principalTwoBlock,f,s0,s1,Fin.sum_univ_two]
      · have hj0 : j ≠ s0 := fun h => hj (Or.inl h)
        have hj1 : j ≠ s1 := fun h => hj (Or.inr h)
        have hz := (hzero j (hmem j hj0 hj1) i).2
        change R (Matrix.single j i 1) = 0 at hz
        simp [hz]
    · have hi0 : i ≠ s0 := fun h => hi (Or.inl h)
      have hi1 : i ≠ s1 := fun h => hi (Or.inr h)
      have hz := (hzero i (hmem i hi0 hi1) j).1
      change R (Matrix.single j i 1) = 0 at hz
      simp [hz]
  have hsum : (Q*W).trace = (Q*choi F).trace + (Q*choi R).trace := by
    have hRchoi : choi R = W - choi F := by
      dsimp only [R,T]
      rw [choi_sub,choi_mapFromChoi]
    rw [hRchoi,Matrix.mul_sub,Matrix.trace_sub]
    abel
  have hnonneg : 0 ≤ (Q*W).trace := by
    rw [hsum,htrace]
    exact add_nonneg hposF hposR
  have hh := (Complex.nonneg_iff.mp hnonneg).1
  linarith
theorem ppt_pair_trimming_of_schmidt_witness {p q r : ℕ}
    (S : MatrixMap p q) (T : MatrixMap q r) (hS : IsPPTMap S) (hT : IsPPTMap T)
    (hWitness : SchmidtWitnessCompleteness) : SchmidtTrimming (T.comp S) :=
  ppt_pair_schmidt_trimming_of_block_criterion S T hS hT (block_structure_from_schmidt_witness hWitness)

theorem ppt_index_of_schmidt_witness {d : ℕ} (T : MatrixMap d d)
    (hT : IsPPTMap T) (hd : 2 ≤ d) (hWitness : SchmidtWitnessCompleteness) :
    ∃ h : ∃ n, 0 < n ∧ IsEntanglementBreaking (T^n),
      entanglementBreakingIndex T h ≤ 2*(d-1) :=
  ppt_index_of_block_criterion T hT hd (block_structure_from_schmidt_witness hWitness)

end PPTQubit
#print axioms PPTQubit.block_structure_from_schmidt_witness

#print axioms PPTQubit.ppt_index_of_schmidt_witness
