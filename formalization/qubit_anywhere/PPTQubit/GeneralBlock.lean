import PPTQubit.Unconditional
import PPTQubit.BlockStructure
/-! General principal-block Schmidt-number structure. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem principalBlock_embed_entry {n q k : ℕ} (f : Fin k → Fin n)
    (hf : Function.Injective f)
    (Q : Matrix (Fin n × Fin q) (Fin n × Fin q) ℂ)
    (i j : Fin k) (a b : Fin q) :
    localCongruence (fun x t => if x = f t then 1 else 0 : Matrix (Fin n) (Fin k) ℂ)
      (principalBlock f Q) (f i,a) (f j,b) = Q (f i,a) (f j,b) := by
  simp [localCongruence_entry,principalBlock,hf.eq_iff,apply_ite]

theorem principal_block_structure : PrincipalBlockStructure := by
  classical
  intro n q Q hQ l k hnq hl hs hk f hf
  let r := schmidtNumber Q hQ
  have hrn : r ≤ n := (schmidtNumber_le_iff Q hQ).mpr (positive_schmidt_bound_reference Q hQ)
  have hkn : k ≤ n := by omega
  by_contra hblock
  have hnot : ¬ SchmidtNumberAtMost (r-1) Q := by
    intro hh
    have hs' : r ≤ r-1 := (schmidtNumber_le_iff Q hQ).mpr hh
    omega
  obtain ⟨W,hWH,hW,hnegative⟩ := schmidt_witness_complete n q (r-1) Q hQ hnot
  let S : Finset (Fin n) := Finset.univ \ (Finset.univ.image f)
  let L : List (Fin n) := S.toList
  have hlen : L.length = n-k := by
    simp [L,S,Finset.card_sdiff,Finset.card_image_of_injective _ hf]
  have hmem (i : Fin n) (hi : i ∉ Finset.univ.image f) : i ∈ L := by
    simp [L,S,hi]
  let T : MatrixMap n q := mapFromChoi W
  have hTH : (choi T).IsHermitian := by simpa [T] using hWH
  have hT : IsKPositiveMap ((r-2)+1) T := by
    apply choi_kblock_implies_kpositive T hTH
    change IsKBlockPositive ((r-2)+1) (choi (mapFromChoi W))
    rw [choi_mapFromChoi]
    have he : r-2+1 = r-1 := by dsimp [r] at *; omega
    rwa [he]
  obtain ⟨F,hF,hR,hzero⟩ := choi_decomposition_list L (r-2) T hT hTH (by rw [hlen]; dsimp [r] at *; omega)
  let R := T-F
  have hR1 : IsKPositiveMap (r-l+1) R := by
    have he : r-2+1-L.length = r-l+1 := by rw [hlen]; dsimp [r] at *; omega
    simpa only [R,he] using hR
  have hW1 := kpositive_implies_choi_kblock R hR1
  let U : Matrix (Fin n) (Fin k) ℂ := fun i j => if i=f j then 1 else 0
  let Qf := principalBlock f Q
  let Q' := localCongruence U Qf
  have hQ' : SchmidtNumberAtMost (r-l+1) Q' := schmidt_number_local_first U Qf hblock
  have hposF : 0 ≤ (Q * choi F).trace := psd_trace_mul_nonneg Q (choi F) hQ
    (completely_positive_choi F hF)
  have hposR : 0 ≤ (Q' * choi R).trace := (kblock_iff_schmidt_pairing_nonnegative (choi R)).mp hW1 Q' hQ'
  have htrace : (Q * choi R).trace = (Q' * choi R).trace := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type,choi]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro b _
    by_cases hi : i ∈ Finset.univ.image f
    · by_cases hj : j ∈ Finset.univ.image f
      · obtain ⟨i',_,rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨j',_,rfl⟩ := Finset.mem_image.mp hj
        simp only [Q',Qf,U,principalBlock_embed_entry f hf Q]
      · have hz := (hzero j (hmem j hj) i).2
        change R (Matrix.single j i 1) = 0 at hz
        simp [hz]
    · have hz := (hzero i (hmem i hi) j).1
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
end PPTQubit
#print axioms PPTQubit.principal_block_structure
