import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension
open scoped BigOperators
noncomputable section
namespace PPTQubit
variable {E : Type*} [TopologicalSpace E] [T2Space E] [AddCommMonoid E]
  [Module ℝ E] [ContinuousAdd E] [ContinuousSMul ℝ E]

def boundedWeightedSums (S : Set E) (N : ℕ) (B : ℝ) : Set E :=
  {x | ∃ (c : Fin N → ℝ) (z : Fin N → E), (∀ i, c i ∈ Set.Icc 0 B) ∧
    (∀ i, z i ∈ S) ∧ x = ∑ i, c i • z i}

theorem boundedWeightedSums_compact (S : Set E) (hS : IsCompact S) (N : ℕ) (B : ℝ) :
    IsCompact (boundedWeightedSums S N B) := by
  let C : Set (Fin N → ℝ) := {c | ∀ i, c i ∈ Set.Icc 0 B}
  let Z : Set (Fin N → E) := {z | ∀ i, z i ∈ S}
  have hC : IsCompact C := isCompact_pi_infinite (fun _ => isCompact_Icc)
  have hZ : IsCompact Z := isCompact_pi_infinite (fun _ => hS)
  have hcont : Continuous (fun p : (Fin N → ℝ) × (Fin N → E) => ∑ i, p.1 i • p.2 i) := by
    apply continuous_finset_sum
    intro i hi
    exact (continuous_apply i).comp continuous_fst |>.smul ((continuous_apply i).comp continuous_snd)
  have himage := (hC.prod hZ).image hcont
  convert himage using 1
  ext x
  simp only [boundedWeightedSums, Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, C, Z]
  constructor
  · rintro ⟨c,z,hc,hz,hx⟩
    exact ⟨⟨c,z⟩,⟨hc,hz⟩,hx.symm⟩
  · rintro ⟨⟨c,z⟩,⟨hc,hz⟩,hx⟩
    exact ⟨c,z,hc,hz,hx.symm⟩

def fixedConicSums (S : Set E) (N : ℕ) : Set E :=
  {x | ∃ (c : Fin N → ℝ) (z : Fin N → E), (∀ i, 0 ≤ c i) ∧
    (∀ i, z i ∈ S) ∧ x = ∑ i, c i • z i}

theorem fixedConicSums_closed (S : Set E) (hS : IsCompact S) (N : ℕ)
    (f : E →L[ℝ] ℝ) (hpositive : ∀ z ∈ S, 1 ≤ f z) :
    IsClosed (fixedConicSums S N) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  let B := f x + 1
  let U : Set E := {y | f y < B}
  have hU : IsOpen U := isOpen_lt f.continuous continuous_const
  have hxU : x ∈ U := by simp [U, B]
  have hsub : U ∩ fixedConicSums S N ⊆ boundedWeightedSums S N B := by
    rintro y ⟨hyU,c,z,hc,hz,hy⟩
    refine ⟨c,z,fun i => ⟨hc i,?_⟩,hz,hy⟩
    have hfi (i : Fin N) : 0 ≤ f (z i) := le_trans (by norm_num) (hpositive _ (hz i))
    have hterm (i : Fin N) : c i ≤ c i * f (z i) := by
      simpa using mul_le_mul_of_nonneg_left (hpositive _ (hz i)) (hc i)
    have hbound (i : Fin N) : c i * f (z i) ≤ ∑ j, c j * f (z j) := by
      apply Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin N => c j * f (z j))
      · intro j hj
        exact mul_nonneg (hc j) (hfi j)
      · exact Finset.mem_univ i
    have hsum : f y = ∑ i, c i * f (z i) := by
      rw [hy, map_sum]
      simp
    change f y < B at hyU
    linarith [hterm i,hbound i]
  have hlocal : x ∈ closure (U ∩ fixedConicSums S N) := hU.inter_closure ⟨hxU,hx⟩
  have hb : x ∈ boundedWeightedSums S N B :=
    closure_minimal hsub (boundedWeightedSums_compact S hS N B).isClosed hlocal
  obtain ⟨c,z,hc,hz,heq⟩ := hb
  exact ⟨c,z,fun i => (hc i).1,hz,heq⟩
end PPTQubit
#print axioms PPTQubit.fixedConicSums_closed

open scoped BigOperators
noncomputable section
namespace PPTQubit
variable {E : Type*} [TopologicalSpace E] [T2Space E] [AddCommGroup E]
  [Module ℝ E] [ContinuousAdd E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]

theorem conic_compress (S : Set E) {r : ℕ} {x : E}
    (hx : x ∈ fixedConicSums S r) :
    ∃ n ≤ Module.finrank ℝ E + 1, x ∈ fixedConicSums S n := by
  classical
  obtain ⟨c,z,hc,hz,hx⟩ := hx
  let t : ℝ := ∑ i, c i
  have ht : 0 ≤ t := Finset.sum_nonneg (fun i hi => hc i)
  by_cases ht0 : t = 0
  · have hz' : ∀ i, c i = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hc i)).mp ht0
      exact fun i => h i (Finset.mem_univ i)
    refine ⟨0,by omega,?_⟩
    refine ⟨Fin.elim0,Fin.elim0,by simp,by simp,?_⟩
    rw [hx]
    simp [hz']
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let y := ∑ i, (t⁻¹ * c i) • z i
    have hy : y ∈ convexHull ℝ S := by
      apply (convex_convexHull ℝ S).sum_mem
      · intro i hi
        exact mul_nonneg (le_of_lt (inv_pos.mpr htpos)) (hc i)
      · rw [← Finset.mul_sum]
        exact inv_mul_cancel₀ ht0
      · intro i hi
        exact subset_convexHull ℝ S (hz i)
    obtain ⟨ι,inst,z',w,hz',hind,hw,hwsum,hwy⟩ := eq_pos_convex_span_of_mem_convexHull hy
    letI : Fintype ι := inst
    have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 := by
      exact le_trans hind.card_le_finrank_succ (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι,hcard,fun j => t * w (e.symm j),fun j => z' (e.symm j),?_,?_,?_⟩
    · intro j
      exact mul_nonneg ht (le_of_lt (hw _))
    · intro j
      exact hz' ⟨e.symm j,rfl⟩
    · have hreindex : (∑ j, (t * w (e.symm j)) • z' (e.symm j)) =
          ∑ i, (t * w i) • z' i := by
        symm
        apply Fintype.sum_equiv e
        intro i
        simp
      rw [hreindex]
      simp only [mul_smul]
      rw [← Finset.smul_sum]
      rw [hwy]
      dsimp [y]
      rw [hx,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [← mul_smul,ht0]
end PPTQubit
#print axioms PPTQubit.conic_compress

namespace PPTQubit
variable {E : Type*} [TopologicalSpace E] [T2Space E] [AddCommGroup E]
  [Module ℝ E] [ContinuousAdd E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]

def finiteConicHull (S : Set E) : Set E := {x | ∃ n, x ∈ fixedConicSums S n}

theorem finiteConicHull_closed (S : Set E) (hS : IsCompact S)
    (f : E →L[ℝ] ℝ) (hpos : ∀ z ∈ S, 1 ≤ f z) : IsClosed (finiteConicHull S) := by
  have heq : finiteConicHull S = ⋃ n ∈ Finset.range (Module.finrank ℝ E + 2), fixedConicSums S n := by
    ext x
    simp only [finiteConicHull,Set.mem_setOf_eq,Set.mem_iUnion,Finset.mem_range]
    constructor
    · rintro ⟨r,hr⟩
      obtain ⟨n,hn,hx⟩ := conic_compress S hr
      exact ⟨n,by omega,hx⟩
    · rintro ⟨n,hn,hx⟩
      exact ⟨n,hx⟩
  rw [heq]
  apply isClosed_biUnion_finset
  intro n hn
  exact fixedConicSums_closed S hS n f hpos
end PPTQubit
#print axioms PPTQubit.finiteConicHull_closed
