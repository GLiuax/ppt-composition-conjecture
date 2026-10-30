import PPTQubit.Unconditional
import PPTQubit.Adjoint
/-! Arbitrary-length PPT chains and both endpoint dimensions. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

inductive PPTChain : ℕ → ℕ → ℕ → Type where
  | nil (p : ℕ) : PPTChain 0 p p
  | snoc {N p q r : ℕ} (C : PPTChain N p q) (T : MatrixMap q r)
      (hT : IsPPTMap T) : PPTChain (N+1) p r

def PPTChain.toMap : {N p q : ℕ} → PPTChain N p q → MatrixMap p q
  | _, _, _, .nil _ => LinearMap.id
  | _, _, _, .snoc C T _ => T.comp C.toMap

theorem PPTChain.schmidt_iteration {N p q : ℕ} (C : PPTChain N p q)
    (n k : ℕ) (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ)
    (hQ : SchmidtNumberAtMost k Q) :
    SchmidtNumberAtMost (max (k-N/2) 1) (applySecond C.toMap Q) := by
  induction N using Nat.strong_induction_on generalizing p q with
  | h N ih =>
    cases C with
    | nil =>
      rw [PPTChain.toMap, applySecond_id]
      exact schmidt_number_mono Q hQ (by omega)
    | @snoc N p r q C T hT =>
      cases C with
      | nil =>
        rw [PPTChain.toMap,PPTChain.toMap,LinearMap.comp_id]
        apply schmidt_number_mono _ (completely_positive_preserves_schmidt_number T
          (ppt_map_completely_positive T hT) Q hQ)
        omega
      | @snoc m p s r C S hS =>
        have h := ih m (by omega) C Q hQ
        rw [PPTChain.toMap,PPTChain.toMap,← LinearMap.comp_assoc,applySecond_comp]
        have hh := ppt_pair_trimming S T hS hT n (max (k-m/2) 1) _ h
        have he : max (max (k-m/2) 1 - 1) 1 = max (k-((m+2)/2)) 1 := by omega
        rwa [he] at hh

theorem PPTChain.entanglement_breaking_input {N p q : ℕ} (C : PPTChain N p q)
    (hbound : p ≤ N/2+1) : IsEntanglementBreaking C.toMap := by
  apply (entanglementBreaking_iff_choi_separable C.toMap).mpr
  let P := pureProjector (vectorize (1 : Matrix (Fin p) (Fin p) ℂ))
  have hP : SchmidtNumberAtMost p P := positive_schmidt_bound_reference P (pureProjector_positive _)
  have h := C.schmidt_iteration p p P hP
  have hb : max (p-N/2) 1 = 1 := by omega
  rw [hb,schmidt_one_iff_separable] at h
  have hc : applySecond C.toMap P = choi C.toMap := by
    dsimp only [P]
    rw [applySecond_pure_choi,Matrix.transpose_one,localCongruence_identity]
  rwa [hc] at h

theorem separable_conjugate {p q : ℕ}
    (Q : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ) (hQ : IsSeparable Q) :
    IsSeparable (Q.map star) := by
  obtain ⟨r,v,w,hQ⟩ := hQ
  refine ⟨r,fun s i => star (v s i),fun s i => star (w s i),?_⟩
  intro i a j b
  simp only [Matrix.map_apply,hQ,star_sum,StarMul.star_mul,star_star]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem hsAdjoint_involutive {p q : ℕ} (T : MatrixMap p q) :
    hsAdjoint (hsAdjoint T) = T := by
  unfold hsAdjoint
  rw [choi_mapFromChoi]
  have he : (swapFactors ((swapFactors (choi T)).map star)).map star = choi T := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp [swapFactors]
  rw [he,mapFromChoi_choi]

theorem hsAdjoint_entanglement_breaking {p q : ℕ} (T : MatrixMap p q)
    (hT : IsEntanglementBreaking T) : IsEntanglementBreaking (hsAdjoint T) := by
  apply (entanglementBreaking_iff_choi_separable _).mpr
  change IsSeparable (choi (mapFromChoi ((swapFactors (choi T)).map star)))
  rw [choi_mapFromChoi]
  exact separable_conjugate _ (swapFactors_separable _ ((entanglementBreaking_iff_choi_separable T).mp hT))

theorem hsAdjoint_entanglement_breaking_iff {p q : ℕ} (T : MatrixMap p q) :
    IsEntanglementBreaking (hsAdjoint T) ↔ IsEntanglementBreaking T := by
  constructor
  · intro h
    have hh := hsAdjoint_entanglement_breaking (hsAdjoint T) h
    rwa [hsAdjoint_involutive] at hh
  · exact hsAdjoint_entanglement_breaking T

def PPTChain.prepend {p q : ℕ} (T : MatrixMap p q) (hT : IsPPTMap T) :
    {N r : ℕ} → PPTChain N q r → PPTChain (N+1) p r
  | _, _, .nil _ => .snoc (.nil p) T hT
  | _, _, .snoc C S hS => .snoc (C.prepend T hT) S hS

theorem PPTChain.prepend_toMap {N p q r : ℕ} (C : PPTChain N q r)
    (T : MatrixMap p q) (hT : IsPPTMap T) :
    (C.prepend T hT).toMap = C.toMap.comp T := by
  induction C with
  | nil => simp [PPTChain.prepend,PPTChain.toMap]
  | snoc C S hS ih => simp [PPTChain.prepend,PPTChain.toMap,ih,LinearMap.comp_assoc]

def PPTChain.reverseAdjoint : {N p q : ℕ} → PPTChain N p q → PPTChain N q p
  | _, _, _, .nil p => .nil p
  | _, _, _, .snoc C T hT => (C.reverseAdjoint).prepend (hsAdjoint T) (hsAdjoint_ppt T hT)

theorem PPTChain.reverseAdjoint_toMap {N p q : ℕ} (C : PPTChain N p q) :
    C.reverseAdjoint.toMap = hsAdjoint C.toMap := by
  induction C with
  | nil p =>
    have h : hsAdjoint (LinearMap.id : MatrixMap p p) = LinearMap.id := by
      ext X i j
      have hh := hsAdjoint_pairing (LinearMap.id : MatrixMap p p) (Matrix.single i j 1) X
      simpa [hsPair_single] using hh.symm
    simpa [PPTChain.reverseAdjoint,PPTChain.toMap] using h.symm
  | snoc C T hT ih =>
    rw [PPTChain.reverseAdjoint,PPTChain.prepend_toMap,ih,PPTChain.toMap,hsAdjoint_comp]

theorem PPTChain.entanglement_breaking_output {N p q : ℕ} (C : PPTChain N p q)
    (hbound : q ≤ N/2+1) : IsEntanglementBreaking C.toMap := by
  apply (hsAdjoint_entanglement_breaking_iff C.toMap).mp
  rw [← C.reverseAdjoint_toMap]
  exact C.reverseAdjoint.entanglement_breaking_input hbound

theorem PPTChain.entanglement_breaking_rectangular {N p q : ℕ} (C : PPTChain N p q)
    (hbound : 2*(min p q - 1) ≤ N) : IsEntanglementBreaking C.toMap := by
  rcases le_total p q with hpq | hqp
  · apply C.entanglement_breaking_input
    rw [min_eq_left hpq] at hbound
    omega
  · apply C.entanglement_breaking_output
    rw [min_eq_right hqp] at hbound
    omega

end PPTQubit
#print axioms PPTQubit.PPTChain.entanglement_breaking_rectangular
#print axioms PPTQubit.PPTChain.schmidt_iteration
#print axioms PPTQubit.PPTChain.entanglement_breaking_input
