import PPTQubit.Schmidt
/-! Schmidt-number iteration for maps with a proved one-step trimming property.
The general implication from 2-EB to this property is a separate theorem. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def SchmidtTrimming {p q : ℕ} (T : MatrixMap p q) : Prop :=
  ∀ (n k : ℕ) (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ),
    SchmidtNumberAtMost k Q → SchmidtNumberAtMost (max (k-1) 1) (applySecond T Q)

/-- The one-step property is already unconditional when the input space has
at most two dimensions. -/
theorem two_eb_trimming_small_input {p q : ℕ} (T : MatrixMap p q)
    (hT : IsTwoEntanglementBreaking T) (hp : p ≤ 2) : SchmidtTrimming T := by
  intro n k Q hQ
  have hsmall : SchmidtNumberAtMost 2 Q := schmidt_number_mono Q
    (positive_schmidt_bound_system Q (schmidt_number_positive Q hQ)) hp
  have hsep := two_eb_schmidt_two T hT Q hsmall
  exact schmidt_number_mono _ ((schmidt_one_iff_separable _).mpr hsep) (by omega)

def IsKEntanglementBreaking {p q : ℕ} (k : ℕ) (T : MatrixMap p q) : Prop :=
  ∀ Q : Matrix (Fin k × Fin p) (Fin k × Fin p) ℂ,
    Q.PosSemidef → IsSeparable (applySecond T Q)

inductive TrimChain : ℕ → ℕ → ℕ → Type where
  | nil (p : ℕ) : TrimChain 0 p p
  | snoc {l p q r : ℕ} (C : TrimChain l p q) (T : MatrixMap q r)
      (hT : SchmidtTrimming T) : TrimChain (l+1) p r

def TrimChain.toMap : {l p q : ℕ} → TrimChain l p q → MatrixMap p q
  | _, _, _, .nil _ => LinearMap.id
  | _, _, _, .snoc C T _ => T.comp C.toMap

theorem applySecond_id {p n : ℕ} (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ) :
    applySecond (LinearMap.id : MatrixMap p p) Q = Q := by
  ext ⟨i,a⟩ ⟨j,b⟩
  rfl

theorem trim_bound_step (k l : ℕ) : max (max (k-l) 1 - 1) 1 = max (k-(l+1)) 1 := by omega

theorem TrimChain.schmidt_iteration {l p q : ℕ} (C : TrimChain l p q)
    (n k : ℕ) (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ)
    (hQ : SchmidtNumberAtMost k Q) :
    SchmidtNumberAtMost (max (k-l) 1) (applySecond C.toMap Q) := by
  induction C with
  | nil p =>
      rw [TrimChain.toMap,applySecond_id]
      apply schmidt_number_mono Q hQ
      omega
  | @snoc l p q r C T hT ih =>
      rw [TrimChain.toMap,applySecond_comp,← trim_bound_step]
      exact hT n (max (k-l) 1) _ (ih Q hQ)

theorem TrimChain.entanglement_breaking {l p q : ℕ} (C : TrimChain l p q)
    (hbound : p ≤ l+1) : IsEntanglementBreaking C.toMap := by
  apply (entanglementBreaking_iff_choi_separable C.toMap).mpr
  let P := pureProjector (vectorize (1 : Matrix (Fin p) (Fin p) ℂ))
  have hP : SchmidtNumberAtMost p P := positive_schmidt_bound_reference P (pureProjector_positive _)
  have h := C.schmidt_iteration p p P hP
  have hb : max (p-l) 1 = 1 := by omega
  rw [hb,schmidt_one_iff_separable] at h
  have hc : applySecond C.toMap P = choi C.toMap := by
    dsimp only [P]
    rw [applySecond_pure_choi,Matrix.transpose_one,localCongruence_identity]
  rwa [hc] at h

theorem TrimChain.ancilla_bound {l p q : ℕ} (C : TrimChain l p q) :
    IsKEntanglementBreaking (l+1) C.toMap := by
  intro Q hQ
  have h := C.schmidt_iteration (l+1) (l+1) Q (positive_schmidt_bound_reference Q hQ)
  have hb : max ((l+1)-l) 1 = 1 := by omega
  rw [hb,schmidt_one_iff_separable] at h
  exact h

def TrimChain.repeat {p : ℕ} (T : MatrixMap p p) (hT : SchmidtTrimming T) :
    (l : ℕ) → TrimChain l p p
  | 0 => .nil p
  | l+1 => .snoc (TrimChain.repeat T hT l) T hT

theorem TrimChain.repeat_toMap {p : ℕ} (T : MatrixMap p p) (hT : SchmidtTrimming T)
    (l : ℕ) : (TrimChain.repeat T hT l).toMap = T^l := by
  induction l with
  | zero => rfl
  | succ l ih =>
      change T.comp (TrimChain.repeat T hT l).toMap = T^(l+1)
      rw [ih,pow_succ]
      change T * T^l = T^l * T
      exact (Commute.self_pow T l).eq

/-- Conditional index bound: the remaining task is to prove trimming for a
PPT pair; no trimming result is assumed globally or introduced as an axiom. -/
theorem square_power_entanglement_breaking_of_trimming {d : ℕ}
    (T : MatrixMap d d) (htrim : SchmidtTrimming (T.comp T)) (hd : 2 ≤ d) :
    IsEntanglementBreaking (T ^ (2*(d-1))) := by
  have h := (TrimChain.repeat (T.comp T) htrim (d-1)).entanglement_breaking (by omega)
  rw [TrimChain.repeat_toMap] at h
  have heq : T.comp T = T^2 := by
    ext X
    simp [pow_two,Module.End.mul_apply]
  rw [heq,← pow_mul] at h
  exact h
/-- The least positive exponent is defined when an EB power has been proved. -/
def entanglementBreakingIndex {d : ℕ} (T : MatrixMap d d)
    (h : ∃ n, 0 < n ∧ IsEntanglementBreaking (T^n)) : ℕ := by
  classical
  exact Nat.find h

theorem square_index_bound_of_trimming {d : ℕ} (T : MatrixMap d d)
    (htrim : SchmidtTrimming (T.comp T)) (hd : 2 ≤ d) :
    ∃ h : ∃ n, 0 < n ∧ IsEntanglementBreaking (T^n),
      entanglementBreakingIndex T h ≤ 2*(d-1) := by
  classical
  have hpower := square_power_entanglement_breaking_of_trimming T htrim hd
  let h : ∃ n, 0 < n ∧ IsEntanglementBreaking (T^n) := ⟨2*(d-1),by omega,hpower⟩
  refine ⟨h,?_⟩
  exact Nat.find_min' h ⟨by omega,hpower⟩

theorem ppt_qubit_square_entanglement_breaking (T : MatrixMap 2 2) (hT : IsPPTMap T) :
    IsEntanglementBreaking (T^2) := by
  have h := ppt_composition_qubit_middle T T hT hT
  have heq : T.comp T = T^2 := by
    ext X i j
    simp [pow_two,Module.End.mul_apply]
  rwa [heq] at h

theorem ppt_qubit_index_bound (T : MatrixMap 2 2) (hT : IsPPTMap T) :
    ∃ h : ∃ n, 0 < n ∧ IsEntanglementBreaking (T^n),
      entanglementBreakingIndex T h ≤ 2 := by
  classical
  have hpow := ppt_qubit_square_entanglement_breaking T hT
  let h : ∃ n, 0 < n ∧ IsEntanglementBreaking (T^n) := ⟨2,by norm_num,hpow⟩
  exact ⟨h,Nat.find_min' h ⟨by norm_num,hpow⟩⟩

end PPTQubit
#print axioms PPTQubit.TrimChain.schmidt_iteration
#print axioms PPTQubit.square_power_entanglement_breaking_of_trimming

#print axioms PPTQubit.TrimChain.ancilla_bound
#print axioms PPTQubit.square_index_bound_of_trimming

#print axioms PPTQubit.ppt_qubit_index_bound
