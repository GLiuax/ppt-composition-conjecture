import PPTQubit

/-! Independent formulation checks and exact boundary examples for the audit. -/
open Matrix PPTQubit
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTAudit

def partialTransposeSecond {p q : ℕ}
    (Q : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ) :
    Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ :=
  fun i j : Fin p × Fin q => Q (i.1,j.2) (j.1,i.2)

theorem ppt_iff_second_transpose {p q : ℕ}
    (Q : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ) :
    IsPPT Q ↔ Q.PosSemidef ∧ (partialTransposeSecond Q).PosSemidef := by
  have he : partialTransposeSecond Q = (partialTransposeFirst Q).transpose := rfl
  rw [he]
  constructor
  · intro h
    exact ⟨h.1,h.2.transpose⟩
  · intro h
    exact ⟨h.1,by simpa using h.2.transpose⟩

def outputTranspose {p q : ℕ} (T : MatrixMap p q) : MatrixMap p q where
  toFun A := (T A).transpose
  map_add' A B := by simp
  map_smul' c A := by simp

theorem outputTranspose_action {p q n : ℕ} (T : MatrixMap p q)
    (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ) :
    applySecond (outputTranspose T) Q = partialTransposeSecond (applySecond T Q) := rfl

theorem ppt_map_iff_cp_and_ccp {p q : ℕ} (T : MatrixMap p q) :
    IsPPTMap T ↔ IsCompletelyPositiveMap T ∧ IsCompletelyPositiveMap (outputTranspose T) := by
  constructor
  · intro h
    refine ⟨ppt_map_completely_positive T h,?_⟩
    intro n Q hQ
    rw [outputTranspose_action]
    exact ((ppt_iff_second_transpose _).mp (ppt_map_applySecond T h Q hQ)).2
  · rintro ⟨hcp,hccp⟩
    rw [ppt_map_iff_complete_ppt]
    intro n Q hQ
    apply (ppt_iff_second_transpose _).mpr
    exact ⟨hcp n Q hQ,by simpa only [outputTranspose_action] using hccp n Q hQ⟩

def bell : Fin 2 × Fin 2 → ℂ := fun x => if x.1 = x.2 then 1 else 0

theorem bell_positive : (pureProjector bell).PosSemidef := pureProjector_positive bell

theorem bell_not_ppt : ¬ IsPPT (pureProjector bell) := by
  intro h
  let z : Fin 2 × Fin 2 → ℂ := fun x => if x = (0,1) then 1 else if x = (1,0) then -1 else 0
  have hz := h.2.dotProduct_mulVec_nonneg z
  have he : star z ⬝ᵥ (partialTransposeFirst (pureProjector bell)).mulVec z = (-2 : ℂ) := by
    norm_num [z,bell,partialTransposeFirst,pureProjector,Matrix.mulVec,dotProduct,
      Fintype.sum_prod_type,Fin.sum_univ_two]
  rw [he] at hz
  have hr := (Complex.nonneg_iff.mp hz).1
  norm_num at hr

theorem bell_not_separable : ¬ IsSeparable (pureProjector bell) :=
  fun h => bell_not_ppt (separable_ppt _ h)

theorem bell_schmidt_number_two : schmidtNumber (pureProjector bell) bell_positive = 2 := by
  have hu : schmidtNumber (pureProjector bell) bell_positive ≤ 2 :=
    (schmidtNumber_le_iff _ _).mpr (positive_schmidt_bound_reference _ bell_positive)
  have hl : ¬ schmidtNumber (pureProjector bell) bell_positive ≤ 1 := by
    intro h
    exact bell_not_separable ((schmidtNumber_le_one_iff_separable _ _).mp h)
  omega

theorem identity_cp : IsCompletelyPositiveMap (LinearMap.id : MatrixMap 2 2) := by
  intro n Q hQ
  simpa only [applySecond_id] using hQ

theorem identity_choi : choi (LinearMap.id : MatrixMap 2 2) = pureProjector bell := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [choi,pureProjector,bell]

theorem identity_not_ppt : ¬ IsPPTMap (LinearMap.id : MatrixMap 2 2) := by
  change ¬ IsPPT (choi (LinearMap.id : MatrixMap 2 2))
  rw [identity_choi]
  exact bell_not_ppt

theorem identity_not_eb : ¬ IsEntanglementBreaking (LinearMap.id : MatrixMap 2 2) := by
  intro h
  have hs := h 2 (pureProjector bell) bell_positive
  rw [applySecond_id] at hs
  exact bell_not_separable hs

def productVector : Fin 2 × Fin 2 → ℂ :=
  fun x => (if x.1 = 0 then 1 else 0) * (if x.2 = 0 then 1 else 0)

theorem product_separable : IsSeparable (pureProjector productVector) := by
  refine ⟨1,fun _ i => if i=0 then 1 else 0,fun _ i => if i=0 then 1 else 0,?_⟩
  intro i a j b
  simp [pureProjector,productVector]

theorem nonzero_ppt_map_exists : ∃ T : MatrixMap 2 2, IsPPTMap T ∧ T ≠ 0 := by
  refine ⟨mapFromChoi (pureProjector productVector),?_,?_⟩
  · change IsPPT (choi (mapFromChoi _))
    rw [choi_mapFromChoi]
    exact separable_ppt _ product_separable
  · intro hz
    have hh := congrArg (fun T : MatrixMap 2 2 => choi T (0,0) (0,0)) hz
    change choi (mapFromChoi (pureProjector productVector)) (0,0) (0,0) = 0 at hh
    rw [choi_mapFromChoi] at hh
    norm_num [pureProjector,productVector,choi] at hh

theorem zero_effect_outcome {a b c d : ℕ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ) : swappingOutcome R S 0 = 0 := map_zero _

theorem zero_schmidt_iff {a b : ℕ}
    (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hQ : Q.PosSemidef) :
    schmidtNumber Q hQ = 0 ↔ Q = 0 := by
  rw [← Nat.le_zero,schmidtNumber_le_iff]
  change Q ∈ SchmidtCone 0 ↔ Q = 0
  rw [schmidtCone_zero_eq_singleton]
  rfl

end PPTAudit
#print axioms PPTAudit.ppt_map_iff_cp_and_ccp
#print axioms PPTAudit.bell_not_ppt
#print axioms PPTAudit.identity_not_ppt
#print axioms PPTAudit.zero_schmidt_iff

#print axioms PPTAudit.bell_schmidt_number_two
#print axioms PPTAudit.identity_not_eb
#print axioms PPTAudit.nonzero_ppt_map_exists
