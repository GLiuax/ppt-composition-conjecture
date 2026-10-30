import PPTQubit.SchmidtConsequences
/-! Reduction of Schmidt trimming to a maximal-Schmidt block criterion. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

/-- Every two-dimensional compression on the reference factor is separable. -/
def TwoDimensionalCompressionsSeparable {n q : ℕ}
    (Q : Matrix (Fin n × Fin q) (Fin n × Fin q) ℂ) : Prop :=
  ∀ U : Matrix (Fin 2) (Fin n) ℂ, IsSeparable (localCongruence U Q)

def principalTwoBlock {n q : ℕ} (f : Fin 2 → Fin n)
    (Q : Matrix (Fin n × Fin q) (Fin n × Fin q) ℂ) :
    Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℂ :=
  Q.submatrix (fun x => (f x.1,x.2)) (fun x => (f x.1,x.2))

def PrincipalTwoBlocksSeparable {n q : ℕ}
    (Q : Matrix (Fin n × Fin q) (Fin n × Fin q) ℂ) : Prop :=
  ∀ f : Fin 2 → Fin n, Function.Injective f → IsSeparable (principalTwoBlock f Q)

/-- The maximal-Schmidt special case of the block-structure theorem.
This is a proposition, not an axiom; results using it state the premise. -/
def MaximalSchmidtBlockCriterion : Prop :=
  ∀ (n q : ℕ), 3 ≤ n → n ≤ q →
    ∀ Q : Matrix (Fin n × Fin q) (Fin n × Fin q) ℂ,
      Q.PosSemidef → PrincipalTwoBlocksSeparable Q →
      SchmidtNumberAtMost (n-1) Q

theorem two_eb_output_compressions {p q n : ℕ} (T : MatrixMap p q)
    (hT : IsTwoEntanglementBreaking T)
    (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ) (hQ : Q.PosSemidef) :
    TwoDimensionalCompressionsSeparable (applySecond T Q) := by
  intro U
  rw [← applySecond_localCongruence]
  exact hT _ (hQ.mul_mul_conjTranspose_same (localLift U))

theorem two_eb_output_principal_blocks {p q n : ℕ} (T : MatrixMap p q)
    (hT : IsTwoEntanglementBreaking T)
    (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ) (hQ : Q.PosSemidef) :
    PrincipalTwoBlocksSeparable (applySecond T Q) := by
  intro f hf
  have he : principalTwoBlock f (applySecond T Q) = applySecond T (principalTwoBlock f Q) := by
    ext ⟨i,a⟩ ⟨j,b⟩
    rfl
  rw [he]
  exact hT _ (hQ.submatrix _)

theorem completely_positive_comp {p q r : ℕ} (S : MatrixMap p q) (T : MatrixMap q r)
    (hS : IsCompletelyPositiveMap S) (hT : IsCompletelyPositiveMap T) :
    IsCompletelyPositiveMap (T.comp S) := by
  intro n Q hQ
  rw [applySecond_comp]
  exact hT n _ (hS n Q hQ)

/-- The small-Schmidt and smaller-output ranges need no block theorem. -/
theorem two_eb_trimming_easy_ranges {p q n k : ℕ} (T : MatrixMap p q)
    (hT : IsCompletelyPositiveMap T) (h2 : IsTwoEntanglementBreaking T)
    (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ)
    (hQ : SchmidtNumberAtMost k Q) (heasy : k ≤ 2 ∨ q < k) :
    SchmidtNumberAtMost (max (k-1) 1) (applySecond T Q) := by
  rcases heasy with hsmall | hlarge
  · have h2Q : SchmidtNumberAtMost 2 Q := schmidt_number_mono Q hQ hsmall
    have hsep := two_eb_schmidt_two T h2 Q h2Q
    exact schmidt_number_mono _ ((schmidt_one_iff_separable _).mpr hsep) (by omega)
  · have hY := hT n Q (schmidt_number_positive Q hQ)
    exact schmidt_number_mono _ (positive_schmidt_bound_system _ hY) (by omega)

theorem ppt_pair_trimming_easy_ranges {p q r n k : ℕ} (S : MatrixMap p q) (T : MatrixMap q r)
    (hS : IsPPTMap S) (hT : IsPPTMap T)
    (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ)
    (hQ : SchmidtNumberAtMost k Q) (heasy : k ≤ 2 ∨ r < k) :
    SchmidtNumberAtMost (max (k-1) 1) (applySecond (T.comp S) Q) :=
  two_eb_trimming_easy_ranges _
    (completely_positive_comp S T (ppt_map_completely_positive S hS) (ppt_map_completely_positive T hT))
    (ppt_composition_two_entanglement_breaking S T hS hT) Q hQ heasy

theorem ppt_pair_numeric_easy_ranges {p q r n : ℕ} (S : MatrixMap p q) (T : MatrixMap q r)
    (hS : IsPPTMap S) (hT : IsPPTMap T)
    (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ) (hQ : Q.PosSemidef)
    (heasy : schmidtNumber Q hQ ≤ 2 ∨ r < schmidtNumber Q hQ) :
    ∃ hOut : (applySecond (T.comp S) Q).PosSemidef,
      schmidtNumber (applySecond (T.comp S) Q) hOut ≤ max (schmidtNumber Q hQ-1) 1 := by
  have hOut : (applySecond (T.comp S) Q).PosSemidef := by
    rw [applySecond_comp]
    exact (ppt_map_applySecond T hT _ (ppt_map_applySecond S hS Q hQ).1).1
  refine ⟨hOut,?_⟩
  apply (schmidtNumber_le_iff _ hOut).mpr
  exact ppt_pair_trimming_easy_ranges S T hS hT Q (schmidtNumber_spec Q hQ) heasy

/-- A CP, 2-EB map trims Schmidt number once the block criterion is supplied. -/
theorem two_eb_schmidt_trimming_of_block_criterion {p q : ℕ} (T : MatrixMap p q)
    (hT : IsCompletelyPositiveMap T) (h2 : IsTwoEntanglementBreaking T)
    (hBlock : MaximalSchmidtBlockCriterion) : SchmidtTrimming T := by
  intro n k Q hQ
  by_cases hk : k ≤ 2
  · have h2Q : SchmidtNumberAtMost 2 Q := schmidt_number_mono Q hQ hk
    have hsep := two_eb_schmidt_two T h2 Q h2Q
    exact schmidt_number_mono _ ((schmidt_one_iff_separable _).mpr hsep) (by omega)
  · have hk3 : 3 ≤ k := by omega
    have htarget : max (k-1) 1 = k-1 := by omega
    rw [htarget]
    obtain ⟨r,z,hQ,hz⟩ := hQ
    rw [hQ,map_sum]
    apply schmidt_number_finite_sum
    intro t
    obtain ⟨v,w,hv⟩ := hz t
    let U : Matrix (Fin n) (Fin k) ℂ := fun a i => v i a
    let z' : Fin k × Fin p → ℂ := fun x => w x.1 x.2
    have he : z t = fun x => ∑ i, U x.1 i * z' (i,x.2) := by
      funext ⟨i,a⟩
      exact hv i a
    rw [he,← localCongruence_pure,applySecond_localCongruence]
    apply schmidt_number_local_first
    have hY : (applySecond T (pureProjector z')).PosSemidef :=
      hT k _ (pureProjector_positive z')
    by_cases hsmall : k ≤ q
    · exact hBlock k q hk3 hsmall _ hY
        (two_eb_output_principal_blocks T h2 _ (pureProjector_positive z'))
    · exact schmidt_number_mono _ (positive_schmidt_bound_system _ hY) (by omega)

theorem ppt_pair_schmidt_trimming_of_block_criterion {p q r : ℕ}
    (S : MatrixMap p q) (T : MatrixMap q r) (hS : IsPPTMap S) (hT : IsPPTMap T)
    (hBlock : MaximalSchmidtBlockCriterion) : SchmidtTrimming (T.comp S) :=
  two_eb_schmidt_trimming_of_block_criterion _
    (completely_positive_comp S T (ppt_map_completely_positive S hS) (ppt_map_completely_positive T hT))
    (ppt_composition_two_entanglement_breaking S T hS hT) hBlock

theorem ppt_index_of_block_criterion {d : ℕ} (T : MatrixMap d d)
    (hT : IsPPTMap T) (hd : 2 ≤ d) (hBlock : MaximalSchmidtBlockCriterion) :
    ∃ h : ∃ n, 0 < n ∧ IsEntanglementBreaking (T^n),
      entanglementBreakingIndex T h ≤ 2*(d-1) :=
  square_index_bound_of_trimming T (ppt_pair_schmidt_trimming_of_block_criterion T T hT hT hBlock) hd
end PPTQubit
#print axioms PPTQubit.two_eb_schmidt_trimming_of_block_criterion
#print axioms PPTQubit.ppt_index_of_block_criterion

#print axioms PPTQubit.ppt_pair_trimming_easy_ranges

#print axioms PPTQubit.ppt_pair_numeric_easy_ranges
