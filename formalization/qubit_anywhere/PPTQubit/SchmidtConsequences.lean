import PPTQubit.SchmidtNumber
import PPTQubit.SchmidtIteration
/-! Numeric versions of the Schmidt conclusions; iteration retains its explicit trimming premise. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem TrimChain.schmidt_number_decay {l p q : ℕ} (C : TrimChain l p q)
    {n : ℕ} (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ)
    (hQ : Q.PosSemidef) (hOut : (applySecond C.toMap Q).PosSemidef) :
    schmidtNumber (applySecond C.toMap Q) hOut ≤ max (schmidtNumber Q hQ-l) 1 := by
  apply (schmidtNumber_le_iff _ hOut).mpr
  exact C.schmidt_iteration n (schmidtNumber Q hQ) Q (schmidtNumber_spec Q hQ)

theorem ppt_pair_schmidt_number_two {p q r n : ℕ} (S : MatrixMap p q) (T : MatrixMap q r)
    (hS : IsPPTMap S) (hT : IsPPTMap T)
    (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ)
    (hQ : Q.PosSemidef) (hSN : schmidtNumber Q hQ ≤ 2) :
    ∃ hOut : (applySecond (T.comp S) Q).PosSemidef,
      schmidtNumber (applySecond (T.comp S) Q) hOut ≤ 1 := by
  have hOut : (applySecond (T.comp S) Q).PosSemidef := by
    rw [applySecond_comp]
    exact (ppt_map_applySecond T hT (applySecond S Q) (ppt_map_applySecond S hS Q hQ).1).1
  refine ⟨hOut,?_⟩
  apply (schmidtNumber_le_one_iff_separable _ hOut).mpr
  exact ppt_pair_schmidt_two S T hS hT Q ((schmidtNumber_le_iff Q hQ).mp hSN)
end PPTQubit
#print axioms PPTQubit.TrimChain.schmidt_number_decay
#print axioms PPTQubit.ppt_pair_schmidt_number_two
