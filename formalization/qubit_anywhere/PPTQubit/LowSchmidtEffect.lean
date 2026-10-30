import PPTQubit.Unconditional
import PPTQubit.Adjoint
/-! Swapping for measurement effects of Schmidt number at most two. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem sum_six_exchange {α β γ δ ε ζ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε] [Fintype ζ]
    (f : α → β → γ → δ → ε → ζ → ℂ) :
    (∑ p, ∑ q, ∑ r, ∑ s, ∑ t, ∑ u, f p q r s t u) =
      ∑ t, ∑ u, ∑ r, ∑ s, ∑ p, ∑ q, f p q r s t u := by
  calc
    _ = ∑ r, ∑ s, ∑ p, ∑ q, ∑ t, ∑ u, f p q r s t u := sum_four_exchange _
    _ = ∑ r, ∑ s, ∑ t, ∑ u, ∑ p, ∑ q, f p q r s t u := by
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro s _
      exact sum_four_exchange _
    _ = _ := sum_four_exchange _

theorem swapping_schmidt_two_rank_one {a b c d : ℕ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ)
    (eta : Fin b × Fin c → ℂ) (hR : IsPPT R) (hS : IsPPT S)
    (heta : SchmidtRankAtMost 2 eta) :
    IsSeparable (swappingOutcome R S (pureProjector eta)) := by
  obtain ⟨v,w,hv⟩ := heta
  let V : Matrix (Fin 2) (Fin b) ℂ := fun i p => star (v i p)
  let U : Matrix (Fin 2) (Fin c) ℂ := fun i r => star (w i r)
  have he : swappingOutcome R S (pureProjector eta) =
      qubitLink (swapFactors (secondFilter V R)) (localCongruence U S) := by
    ext ⟨i,x⟩ ⟨j,y⟩
    simp only [swappingOutcome,LinearMap.coe_mk,AddHom.coe_mk,pureProjector,hv,
      star_sum,StarMul.star_mul,qubitLink,Matrix.sum_apply,Matrix.kronecker,
      Matrix.kroneckerMap_apply,qubitBlock,Matrix.submatrix_apply,swapFactors,
      Prod.swap_prod_mk,secondFilter_entry,localCongruence_entry,V,U,star_star]
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [sum_six_exchange]
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro u _
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring
  rw [he]
  exact qubitLink_ppt_separable _ _ (swapFactors_ppt _ (secondFilter_ppt _ _ hR))
    (localCongruence_ppt _ _ hS)

theorem swapping_schmidt_two_effect {a b c d : ℕ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ)
    (M : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)
    (hR : IsPPT R) (hS : IsPPT S) (hM : SchmidtNumberAtMost 2 M) :
    IsSeparable (swappingOutcome R S M) := by
  obtain ⟨k,eta,hMsum,heta⟩ := hM
  rw [hMsum,map_sum]
  exact separable_finite_sum _ (fun i => swapping_schmidt_two_rank_one R S (eta i) hR hS (heta i))
theorem swapping_schmidt_number_two_effect {a b c d : ℕ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ)
    (M : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)
    (hR : IsPPT R) (hS : IsPPT S) (hM : M.PosSemidef)
    (hSN : schmidtNumber M hM ≤ 2) :
    IsSeparable (swappingOutcome R S M) :=
  swapping_schmidt_two_effect R S M hR hS ((schmidtNumber_le_iff M hM).mp hSN)
end PPTQubit
#print axioms PPTQubit.swapping_schmidt_number_two_effect
#print axioms PPTQubit.swapping_schmidt_two_effect
