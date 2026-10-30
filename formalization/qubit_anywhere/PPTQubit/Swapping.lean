import PPTQubit.MiddleQubit
/-! Entanglement swapping for arbitrary positive joint measurement effects. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def secondFilter {p q r : ℕ} (U : Matrix (Fin q) (Fin p) ℂ)
    (Q : Matrix (Fin r × Fin p) (Fin r × Fin p) ℂ) :
    Matrix (Fin r × Fin q) (Fin r × Fin q) ℂ :=
  swapFactors (localCongruence U (swapFactors Q))

theorem secondFilter_ppt {p q r : ℕ} (U : Matrix (Fin q) (Fin p) ℂ)
    (Q : Matrix (Fin r × Fin p) (Fin r × Fin p) ℂ) (hQ : IsPPT Q) :
    IsPPT (secondFilter U Q) :=
  swapFactors_ppt _ (localCongruence_ppt U _ (swapFactors_ppt Q hQ))

theorem secondFilter_entry {p q r : ℕ} (U : Matrix (Fin q) (Fin p) ℂ)
    (Q : Matrix (Fin r × Fin p) (Fin r × Fin p) ℂ) (i j : Fin r) (a b : Fin q) :
    secondFilter U Q (i,a) (j,b) = ∑ s, ∑ t, U a s * Q (i,s) (j,t) * star (U b t) := by
  exact localCongruence_entry U (swapFactors Q) a b i j

/-- Entry formula for partial tracing the two measured systems after the effect M. -/
def swappingOutcome {a b c d : ℕ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ) :
    Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ →ₗ[ℂ]
      Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ where
  toFun M x y := ∑ p, ∑ q, ∑ r, ∑ s,
    R (x.1,p) (y.1,q) * S (r,x.2) (s,y.2) * M (q,s) (p,r)
  map_add' M N := by
    ext ⟨i,u⟩ ⟨j,v⟩
    simp only [Matrix.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' z M := by
    ext ⟨i,u⟩ ⟨j,v⟩
    simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro s _
    ring

def outcomeFilter {b c : ℕ} (eta : Fin b × Fin c → ℂ) : Matrix (Fin c) (Fin b) ℂ :=
  fun r p => star (eta (p,r))

theorem sum_four_exchange {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    (∑ p, ∑ q, ∑ r, ∑ s, f p q r s) = ∑ r, ∑ s, ∑ p, ∑ q, f p q r s := by
  calc
    _ = ∑ x : α × β, ∑ y : γ × δ, f x.1 x.2 y.1 y.2 := by simp only [Fintype.sum_prod_type]
    _ = ∑ y : γ × δ, ∑ x : α × β, f x.1 x.2 y.1 y.2 := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

theorem swapping_rank_one_left {a b c d : ℕ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ)
    (eta : Fin b × Fin c → ℂ) :
    swappingOutcome R S (pureProjector eta) =
      choi ((mapFromChoi S).comp (mapFromChoi (secondFilter (outcomeFilter eta) R))) := by
  rw [choi_comp,choi_mapFromChoi]
  ext ⟨i,u⟩ ⟨j,v⟩
  simp only [swappingOutcome,LinearMap.coe_mk,AddHom.coe_mk,applySecond,
    Matrix.submatrix_apply,mapFromChoi,secondFilter_entry,outcomeFilter,
    star_star,pureProjector,Finset.sum_mul]
  rw [sum_four_exchange]
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro q _
  ring

theorem swapping_rank_one_right {a b c d : ℕ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ)
    (eta : Fin b × Fin c → ℂ) :
    swappingOutcome R S (pureProjector eta) =
      choi ((mapFromChoi (localCongruence (outcomeFilter eta).transpose S)).comp (mapFromChoi R)) := by
  rw [choi_comp,choi_mapFromChoi]
  ext ⟨i,u⟩ ⟨j,v⟩
  simp only [swappingOutcome,LinearMap.coe_mk,AddHom.coe_mk,applySecond,
    Matrix.submatrix_apply,mapFromChoi,localCongruence_entry,outcomeFilter,
    Matrix.transpose_apply,star_star,pureProjector,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro q _
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro s _
  ring

/-- Every rank-one measurement effect gives a separable output when any of
    the four local dimensions is two. The filters can be rectangular or singular. -/
theorem swapping_rank_one_separable {a b c d : ℕ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ)
    (eta : Fin b × Fin c → ℂ) (hR : IsPPT R) (hS : IsPPT S)
    (hqubit : a = 2 ∨ b = 2 ∨ c = 2 ∨ d = 2) :
    IsSeparable (swappingOutcome R S (pureProjector eta)) := by
  have hleft (h : a = 2 ∨ c = 2 ∨ d = 2) :
      IsSeparable (swappingOutcome R S (pureProjector eta)) := by
    rw [swapping_rank_one_left]
    apply (entanglementBreaking_iff_choi_separable _).mp
    apply ppt_composition_qubit_anywhere
    · change IsPPT (choi (mapFromChoi (secondFilter (outcomeFilter eta) R)))
      rw [choi_mapFromChoi]
      exact secondFilter_ppt _ _ hR
    · change IsPPT (choi (mapFromChoi S))
      rw [choi_mapFromChoi]
      exact hS
    · exact h
  have hright (h : a = 2 ∨ b = 2 ∨ d = 2) :
      IsSeparable (swappingOutcome R S (pureProjector eta)) := by
    rw [swapping_rank_one_right]
    apply (entanglementBreaking_iff_choi_separable _).mp
    apply ppt_composition_qubit_anywhere
    · change IsPPT (choi (mapFromChoi R))
      rw [choi_mapFromChoi]
      exact hR
    · change IsPPT (choi (mapFromChoi (localCongruence (outcomeFilter eta).transpose S)))
      rw [choi_mapFromChoi]
      exact localCongruence_ppt _ _ hS
    · exact h
  rcases hqubit with ha | hb | hc | hd
  · exact hleft (Or.inl ha)
  · exact hright (Or.inr (Or.inl hb))
  · exact hleft (Or.inr (Or.inl hc))
  · exact hleft (Or.inr (Or.inr hd))

/-- The swapping state is separable for every positive joint effect. -/
theorem swapping_positive_effect_separable {a b c d : ℕ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ)
    (M : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)
    (hR : IsPPT R) (hS : IsPPT S) (hM : M.PosSemidef)
    (hqubit : a = 2 ∨ b = 2 ∨ c = 2 ∨ d = 2) :
    IsSeparable (swappingOutcome R S M) := by
  obtain ⟨k,eta,hMsum⟩ := positive_pure_expansion M hM
  rw [hMsum,map_sum]
  exact separable_finite_sum _ (fun i => swapping_rank_one_separable R S (eta i) hR hS hqubit)

def relayEffectLift {a b c d : ℕ}
    (M : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ) :
    Matrix ((Fin a × Fin b) × (Fin c × Fin d))
      ((Fin a × Fin b) × (Fin c × Fin d)) ℂ := fun x y =>
  (1 : Matrix (Fin a) (Fin a) ℂ) x.1.1 y.1.1 * M (x.1.2,x.2.1) (y.1.2,y.2.1) *
    (1 : Matrix (Fin d) (Fin d) ℂ) x.2.2 y.2.2

def traceRelay {a b c d : ℕ}
    (X : Matrix ((Fin a × Fin b) × (Fin c × Fin d))
      ((Fin a × Fin b) × (Fin c × Fin d)) ℂ) :
    Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ := fun x y =>
  ∑ p : Fin b, ∑ r : Fin c, X ((x.1,p),(r,x.2)) ((y.1,p),(r,y.2))

theorem swappingOutcome_partial_trace {a b c d : ℕ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ)
    (M : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ) :
    swappingOutcome R S M = traceRelay (Matrix.kronecker R S * relayEffectLift (a := a) (d := d) M) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [swappingOutcome,traceRelay,relayEffectLift,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.one_apply,apply_ite]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]

end PPTQubit

#print axioms PPTQubit.swapping_positive_effect_separable
#print axioms PPTQubit.swappingOutcome_partial_trace
