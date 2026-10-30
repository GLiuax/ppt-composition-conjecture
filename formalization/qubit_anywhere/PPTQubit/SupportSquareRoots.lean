import PPTQubit.SpectralTools
/-! Square roots and generalized inverse square roots on the full marginal space. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem positive_support_square_roots {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.PosSemidef) :
    ∃ B J P : Matrix n n ℂ,
      B.IsHermitian ∧ J.IsHermitian ∧ P.IsHermitian ∧
      B * B = M ∧ B * J = P ∧ J * B = P ∧
      P * P = P ∧ M * P = M ∧ J * M * J = P ∧
      B * P = B ∧ (1 - P).PosSemidef := by
  obtain ⟨U,f,hU,hU',hMf⟩ := hermitian_spectral_representation M hM.isHermitian
  have hf : ∀ i, 0 ≤ f i := realSpectral_nonnegative U hU f (hMf ▸ hM)
  let b : n → ℝ := fun i => Real.sqrt (f i)
  let j : n → ℝ := fun i => (b i)⁻¹
  let p : n → ℝ := fun i => b i * j i
  have hbb : ∀ i, b i * b i = f i := fun i => Real.mul_self_sqrt (hf i)
  have hbp : ∀ i, b i * p i = b i := by
    intro i
    dsimp [p,j]
    by_cases h : b i = 0 <;> simp [h]
  have hpp : ∀ i, p i * p i = p i := by
    intro i
    dsimp [p,j]
    by_cases h : b i = 0 <;> simp [h]
  have hmp : ∀ i, f i * p i = f i := by
    intro i
    rw [← hbb i,mul_assoc,hbp]
  have hjmj : ∀ i, j i * f i * j i = p i := by
    intro i
    rw [← hbb i]
    dsimp [p,j]
    by_cases h : b i = 0
    · simp [h]
    · field_simp
  refine ⟨realSpectral U b,realSpectral U j,realSpectral U p,
    realSpectral_hermitian _ _,realSpectral_hermitian _ _,realSpectral_hermitian _ _,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [realSpectral_mul U hU,hMf]
    congr 1; funext i; exact hbb i
  · exact realSpectral_mul U hU b j
  · rw [realSpectral_mul U hU]
    congr 1; funext i; exact mul_comm _ _
  · rw [realSpectral_mul U hU]
    congr 1; funext i; exact hpp i
  · rw [hMf,realSpectral_mul U hU]
    congr 1; funext i; exact hmp i
  · rw [hMf,realSpectral_mul U hU,realSpectral_mul U hU]
    congr 1; funext i; exact hjmj i
  · rw [realSpectral_mul U hU]
    congr 1; funext i; exact hbp i
  · rw [← realSpectral_one U hU',← realSpectral_sub]
    apply realSpectral_positive
    intro i
    dsimp [p,j]
    by_cases h : b i = 0 <;> simp [h]
end PPTQubit