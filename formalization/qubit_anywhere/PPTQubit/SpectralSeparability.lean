import PPTQubit.SpectralTools
import PPTQubit.SeparableTensor
/-! Positive spectral grids and separability of tensor differences squared. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem realSpectral_tensor {a b : ℕ} (U : Matrix (Fin a) (Fin a) ℂ)
    (V : Matrix (Fin b) (Fin b) ℂ) (f : Fin a → ℝ) (g : Fin b → ℝ) :
    realSpectral (Matrix.kronecker U V) (fun i => f i.1 * g i.2) =
    Matrix.kronecker (realSpectral U f) (realSpectral V g) := by
  simp only [realSpectral,Matrix.kronecker,Matrix.conjTranspose_kronecker,
    Matrix.mul_kronecker_mul,Matrix.diagonal_kronecker_diagonal,Complex.ofReal_mul]

theorem separable_spectral_grid {a b : ℕ} (U : Matrix (Fin a) (Fin a) ℂ)
    (V : Matrix (Fin b) (Fin b) ℂ) (f : Fin a × Fin b → ℝ) (hf : ∀ i, 0 ≤ f i) :
    IsSeparable (realSpectral (Matrix.kronecker U V) f) := by
  let e : Fin (a*b) ≃ Fin a × Fin b := finProdFinEquiv.symm
  refine ⟨a*b,fun k i => (Real.sqrt (f (e k)) : ℂ) * U i (e k).1,
    fun k j => V j (e k).2,?_⟩
  intro i a j b
  have he : ∀ x y, realSpectral (Matrix.kronecker U V) f x y =
      ∑ s, ((Matrix.kronecker U V) x s * (f s : ℂ)) * star ((Matrix.kronecker U V) y s) := by
    intro x y
    simp [realSpectral,Matrix.mul_apply,Matrix.diagonal_apply,Matrix.conjTranspose_apply]
  rw [he,← e.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  have hs : (Real.sqrt (f (e k)) : ℂ) * (Real.sqrt (f (e k)) : ℂ) = (f (e k) : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (hf _)]
  change (U i (e k).1 * V a (e k).2 * (f (e k) : ℂ)) * star (U j (e k).1 * V b (e k).2) = _
  rw [← hs]
  simp only [StarMul.star_mul,Complex.star_def,Complex.conj_ofReal]
  ring

theorem separable_tensor_difference_square {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    IsSeparable ((Matrix.kronecker A (1 : Matrix (Fin b) (Fin b) ℂ) -
      Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) B) *
      (Matrix.kronecker A (1 : Matrix (Fin b) (Fin b) ℂ) -
      Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) B)) := by
  obtain ⟨U,f,hU,hU',rfl⟩ := hermitian_spectral_representation A hA
  obtain ⟨V,g,hV,hV',rfl⟩ := hermitian_spectral_representation B hB
  have hL : (Matrix.kronecker U V).conjTranspose * Matrix.kronecker U V = 1 := by
    simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,
      hU,hV,Matrix.one_kronecker_one]
  have hleft : Matrix.kronecker (realSpectral U f) (1 : Matrix (Fin b) (Fin b) ℂ) =
      realSpectral (Matrix.kronecker U V) (fun i => f i.1) := by
    simpa only [mul_one,realSpectral_one V hV'] using (realSpectral_tensor U V f (fun _ => 1)).symm
  have hright : Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (realSpectral V g) =
      realSpectral (Matrix.kronecker U V) (fun i => g i.2) := by
    simpa only [one_mul,realSpectral_one U hU'] using (realSpectral_tensor U V (fun _ => 1) g).symm
  rw [hleft,hright,← realSpectral_sub,realSpectral_mul _ hL]
  apply separable_spectral_grid
  intro i
  exact mul_self_nonneg _
end PPTQubit