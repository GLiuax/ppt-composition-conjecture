import PPTQubit.Endpoints
/-! Spectral calculus for positive contractions and Hermitian absolute parts. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def realSpectral {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (f : n → ℝ) : Matrix n n ℂ :=
  U * Matrix.diagonal (fun i => (f i : ℂ)) * U.conjTranspose

theorem realSpectral_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (f : n → ℝ) : (realSpectral U f).IsHermitian := by
  have hd : (Matrix.diagonal (fun i => (f i : ℂ))).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  change (U * Matrix.diagonal (fun i => (f i : ℂ)) * U.conjTranspose).conjTranspose = _
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hd]
  simp only [realSpectral,Matrix.mul_assoc]

theorem realSpectral_positive {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (f : n → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (realSpectral U f).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.nonneg_iff.mpr ⟨hf i,rfl⟩

theorem realSpectral_add {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (f g : n → ℝ) :
    realSpectral U (fun i => f i + g i) = realSpectral U f + realSpectral U g := by
  have hd : Matrix.diagonal (fun i => ((f i + g i : ℝ) : ℂ)) = Matrix.diagonal (fun i => (f i : ℂ)) + Matrix.diagonal (fun i => (g i : ℂ)) := by
    ext i j; simp [Matrix.diagonal_apply]; split_ifs <;> simp
  simp only [realSpectral,hd,Matrix.mul_add,Matrix.add_mul]

theorem realSpectral_sub {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (f g : n → ℝ) :
    realSpectral U (fun i => f i - g i) = realSpectral U f - realSpectral U g := by
  have hd : Matrix.diagonal (fun i => ((f i - g i : ℝ) : ℂ)) = Matrix.diagonal (fun i => (f i : ℂ)) - Matrix.diagonal (fun i => (g i : ℂ)) := by
    ext i j; simp [Matrix.diagonal_apply]; split_ifs <;> simp
  simp only [realSpectral,hd,Matrix.mul_sub,Matrix.sub_mul]

theorem realSpectral_one {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U * U.conjTranspose = 1) :
    realSpectral U (fun _ => 1) = 1 := by
  simpa [realSpectral] using hU

theorem realSpectral_mul {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U.conjTranspose * U = 1) (f g : n → ℝ) :
    realSpectral U f * realSpectral U g = realSpectral U (fun i => f i * g i) := by
  let F := Matrix.diagonal (fun i => (f i : ℂ))
  let G := Matrix.diagonal (fun i => (g i : ℂ))
  have hFG : F * G = Matrix.diagonal (fun i => ((f i * g i : ℝ) : ℂ)) := by
    simp only [F,G,Matrix.diagonal_mul_diagonal,Complex.ofReal_mul]
  change (U * F * U.conjTranspose) * (U * G * U.conjTranspose) = _
  calc
    _ = U * F * (U.conjTranspose * U) * G * U.conjTranspose := by noncomm_ring
    _ = realSpectral U (fun i => f i * g i) := by rw [hU,Matrix.mul_one,Matrix.mul_assoc U F G,hFG]; rfl

theorem realSpectral_nonnegative {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U.conjTranspose * U = 1) (f : n → ℝ)
    (hf : (realSpectral U f).PosSemidef) : ∀ i, 0 ≤ f i := by
  have hd : U.conjTranspose * realSpectral U f * U = Matrix.diagonal (fun i => (f i : ℂ)) := by
    dsimp only [realSpectral]
    calc
      _ = (U.conjTranspose * U) * Matrix.diagonal (fun i => (f i : ℂ)) * (U.conjTranspose * U) := by noncomm_ring
      _ = _ := by rw [hU,Matrix.one_mul,Matrix.mul_one]
  have hh := hf.conjTranspose_mul_mul_same U
  rw [hd] at hh
  intro i
  have h := hh.diag_nonneg (i := i)
  simpa using (Complex.nonneg_iff.mp h).1

theorem hermitian_spectral_representation {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (f : n → ℝ), U.conjTranspose * U = 1 ∧
      U * U.conjTranspose = 1 ∧ A = realSpectral U f := by
  refine ⟨hA.eigenvectorUnitary,hA.eigenvalues,?_,?_,?_⟩
  · simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  · simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  · simpa only [realSpectral,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,Function.comp_apply] using hA.spectral_theorem

theorem positive_contraction_sub_square {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef) (h1A : (1 - A).PosSemidef) :
    (A - A * A).PosSemidef := by
  obtain ⟨U,f,hU,hU',rfl⟩ := hermitian_spectral_representation A hA.isHermitian
  have hf := realSpectral_nonnegative U hU f hA
  have hbound : ∀ i, 0 ≤ 1 - f i := by
    apply realSpectral_nonnegative U hU
    rw [realSpectral_sub,realSpectral_one U hU']
    exact h1A
  rw [realSpectral_mul U hU,← realSpectral_sub]
  apply realSpectral_positive
  intro i
  nlinarith [hf i,hbound i]

theorem hermitian_absolute_parts {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    ∃ A : Matrix n n ℂ, A.IsHermitian ∧ A * A = X * X ∧
      (A + X).PosSemidef ∧ (A - X).PosSemidef := by
  obtain ⟨U,f,hU,_,rfl⟩ := hermitian_spectral_representation X hX
  refine ⟨realSpectral U (fun i => |f i|),realSpectral_hermitian _ _,?_,?_,?_⟩
  · rw [realSpectral_mul U hU,realSpectral_mul U hU]
    congr 1
    funext i
    exact abs_mul_abs_self (f i)
  · rw [← realSpectral_add]
    apply realSpectral_positive
    intro i
    linarith [neg_le_abs (f i)]
  · rw [← realSpectral_sub]
    apply realSpectral_positive
    intro i
    linarith [le_abs_self (f i)]
end PPTQubit