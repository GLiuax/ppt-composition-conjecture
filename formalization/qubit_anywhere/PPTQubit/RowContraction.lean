import PPTQubit.SpectralSeparability
/-! An explicit separable decomposition for pairs of Hermitian row contractions. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit
local notation:100 A:100 " ⊗ₘ " B:101 => Matrix.kroneckerMap (· * ·) A B

theorem tensor_row_term_identity {a b : ℕ}
    (A X : Matrix (Fin a) (Fin a) ℂ) (B Y : Matrix (Fin b) (Fin b) ℂ) :
    (1/2 : ℂ) • ((A+X) ⊗ₘ (B+Y) + (A-X) ⊗ₘ (B-Y)) +
    (1/2 : ℂ) • ((A ⊗ₘ (1 : Matrix (Fin b) (Fin b) ℂ) -
      (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₘ B) *
      (A ⊗ₘ (1 : Matrix (Fin b) (Fin b) ℂ) -
      (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₘ B)) =
    X ⊗ₘ Y + (1/2 : ℂ) • ((A*A) ⊗ₘ (1 : Matrix (Fin b) (Fin b) ℂ)) +
      (1/2 : ℂ) • ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₘ (B*B)) := by
  simp only [Matrix.mul_sub,Matrix.sub_mul,← Matrix.mul_kronecker_mul,
    Matrix.mul_one,Matrix.one_mul]
  ext ⟨i,c⟩ ⟨j,d⟩
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.add_apply,Matrix.sub_apply,Matrix.kroneckerMap_apply]
  ring

theorem hermitian_row_contraction_separable {a b k : ℕ}
    (X : Fin k → Matrix (Fin a) (Fin a) ℂ) (Y : Fin k → Matrix (Fin b) (Fin b) ℂ)
    (hX : ∀ i, (X i).IsHermitian) (hY : ∀ i, (Y i).IsHermitian)
    (hXX : (1 - ∑ i, X i * X i).PosSemidef)
    (hYY : (1 - ∑ i, Y i * Y i).PosSemidef) :
    IsSeparable ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₘ (1 : Matrix (Fin b) (Fin b) ℂ) +
      ∑ i, (X i) ⊗ₘ (Y i)) := by
  choose A hA hAX hAp hAm using fun i => hermitian_absolute_parts (X i) (hX i)
  choose B hB hBY hBp hBm using fun i => hermitian_absolute_parts (Y i) (hY i)
  let Z := fun i => (X i) ⊗ₘ (Y i) + (1/2 : ℂ) • ((A i * A i) ⊗ₘ (1 : Matrix (Fin b) (Fin b) ℂ)) +
      (1/2 : ℂ) • ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₘ (B i * B i))
  have hZ : ∀ i, IsSeparable (Z i) := by
    intro i
    dsimp only [Z]
    rw [← tensor_row_term_identity]
    apply separable_add
    · simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using separable_nonneg_smul _ (separable_add _ _
        (separable_tensor_positive _ _ (hAp i) (hBp i))
        (separable_tensor_positive _ _ (hAm i) (hBm i))) (1/2) (by norm_num)
    · simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using separable_nonneg_smul _ (separable_tensor_difference_square _ _ (hA i) (hB i)) (1/2) (by norm_num)
  have hrA := separable_nonneg_smul _
    (separable_tensor_positive _ (1 : Matrix (Fin b) (Fin b) ℂ) hXX Matrix.PosSemidef.one)
    (1/2) (by norm_num)
  have hrB := separable_nonneg_smul _
    (separable_tensor_positive (1 : Matrix (Fin a) (Fin a) ℂ) _ Matrix.PosSemidef.one hYY)
    (1/2) (by norm_num)
  have hSep := separable_add _ _ (separable_add _ _ (separable_finite_sum Z hZ) hrA) hrB
  convert hSep using 1
  ext ⟨i,c⟩ ⟨j,d⟩
  simp only [Z,Matrix.sum_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.kronecker,Matrix.kroneckerMap_apply,hAX,hBY,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
  ring
end PPTQubit
#print axioms PPTQubit.hermitian_row_contraction_separable
