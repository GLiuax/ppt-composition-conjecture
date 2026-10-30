import PPTQubit.SchmidtCone
/-! Real-linear functionals on complex matrices as real trace pairings. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def realDualMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (f : Matrix n n ℂ →ₗ[ℝ] ℝ) : Matrix n n ℂ := fun i j =>
  (f (Matrix.single j i (1 : ℂ)) : ℂ) - Complex.I * (f (Complex.I • Matrix.single j i (1 : ℂ)) : ℂ)

theorem real_linear_single {n : Type*} [Fintype n] [DecidableEq n]
    (f : Matrix n n ℂ →ₗ[ℝ] ℝ) (z : ℂ) (i j : n) :
    f (z • Matrix.single i j (1 : ℂ)) =
      z.re * f (Matrix.single i j (1 : ℂ)) + z.im * f (Complex.I • Matrix.single i j (1 : ℂ)) := by
  have hm : z • Matrix.single i j (1 : ℂ) =
      z.re • Matrix.single i j (1 : ℂ) + z.im • (Complex.I • Matrix.single i j (1 : ℂ)) := by
    ext a b
    simp only [Matrix.smul_apply,Matrix.add_apply,Complex.real_smul,smul_eq_mul]
    calc
      _ = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) * Matrix.single i j (1 : ℂ) a b := by rw [Complex.re_add_im]
      _ = _ := by ring
  rw [hm,map_add,map_smul,map_smul]
  rfl

theorem real_linear_trace_pairing {n : Type*} [Fintype n] [DecidableEq n]
    (f : Matrix n n ℂ →ₗ[ℝ] ℝ) (A : Matrix n n ℂ) :
    f A = (A * realDualMatrix f).trace.re := by
  have hA : f A = ∑ i, ∑ j,
      ((A i j).re * f (Matrix.single i j (1 : ℂ)) +
      (A i j).im * f (Complex.I • Matrix.single i j (1 : ℂ))) := by
    have he : A = ∑ i, ∑ j, A i j • Matrix.single i j (1 : ℂ) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single A]
      simp only [Matrix.smul_single,smul_eq_mul,mul_one]
    conv_lhs => rw [he]
    simp only [map_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    exact real_linear_single f (A i j) i j
  rw [hA]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Complex.re_sum,realDualMatrix,
    Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring
def hermitianPart {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℂ) : Matrix n n ℂ := (1/2 : ℂ) • (W+W.conjTranspose)

theorem hermitianPart_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℂ) : (hermitianPart W).IsHermitian := by
  change ((1/2 : ℂ) • (W+W.conjTranspose)).conjTranspose = _
  simp [hermitianPart,Matrix.conjTranspose_smul,Matrix.conjTranspose_add,add_comm]

theorem real_trace_hermitian_part {n : Type*} [Fintype n] [DecidableEq n]
    (A W : Matrix n n ℂ) (hA : A.IsHermitian) :
    (A * hermitianPart W).trace.re = (A*W).trace.re := by
  have hh : (A * W.conjTranspose).trace = star (A*W).trace := by
    calc
      _ = (W.conjTranspose*A).trace := Matrix.trace_mul_comm _ _
      _ = (A*W).conjTranspose.trace := by rw [Matrix.conjTranspose_mul,hA.eq]
      _ = star (A*W).trace := Matrix.trace_conjTranspose _
  have hhalf : ((1/2 : ℂ)).re = (1/2 : ℝ) := by norm_num
  have hhalf' : ((1/2 : ℂ)).im = (0 : ℝ) := by norm_num
  simp only [hermitianPart,Matrix.mul_smul,Matrix.mul_add,Matrix.trace_smul,
    Matrix.trace_add,smul_eq_mul,hh,Complex.star_def,Complex.mul_re,Complex.add_re,
    Complex.conj_re,hhalf,hhalf',zero_mul,sub_zero]
  ring


theorem real_linear_hermitian_witness {n : Type*} [Fintype n] [DecidableEq n]
    (f : Matrix n n ℂ →ₗ[ℝ] ℝ) :
    ∃ W : Matrix n n ℂ, W.IsHermitian ∧
      ∀ A : Matrix n n ℂ, A.IsHermitian → f A = (A*W).trace.re := by
  refine ⟨hermitianPart (realDualMatrix f),hermitianPart_hermitian _,?_⟩
  intro A hA
  rw [real_trace_hermitian_part A _ hA]
  exact real_linear_trace_pairing f A

end PPTQubit
#print axioms PPTQubit.real_linear_trace_pairing

#print axioms PPTQubit.real_linear_hermitian_witness
