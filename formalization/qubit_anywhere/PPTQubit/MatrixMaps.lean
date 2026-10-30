import PPTQubit.QubitPairing
import Mathlib.LinearAlgebra.Matrix.Kronecker
/-! Positive complex-linear matrix maps, real restrictions, and the Choi and tensor-action definitions. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit
abbrev MatrixMap (p q : ℕ) := Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix (Fin q) (Fin q) ℂ

def IsPositiveMap {p q : ℕ} (T : MatrixMap p q) : Prop :=
  ∀ A, A.PosSemidef → (T A).PosSemidef

def congruenceMap {p q : ℕ} (U : Matrix (Fin q) (Fin p) ℂ) : MatrixMap p q where
  toFun A := U * A * U.conjTranspose
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem congruenceMap_positive {p q : ℕ} (U : Matrix (Fin q) (Fin p) ℂ) :
    IsPositiveMap (congruenceMap U) := by
  intro A hA
  exact hA.mul_mul_conjTranspose_same U

def IsTransposeInvariantMap {p q : ℕ} (T : MatrixMap p q) : Prop :=
  ∀ A, T A.transpose = T A

def realMatrix {p q : ℕ} (U : Matrix (Fin p) (Fin q) ℝ) : Matrix (Fin p) (Fin q) ℂ :=
  U.map Complex.ofReal

theorem real_congruence_transpose {p q : ℕ} (U : Matrix (Fin q) (Fin p) ℝ)
    (A : Matrix (Fin p) (Fin p) ℂ) :
    (congruenceMap (realMatrix U) A).transpose =
      congruenceMap (realMatrix U) A.transpose := by
  have hreal : (realMatrix U).conjTranspose = (realMatrix U).transpose := by
    ext i j
    simp [realMatrix, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
  change ((realMatrix U * A * (realMatrix U).conjTranspose)).transpose =
    realMatrix U * A.transpose * (realMatrix U).conjTranspose
  rw [hreal, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

theorem real_restriction_positive {p q k : ℕ} (T : MatrixMap p k)
    (hT : IsPositiveMap T) (U : Matrix (Fin p) (Fin q) ℝ) :
    IsPositiveMap (T.comp (congruenceMap (realMatrix U))) := by
  intro A hA
  exact hT _ (congruenceMap_positive (realMatrix U) A hA)

theorem real_restriction_transpose_invariant {p q k : ℕ} (T : MatrixMap p k)
    (hT : IsTransposeInvariantMap T) (U : Matrix (Fin p) (Fin q) ℝ) :
    IsTransposeInvariantMap (T.comp (congruenceMap (realMatrix U))) := by
  intro A
  change T (congruenceMap (realMatrix U) A.transpose) = T (congruenceMap (realMatrix U) A)
  rw [← real_congruence_transpose]
  exact hT _

def choi {p q : ℕ} (T : MatrixMap p q) : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ :=
  fun i j => T (Matrix.single i.1 j.1 1) i.2 j.2

def applySecond {p q n : ℕ} (T : MatrixMap p q) :
    Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ →ₗ[ℂ]
      Matrix (Fin n × Fin q) (Fin n × Fin q) ℂ where
  toFun X i j := T (X.submatrix (fun a => (i.1,a)) (fun b => (j.1,b))) i.2 j.2
  map_add' X Y := by
    ext ⟨i,a⟩ ⟨j,b⟩
    change T ((X + Y).submatrix _ _) a b = _
    simp only [Matrix.submatrix_add, Pi.add_apply, map_add, Matrix.add_apply]
  map_smul' c X := by
    ext ⟨i,a⟩ ⟨j,b⟩
    change T ((c • X).submatrix _ _) a b = _
    simp only [Matrix.submatrix_smul, Pi.smul_apply, map_smul, Matrix.smul_apply, RingHom.id_apply]

theorem matrix_unit_expansion {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) :
    A = ∑ i, ∑ j, A i j • Matrix.single i j (1 : ℂ) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_single, smul_eq_mul, mul_one]

theorem map_entry_expansion {p q : ℕ} (T : MatrixMap p q)
    (A : Matrix (Fin p) (Fin p) ℂ) (a b : Fin q) :
    T A a b = ∑ i, ∑ j, A i j * T (Matrix.single i j 1) a b := by
  conv_lhs => rw [matrix_unit_expansion A]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]


end PPTQubit
#print axioms PPTQubit.real_restriction_transpose_invariant
#print axioms PPTQubit.map_entry_expansion
#print axioms PPTQubit.real_restriction_positive
