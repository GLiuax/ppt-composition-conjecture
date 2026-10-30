import PPTQubit.Auxiliary
import PPTQubit.GramDecomposition
/-! Generalized-inverse support identities and Hermitian extension for singular Gram matrices. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem gram_kernel {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℂ)
    (x : Fin m → ℂ) (hx : (A.conjTranspose * A).mulVec x = 0) :
    A.mulVec x = 0 := by
  have h : x ∈ (A.conjTranspose * A).mulVecLin.ker := hx
  rw [Matrix.ker_mulVecLin_conjTranspose_mul_self] at h
  exact h

theorem right_support_of_kernel {r m : ℕ} (A B : Matrix (Fin r) (Fin m) ℂ)
    (J : Matrix (Fin m) (Fin m) ℂ)
    (hGJG : (A.conjTranspose * A) * J * (A.conjTranspose * A) = A.conjTranspose * A)
    (hker : ∀ x, A.mulVec x = 0 → B.mulVec x = 0) :
    B * (J * (A.conjTranspose * A)) = B := by
  let G := A.conjTranspose * A
  have hzero : G * (1 - J * G) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hGJG, sub_self]
  have hA : A * (1 - J * G) = 0 := by
    ext i j
    have hx : G.mulVec ((1 - J * G).col j) = 0 := by
      funext k
      exact congrFun (congrFun hzero k) j
    have hz := gram_kernel A _ hx
    exact congrFun hz i
  have hB : B * (1 - J * G) = 0 := by
    ext i j
    have hx : A.mulVec ((1 - J * G).col j) = 0 := by
      funext k
      exact congrFun (congrFun hA k) j
    exact congrFun (hker _ hx) i
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hB
  exact hB.symm

theorem singular_hermitian_extension {r m : ℕ}
    (A B : Matrix (Fin r) (Fin m) ℂ)
    (hcross : (A.conjTranspose * B).IsHermitian)
    (hker : ∀ x, A.mulVec x = 0 → B.mulVec x = 0) :
    ∃ K : Matrix (Fin r) (Fin r) ℂ, K.IsHermitian ∧ K * A = B := by
  let G := A.conjTranspose * A
  obtain ⟨J, hJ, hJGJ, hGJG⟩ := psd_generalized_inverse G
    (Matrix.posSemidef_conjTranspose_mul_self A)
  let P := A * J * A.conjTranspose
  let L := B * J * A.conjTranspose
  have hAs := right_support_of_kernel A A J hGJG (fun _ hx => hx)
  have hBs := right_support_of_kernel A B J hGJG hker
  have hP : P.IsHermitian := by
    change (A * J * A.conjTranspose).conjTranspose = A * J * A.conjTranspose
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hJ.isHermitian.eq, Matrix.mul_assoc]
  have hPA : P * A = A := by
    simpa only [P, Matrix.mul_assoc] using hAs
  have hLA : L * A = B := by
    simpa only [L, Matrix.mul_assoc] using hBs
  have hLP : L * P = L := by
    change (B * J * A.conjTranspose) * (A * J * A.conjTranspose) = _
    calc
      _ = B * (J * G * J) * A.conjTranspose := by dsimp [G]; simp only [Matrix.mul_assoc]
      _ = L := by rw [hJGJ]
  have hPL : (P * L).IsHermitian := by
    have hc := hcross.eq
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at hc
    change (P * L).conjTranspose = P * L
    calc
      _ = A * J * (B.conjTranspose * A) * J * A.conjTranspose := by
        dsimp only [P, L]
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          hJ.isHermitian.eq, Matrix.mul_assoc]
      _ = A * J * (A.conjTranspose * B) * J * A.conjTranspose := by rw [hc]
      _ = P * L := by dsimp only [P, L]; simp only [Matrix.mul_assoc]
  exact ⟨_, hermitian_extension P L A B hP hLP hPL hPA hLA⟩


end PPTQubit
#print axioms PPTQubit.singular_hermitian_extension
