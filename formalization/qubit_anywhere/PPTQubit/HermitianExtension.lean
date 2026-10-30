import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.NoncommRing
/-! The Hermitian extension step in Sec. S2 of the manuscript. -/

open Matrix
noncomputable section
namespace PPTQubit
set_option linter.unusedSimpArgs false

theorem hermitian_extension {r m : ℕ} (P L : Matrix (Fin r) (Fin r) ℂ)
    (D0 D1 : Matrix (Fin r) (Fin m) ℂ)
    (hP : P.IsHermitian) (hLP : L * P = L)
    (hPL : (P * L).IsHermitian) (hPD : P * D0 = D0) (hLD : L * D0 = D1) :
    let K := L + L.conjTranspose - P * L
    K.IsHermitian ∧ K * D0 = D1 := by
  dsimp
  have hx : L.conjTranspose * P = P * L := by
    simpa only [Matrix.conjTranspose_mul, hP.eq] using hPL.eq
  have hk : (L + L.conjTranspose - P * L).IsHermitian := by
    change (L + L.conjTranspose - P * L).conjTranspose =
      L + L.conjTranspose - P * L
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, hPL.eq]
    abel
  have hkp : (L + L.conjTranspose - P * L) * P = L := by
    calc
      _ = L * P + L.conjTranspose * P - P * (L * P) := by noncomm_ring
      _ = L := by rw [hLP, hx]; abel
  refine ⟨hk, ?_⟩
  calc
    _ = (L + L.conjTranspose - P * L) * (P * D0) := by rw [hPD]
    _ = ((L + L.conjTranspose - P * L) * P) * D0 :=
      (Matrix.mul_assoc (L + L.conjTranspose - P * L) P D0).symm
    _ = D1 := by rw [hkp, hLD]

theorem explicit_hermitian_extension {r m : ℕ}
    (D0 D1 : Matrix (Fin r) (Fin m) ℂ)
    (hunit : IsUnit (D0.conjTranspose * D0).det)
    (hcross : (D0.conjTranspose * D1).IsHermitian) :
    ∃ K : Matrix (Fin r) (Fin r) ℂ, K.IsHermitian ∧ K * D0 = D1 := by
  let J : Matrix (Fin m) (Fin m) ℂ := (D0.conjTranspose * D0)⁻¹
  let P : Matrix (Fin r) (Fin r) ℂ := D0 * J * D0.conjTranspose
  let L : Matrix (Fin r) (Fin r) ℂ := D1 * J * D0.conjTranspose
  have hgram : (D0.conjTranspose * D0).IsHermitian := by
    change (D0.conjTranspose * D0).conjTranspose = D0.conjTranspose * D0
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hJ : J.IsHermitian := hgram.inv
  have hJG : J * (D0.conjTranspose * D0) = 1 :=
    Matrix.nonsing_inv_mul _ hunit
  have hGJ : (D0.conjTranspose * D0) * J = 1 :=
    Matrix.mul_nonsing_inv _ hunit
  have hP : P.IsHermitian := by
    change (D0 * J * D0.conjTranspose).conjTranspose = D0 * J * D0.conjTranspose
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ.eq]
    exact (Matrix.mul_assoc D0 J D0.conjTranspose).symm
  have hPD : P * D0 = D0 := by
    dsimp only [P]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc D0.conjTranspose D0, hJG,
      Matrix.mul_one, Matrix.one_mul]
  have hLD : L * D0 = D1 := by
    dsimp only [L]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc D0.conjTranspose D0, hJG,
      Matrix.mul_one, Matrix.one_mul]
  have hLP : L * P = L := by
    dsimp only [L, P]
    calc
      _ = D1 * (J * (D0.conjTranspose * D0) * J) * D0.conjTranspose := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJG, Matrix.one_mul]
  have hPL : (P * L).IsHermitian := by
    change (P * L).conjTranspose = P * L
    have hc := hcross.eq
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at hc
    calc
      _ = D0 * J * (D1.conjTranspose * D0) * J * D0.conjTranspose := by
        dsimp only [P, L]
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ.eq,
          Matrix.mul_assoc]
      _ = D0 * J * (D0.conjTranspose * D1) * J * D0.conjTranspose := by rw [hc]
      _ = P * L := by dsimp only [P, L]; simp only [Matrix.mul_assoc]
  exact ⟨_, hermitian_extension P L D0 D1 hP hLP hPL hPD hLD⟩

theorem real_eigenvalue_annihilator {r m : ℕ}
    (K : Matrix (Fin r) (Fin r) ℂ) (D0 D1 : Matrix (Fin r) (Fin m) ℂ)
    (x : Fin r → ℂ) (ell : ℝ) (hK : K.IsHermitian)
    (hD : K * D0 = D1) (hx : K.mulVec x = (ell : ℂ) • x) :
    D1.conjTranspose.mulVec x = (ell : ℂ) • D0.conjTranspose.mulVec x := by
  rw [← hD, Matrix.conjTranspose_mul, hK.eq, ← Matrix.mulVec_mulVec, hx]
  exact Matrix.mulVec_smul D0.conjTranspose (ell : ℂ) x

theorem gram_eigenbasis_relation {r m : ℕ}
    (D0 D1 : Matrix (Fin r) (Fin m) ℂ)
    (hunit : IsUnit (D0.conjTranspose * D0).det)
    (hcross : (D0.conjTranspose * D1).IsHermitian) :
    ∃ K : Matrix (Fin r) (Fin r) ℂ, ∃ hK : K.IsHermitian,
      K * D0 = D1 ∧
      ∀ j : Fin r,
        D1.conjTranspose.mulVec (hK.eigenvectorBasis j).ofLp =
          (hK.eigenvalues j : ℂ) • D0.conjTranspose.mulVec (hK.eigenvectorBasis j).ofLp := by
  obtain ⟨K, hK, hD⟩ := explicit_hermitian_extension D0 D1 hunit hcross
  refine ⟨K, hK, hD, ?_⟩
  intro j
  apply real_eigenvalue_annihilator K D0 D1 _ (hK.eigenvalues j) hK hD
  simpa only [RCLike.real_smul_eq_coe_smul] using hK.mulVec_eigenvectorBasis j

theorem gram_rank_one_expansion {r : ℕ} {m : Type}
    (C : Matrix (Fin r) m ℂ) (U : Matrix (Fin r) (Fin r) ℂ)
    (hU : U * U.conjTranspose = 1) :
    C.conjTranspose * C = fun i j =>
      ∑ s : Fin r, (C.conjTranspose * U) i s *
        star ((C.conjTranspose * U) j s) := by
  calc
    _ = C.conjTranspose * (U * U.conjTranspose) * C := by rw [hU]; simp
    _ = (C.conjTranspose * U) * (U.conjTranspose * C) := by
      simp only [Matrix.mul_assoc]
    _ = (C.conjTranspose * U) * (C.conjTranspose * U).conjTranspose := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    _ = _ := by ext i j; rfl

def firstGram {r m p : ℕ} (C : Matrix (Fin r) (Fin (p + 2) × Fin m) ℂ) :
    Matrix (Fin r) (Fin m) ℂ := fun s a => C s (0, a)

def secondGram {r m p : ℕ} (C : Matrix (Fin r) (Fin (p + 2) × Fin m) ℂ) :
    Matrix (Fin r) (Fin m) ℂ := fun s a => C s (1, a)

theorem conditional_real_hyperplanes {r m p : ℕ}
    (C : Matrix (Fin r) (Fin (p + 2) × Fin m) ℂ)
    (hunit : IsUnit ((firstGram C).conjTranspose * firstGram C).det)
    (hcross : ((firstGram C).conjTranspose * secondGram C).IsHermitian)
    (hinj : Function.Injective C.conjTranspose.mulVec) :
    ∃ (psi : Fin r → Fin (p + 2) × Fin m → ℂ) (ell : Fin r → ℝ),
      (∀ i j, (C.conjTranspose * C) i j = ∑ s, psi s i * star (psi s j)) ∧
      (∀ s a, psi s (1, a) = (ell s : ℂ) * psi s (0, a)) ∧
      (∀ s, psi s ≠ 0) := by
  obtain ⟨K, hK, hKD, hEig⟩ :=
    gram_eigenbasis_relation (firstGram C) (secondGram C) hunit hcross
  let U : Matrix (Fin r) (Fin r) ℂ := hK.eigenvectorUnitary
  let psi : Fin r → Fin (p + 2) × Fin m → ℂ := fun s i => (C.conjTranspose * U) i s
  let ell : Fin r → ℝ := hK.eigenvalues
  have hU : U * U.conjTranspose = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hK.eigenvectorUnitary
  refine ⟨psi, ell, ?_, ?_, ?_⟩
  · intro i j
    exact congrFun (congrFun (gram_rank_one_expansion C U hU) i) j
  · intro s a
    have h := congrFun (hEig s) a
    change psi s (1,a) = (ell s : ℂ) * psi s (0,a)
    simpa [psi, ell, firstGram, secondGram, Matrix.mul_apply, Matrix.mulVec,
      hK.eigenvectorUnitary_apply] using h
  · intro s hzero
    have hxne : (hK.eigenvectorBasis s).ofLp ≠ 0 := by
      intro hz
      have hz' : hK.eigenvectorBasis s = 0 := by
        apply WithLp.ofLp_injective 2
        simpa using hz
      exact (hK.eigenvectorBasis.toBasis.ne_zero s) hz'
    have hpsi : C.conjTranspose.mulVec (hK.eigenvectorBasis s).ofLp = psi s := by
      ext i
      simp [psi, U, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        hK.eigenvectorUnitary_apply]
    apply hxne
    apply hinj
    rw [hpsi, hzero, Matrix.mulVec_zero]

end PPTQubit

#print axioms PPTQubit.explicit_hermitian_extension
#print axioms PPTQubit.real_eigenvalue_annihilator
#print axioms PPTQubit.gram_eigenbasis_relation
#print axioms PPTQubit.gram_rank_one_expansion
#print axioms PPTQubit.conditional_real_hyperplanes
