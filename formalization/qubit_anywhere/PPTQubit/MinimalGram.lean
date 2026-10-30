import PPTQubit.InvariantDecomposition
/-! A Gram factor with exactly rank Q rows and injective adjoint, including Q = 0. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem sum_subtype_of_zero {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (f : ι → ℂ) (h : ∀ i, ¬ p i → f i = 0) :
    (∑ i : {i // p i}, f i) = ∑ i, f i := by
  have hz : (∑ i : {i // ¬ p i}, f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact h i i.property
  simpa only [hz, add_zero] using Fintype.sum_subtype_add_sum_subtype p f

theorem psd_minimal_gram_factor {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (hQ : Q.PosSemidef) :
    ∃ (r : ℕ) (C : Matrix (Fin r) n ℂ),
      C.conjTranspose * C = Q ∧ Function.Injective C.conjTranspose.mulVec ∧ r = Q.rank := by
  classical
  let hH := hQ.isHermitian
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let d : n → ℂ := fun i => (hH.eigenvalues i : ℂ)
  let f : n → ℂ := fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)
  let F := Matrix.diagonal f
  let S := F * U.conjTranspose
  let σ := {i : n // hH.eigenvalues i ≠ 0}
  let r := Fintype.card σ
  let e : Fin r ≃ σ := (Fintype.equivFin σ).symm
  let rows : Fin r → n := fun i => (e i).val
  let C := S.submatrix rows id
  have hU : U.conjTranspose * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hQd : Q = U * Matrix.diagonal d * U.conjTranspose := by
    simpa only [U, d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_apply] using hH.spectral_theorem
  have hF : F.conjTranspose = F := by simp [F, f]
  have hFF : F * F = Matrix.diagonal d := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    dsimp [f, d]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hQ.eigenvalues_nonneg i)]
  have hS : S.conjTranspose * S = Q := by
    dsimp only [S]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hF]
    calc
      _ = U * (F * F) * U.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = Q := by rw [hFF, ← hQd]
  have hSS : S * S.conjTranspose = Matrix.diagonal d := by
    dsimp only [S]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hF]
    calc
      _ = F * (U.conjTranspose * U) * F := by simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal d := by rw [hU, Matrix.mul_one, hFF]
  have hzero (i : n) (hi : hH.eigenvalues i = 0) (a : n) : S i a = 0 := by
    simp [S, F, Matrix.diagonal_mul, f, hi]
  have hC : C.conjTranspose * C = Q := by
    rw [← hS]
    ext a b
    change (∑ i : Fin r, star (S (rows i) a) * S (rows i) b) =
      ∑ i : n, star (S i a) * S i b
    calc
      _ = ∑ i : σ, star (S i a) * S i b := e.sum_comp _
      _ = _ := sum_subtype_of_zero (fun i => hH.eigenvalues i ≠ 0) (fun i => star (S i a) * S i b) (by
        intro i hi
        have hi' : hH.eigenvalues i = 0 := not_not.mp hi
        dsimp only
        rw [hzero i hi' a, star_zero, zero_mul])
  have hrows : Function.Injective rows := Subtype.val_injective.comp e.injective
  have hCC : C * C.conjTranspose = Matrix.diagonal (d ∘ rows) := by
    dsimp only [C]
    rw [Matrix.conjTranspose_submatrix]
    rw [← Matrix.submatrix_mul S S.conjTranspose rows id rows Function.bijective_id]
    rw [hSS, Matrix.submatrix_diagonal d rows hrows]
  have hp : (C * C.conjTranspose).PosDef := by
    rw [hCC]
    apply Matrix.PosDef.diagonal
    intro i
    apply Complex.pos_iff.mpr
    constructor
    · exact lt_of_le_of_ne (hQ.eigenvalues_nonneg (rows i)) (Ne.symm (e i).property)
    · rfl
  have hinj : Function.Injective C.conjTranspose.mulVec := by
    intro x y hxy
    apply Matrix.mulVec_injective_iff_isUnit.mpr hp.isUnit
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
  refine ⟨r, C, hC, hinj, ?_⟩
  rw [hH.rank_eq_rank_diagonal, Matrix.rank_diagonal]

end PPTQubit
#print axioms PPTQubit.psd_minimal_gram_factor
