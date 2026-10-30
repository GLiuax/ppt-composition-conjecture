import PPTQubit.LocalOperations
import PPTQubit.Auxiliary
/-! The auxiliary qutrit lift for an arbitrary product-indexed qubit PPT operator. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem complex_matrix_hermitian_parts {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ X Y : Matrix (Fin n) (Fin n) ℂ,
      X.IsHermitian ∧ Y.IsHermitian ∧ X + Complex.I • Y = Z ∧
        X - Complex.I • Y = Z.conjTranspose := by
  let X := (1 / 2 : ℂ) • (Z + Z.conjTranspose)
  let Y := (-Complex.I / 2 : ℂ) • (Z - Z.conjTranspose)
  have hX : X.IsHermitian := by
    ext i j
    simp [X,
      Matrix.add_apply, Matrix.smul_apply, Matrix.conjTranspose_apply]
    ring
  have hY : Y.IsHermitian := by
    ext i j
    simp [Y,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.conjTranspose_apply]
    ring
  refine ⟨X,Y,hX,hY,?_,?_⟩
  all_goals
    ext i j
    simp [X,Y,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    ring_nf
    simp [Complex.I_sq]
    ring

theorem qubit_ppt_auxiliary {n : ℕ}
    (R : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ) (hR : IsPPT R) :
    ∃ Q : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      Q.PosSemidef ∧ partialTransposeFirst Q = Q ∧ localCongruence V Q = R := by
  let A : Block n := R.submatrix (fun a => (0,a)) (fun b => (0,b))
  let B : Block n := R.submatrix (fun a => (1,a)) (fun b => (1,b))
  let Z : Block n := R.submatrix (fun a => (0,a)) (fun b => (1,b))
  have hlow (a b : Fin n) : Z.conjTranspose a b = R (1,a) (0,b) := by
    exact congrFun (congrFun hR.1.isHermitian.eq (1,a)) (0,b)
  have hblocks : flatten2 !![A,Z;Z.conjTranspose,B] = R := by
    ext ⟨i,a⟩ ⟨j,b⟩
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · exact hlow a b
    · rfl
  have hblockspt : flatten2 !![A,Z.conjTranspose;Z,B] = partialTransposeFirst R := by
    ext ⟨i,a⟩ ⟨j,b⟩
    fin_cases i <;> fin_cases j
    · rfl
    · exact hlow a b
    · rfl
    · rfl
  obtain ⟨X,Y,hX,hY,hZ,hZt⟩ := complex_matrix_hermitian_parts Z
  have hp : (Matrix.fromBlocks A (X + Complex.I • Y) (X - Complex.I • Y) B).PosSemidef := by
    apply (input_block_psd_iff _ _ _ _).mp
    rw [hZ,hZt,hblocks]
    exact hR.1
  have hpt : (Matrix.fromBlocks A (X - Complex.I • Y) (X + Complex.I • Y) B).PosSemidef := by
    apply (input_block_psd_iff _ _ _ _).mp
    rw [hZ,hZt,hblockspt]
    exact hR.2
  obtain ⟨G,_,_,_,hQ,hQpt,hrec⟩ := auxiliary_lift_exists A B X Y hX hY hp hpt
  refine ⟨flatten (aux A B X Y G),hQ,hQpt,?_⟩
  change liftedV * flatten (aux A B X Y G) * (liftedV (n := n)).conjTranspose = R
  rw [hrec,hZ,hZt,hblocks]

end PPTQubit
#print axioms PPTQubit.qubit_ppt_auxiliary
