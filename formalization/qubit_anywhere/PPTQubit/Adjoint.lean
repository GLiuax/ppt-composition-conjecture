import PPTQubit.SchmidtIteration
/-! Hilbert-Schmidt adjoints of PPT maps and the adjoint 2-EB conclusion. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def hsPair {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ i, ∑ j, star (A i j) * B i j

def hsAdjoint {p q : ℕ} (T : MatrixMap p q) : MatrixMap q p :=
  mapFromChoi ((swapFactors (choi T)).map star)

theorem hsAdjoint_pairing {p q : ℕ} (T : MatrixMap p q)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) :
    hsPair (T A) B = hsPair A (hsAdjoint T B) := by
  simp only [hsPair,hsAdjoint,mapFromChoi,LinearMap.coe_mk,AddHom.coe_mk,
    Matrix.map_apply,swapFactors,Matrix.submatrix_apply,Prod.swap_prod_mk,
    choi, map_entry_expansion T A,star_sum,StarMul.star_mul,Finset.sum_mul,Finset.mul_sum]
  rw [sum_four_exchange]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem hsPair_single {p : ℕ} (X : Matrix (Fin p) (Fin p) ℂ) (i j : Fin p) :
    hsPair (Matrix.single i j 1) X = X i j := by
  simp [hsPair,Matrix.single_apply,ite_and,apply_ite]

theorem hsAdjoint_comp {p q r : ℕ} (T : MatrixMap q r) (S : MatrixMap p q) :
    hsAdjoint (T.comp S) = (hsAdjoint S).comp (hsAdjoint T) := by
  ext B i j
  have he (A : Matrix (Fin p) (Fin p) ℂ) :
      hsPair A (hsAdjoint (T.comp S) B) = hsPair A ((hsAdjoint S).comp (hsAdjoint T) B) := by
    change hsPair A (hsAdjoint (T.comp S) B) = hsPair A (hsAdjoint S (hsAdjoint T B))
    calc
      _ = hsPair (T (S A)) B := (hsAdjoint_pairing (T.comp S) A B).symm
      _ = hsPair (S A) (hsAdjoint T B) := hsAdjoint_pairing T (S A) B
      _ = _ := hsAdjoint_pairing S A (hsAdjoint T B)

  simpa only [hsPair_single] using he (Matrix.single i j 1)

theorem ppt_transpose {p q : ℕ} (X : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)
    (hX : IsPPT X) : IsPPT X.transpose := by
  refine ⟨hX.1.transpose,?_⟩
  have he : partialTransposeFirst X.transpose = (partialTransposeFirst X).transpose := by
    ext ⟨i,a⟩ ⟨j,b⟩
    rfl
  rw [he]
  exact hX.2.transpose

theorem conjugateMatrix_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : X.IsHermitian) : X.map star = X.transpose := by
  ext i j
  exact congrFun (congrFun hX.eq j) i

theorem hsAdjoint_ppt {p q : ℕ} (T : MatrixMap p q) (hT : IsPPTMap T) :
    IsPPTMap (hsAdjoint T) := by
  change IsPPT (choi (mapFromChoi ((swapFactors (choi T)).map star)))
  rw [choi_mapFromChoi]
  have h := swapFactors_ppt (choi T) hT
  rw [conjugateMatrix_hermitian _ h.1.isHermitian]
  exact ppt_transpose _ h

theorem ppt_pair_adjoint_two_eb {p q r : ℕ} (S : MatrixMap p q) (T : MatrixMap q r)
    (hS : IsPPTMap S) (hT : IsPPTMap T) :
    IsTwoEntanglementBreaking (hsAdjoint (T.comp S)) := by
  rw [hsAdjoint_comp]
  exact ppt_composition_two_entanglement_breaking (hsAdjoint T) (hsAdjoint S)
    (hsAdjoint_ppt T hT) (hsAdjoint_ppt S hS)
end PPTQubit
#print axioms PPTQubit.hsAdjoint_pairing
#print axioms PPTQubit.ppt_pair_adjoint_two_eb
