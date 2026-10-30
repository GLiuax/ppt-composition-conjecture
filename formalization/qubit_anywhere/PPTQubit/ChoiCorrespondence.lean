import PPTQubit.ChoiTensor
/-! Choi inversion, composition and transpose-dual identities, and the entanglement-breaking criterion. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def swapFactors {p q : ℕ} (X : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ) :
    Matrix (Fin q × Fin p) (Fin q × Fin p) ℂ := X.submatrix Prod.swap Prod.swap

@[simp] theorem swapFactors_involutive {p q : ℕ}
    (X : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ) : swapFactors (swapFactors X) = X := by
  ext ⟨i,a⟩ ⟨j,b⟩
  rfl

theorem swapFactors_ppt {p q : ℕ} (X : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)
    (hX : IsPPT X) : IsPPT (swapFactors X) := by
  constructor
  · exact hX.1.submatrix Prod.swap
  · have heq : partialTransposeFirst (swapFactors X) = swapFactors (partialTransposeFirst X).transpose := by
      ext ⟨i,a⟩ ⟨j,b⟩
      rfl
    rw [heq]
    exact hX.2.transpose.submatrix Prod.swap

theorem swapFactors_separable {p q : ℕ} (X : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)
    (hX : IsSeparable X) : IsSeparable (swapFactors X) := by
  obtain ⟨r,v,w,hsum⟩ := hX
  refine ⟨r,w,v,?_⟩
  intro a i b j
  change X (i,a) (j,b) = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_comm (w s a) (v s i),mul_comm (w s b) (v s j)]

def mapFromChoi {p q : ℕ} (W : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ) : MatrixMap p q where
  toFun A a b := ∑ i, ∑ j, A i j * W (i,a) (j,b)
  map_add' A B := by
    ext a b
    simp [Matrix.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' c A := by
    ext a b
    simp [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

@[simp] theorem choi_mapFromChoi {p q : ℕ}
    (W : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ) : choi (mapFromChoi W) = W := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp [choi,mapFromChoi,Matrix.single_apply, ite_and]

theorem mapFromChoi_choi {p q : ℕ} (T : MatrixMap p q) : mapFromChoi (choi T) = T := by
  ext A a b
  exact (map_entry_expansion T A a b).symm

def transposeDual {p q : ℕ} (T : MatrixMap p q) : MatrixMap q p :=
  mapFromChoi (swapFactors (choi T))

theorem transposeDual_ppt {p q : ℕ} (T : MatrixMap p q) (hT : IsPPTMap T) :
    IsPPTMap (transposeDual T) := by
  change IsPPT (choi (mapFromChoi (swapFactors (choi T))))
  rw [choi_mapFromChoi]
  exact swapFactors_ppt _ hT

theorem choi_comp {p q r : ℕ} (T : MatrixMap q r) (S : MatrixMap p q) :
    choi (T.comp S) = applySecond T (choi S) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  rfl

theorem choi_comp_transposeDual {p q r : ℕ} (T : MatrixMap q r) (S : MatrixMap p q) :
    swapFactors (choi (T.comp S)) = applySecond (transposeDual S) (swapFactors (choi T)) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  change T (S (Matrix.single i j 1)) a b =
    ∑ k, ∑ l, T (Matrix.single k l 1) a b * S (Matrix.single i j 1) k l
  rw [map_entry_expansion]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Entanglement breaking is defined by all ancillary dimensions and all positive inputs. -/
def IsEntanglementBreaking {p q : ℕ} (T : MatrixMap p q) : Prop :=
  ∀ (n : ℕ) (X : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ),
    X.PosSemidef → IsSeparable (applySecond T X)

theorem entanglementBreaking_iff_choi_separable {p q : ℕ} (T : MatrixMap p q) :
    IsEntanglementBreaking T ↔ IsSeparable (choi T) := by
  constructor
  · intro h
    have hh := h p (pureProjector (vectorize (1 : Matrix (Fin p) (Fin p) ℂ)))
      (pureProjector_positive _)
    rw [applySecond_pure_choi,Matrix.transpose_one,localCongruence_identity] at hh
    exact hh
  · intro h n X hX
    obtain ⟨r,psi,hsum⟩ := positive_pure_expansion X hX
    rw [hsum,map_sum]
    apply separable_finite_sum
    intro s
    let C : Matrix (Fin p) (Fin n) ℂ := fun i a => psi s (a,i)
    change IsSeparable (applySecond T (pureProjector (vectorize C)))
    rw [applySecond_pure_choi]
    exact localCongruence_separable C.transpose _ h

end PPTQubit
#print axioms PPTQubit.entanglementBreaking_iff_choi_separable
#print axioms PPTQubit.choi_comp_transposeDual
#print axioms PPTQubit.choi_mapFromChoi
#print axioms PPTQubit.mapFromChoi_choi
#print axioms PPTQubit.transposeDual_ppt
