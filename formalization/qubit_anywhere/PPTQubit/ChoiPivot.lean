import PPTQubit.KPositive
/-! Positive 2-by-2 Choi blocks and generalized-inverse pivot support. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem two_positive_choi_principal {p q : ℕ} (T : MatrixMap p q)
    (hT : IsKPositiveMap 2 T) (f : Fin 2 → Fin p) :
    ((choi T).submatrix (fun x : Fin 2 × Fin q => (f x.1,x.2))
      (fun x : Fin 2 × Fin q => (f x.1,x.2))).PosSemidef := by
  let C : Matrix (Fin p) (Fin 2) ℂ := fun i j => if i = f j then 1 else 0
  have h := hT (pureProjector (vectorize C)) (pureProjector_positive _)
  rw [applySecond_pure_choi] at h
  have he : localCongruence C.transpose (choi T) =
      (choi T).submatrix (fun x : Fin 2 × Fin q => (f x.1,x.2))
        (fun x : Fin 2 × Fin q => (f x.1,x.2)) := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp [localCongruence_entry,C,Matrix.transpose_apply,apply_ite]
  rwa [he] at h

theorem two_positive_choi_diagonal {p q : ℕ} (T : MatrixMap p q)
    (hT : IsKPositiveMap 2 T) (s : Fin p) : (T (Matrix.single s s 1)).PosSemidef := by
  let f : Fin 2 → Fin p := ![s,s]
  have h := (two_positive_choi_principal T hT f).submatrix (fun a : Fin q => (0,a))
  exact h

theorem two_positive_choi_pivot_support_with_inverse {p q : ℕ} (T : MatrixMap p q)
    (hT : IsKPositiveMap 2 T) (hH : (choi T).IsHermitian) (i s : Fin p)
    (G : Matrix (Fin q) (Fin q) ℂ) (hG : G.IsHermitian)
    (hBGB : T (Matrix.single s s 1) * G * T (Matrix.single s s 1) = T (Matrix.single s s 1)) :
    T (Matrix.single i s 1) * G * T (Matrix.single s s 1) = T (Matrix.single i s 1) := by
  let f : Fin 2 → Fin p := ![i,s]
  let W := (choi T).submatrix (fun x : Fin 2 × Fin q => (f x.1,x.2))
      (fun x : Fin 2 × Fin q => (f x.1,x.2))
  have hW : W.PosSemidef := two_positive_choi_principal T hT f
  let A := T (Matrix.single i i 1)
  let B := T (Matrix.single s s 1)
  let C := T (Matrix.single i s 1)
  have hB : B.PosSemidef := two_positive_choi_diagonal T hT s
  have hlower : T (Matrix.single s i 1) = C.conjTranspose := by
    ext a b
    have hh := congrFun (congrFun hH.eq (s,a)) (i,b)
    exact hh.symm
  let e : Fin q ⊕ Fin q → Fin 2 × Fin q := Sum.elim (fun a => (0,a)) (fun a => (1,a))
  have hblock : W.submatrix e e = Matrix.fromBlocks A C C.conjTranspose B := by
    ext x y
    cases x with
    | inl a => cases y with
      | inl b => rfl
      | inr b => rfl
    | inr a => cases y with
      | inl b => exact congrFun (congrFun hlower a) b
      | inr b => rfl
  have hpos : (Matrix.fromBlocks A C C.conjTranspose B).PosSemidef := by
    rw [← hblock]
    exact hW.submatrix e
  exact positive_block_support A B C G hB.isHermitian hG hBGB hpos

theorem two_positive_choi_pivot_support {p q : ℕ} (T : MatrixMap p q)
    (hT : IsKPositiveMap 2 T) (hH : (choi T).IsHermitian) (s : Fin p) :
    ∃ G : Matrix (Fin q) (Fin q) ℂ,
      G.PosSemidef ∧ G * T (Matrix.single s s 1) * G = G ∧
      T (Matrix.single s s 1) * G * T (Matrix.single s s 1) = T (Matrix.single s s 1) ∧
      ∀ i, T (Matrix.single i s 1) * G * T (Matrix.single s s 1) = T (Matrix.single i s 1) := by
  obtain ⟨G,hG,hGBG,hBGB,_⟩ := psd_commuting_generalized_inverse _ (two_positive_choi_diagonal T hT s)
  exact ⟨G,hG,hGBG,hBGB,fun i => two_positive_choi_pivot_support_with_inverse T hT hH i s G hG.isHermitian hBGB⟩

theorem choi_positive_implies_complete_positive {p q : ℕ} (T : MatrixMap p q)
    (hT : (choi T).PosSemidef) : IsCompletelyPositiveMap T := by
  intro n Q hQ
  obtain ⟨r,z,hQ⟩ := positive_pure_expansion Q hQ
  rw [hQ,map_sum]
  apply Finset.sum_induction
  · intro A B hA hB; exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro t _
    let C : Matrix (Fin p) (Fin n) ℂ := fun i a => z t (a,i)
    change (applySecond T (pureProjector (vectorize C))).PosSemidef
    rw [applySecond_pure_choi]
    exact hT.mul_mul_conjTranspose_same (localLift C.transpose)

def choiPivotColumn {p q : ℕ} (T : MatrixMap p q) (s : Fin p) :
    Matrix (Fin p × Fin q) (Fin q) ℂ := fun x b => T (Matrix.single x.1 s 1) x.2 b

def choiPivot {p q : ℕ} (T : MatrixMap p q) (s : Fin p) (G : Matrix (Fin q) (Fin q) ℂ) :
    Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ :=
  choiPivotColumn T s * G * (choiPivotColumn T s).conjTranspose

theorem choiPivot_block {p q : ℕ} (T : MatrixMap p q) (s i j : Fin p)
    (G : Matrix (Fin q) (Fin q) ℂ) :
    (choiPivot T s G).submatrix (fun a => (i,a)) (fun b => (j,b)) =
      T (Matrix.single i s 1) * G * (T (Matrix.single j s 1)).conjTranspose := by
  ext a b
  simp [choiPivot,choiPivotColumn,Matrix.mul_apply,Matrix.conjTranspose_apply]

/-- The completely positive pivot component matches the chosen Choi row and
column, including when the diagonal block is singular. -/
theorem two_positive_choi_pivot_component {p q : ℕ} (T : MatrixMap p q)
    (hT : IsKPositiveMap 2 T) (hH : (choi T).IsHermitian) (s : Fin p) :
    ∃ F : MatrixMap p q, IsCompletelyPositiveMap F ∧
      ∀ i, (T-F) (Matrix.single i s 1) = 0 ∧ (T-F) (Matrix.single s i 1) = 0 := by
  obtain ⟨G,hG,hGBG,hBGB,hs⟩ := two_positive_choi_pivot_support T hT hH s
  let W := choiPivot T s G
  have hW : W.PosSemidef := hG.mul_mul_conjTranspose_same (choiPivotColumn T s)
  let F : MatrixMap p q := mapFromChoi W
  have hF : IsCompletelyPositiveMap F := by
    apply choi_positive_implies_complete_positive
    change (choi (mapFromChoi W)).PosSemidef
    rw [choi_mapFromChoi]
    exact hW
  have hcol (i : Fin p) :
      W.submatrix (fun a => (i,a)) (fun b => (s,b)) = T (Matrix.single i s 1) := by
    rw [choiPivot_block]
    have hB : (T (Matrix.single s s 1)).IsHermitian := (two_positive_choi_diagonal T hT s).isHermitian
    rw [hB.eq,hs]
  have hrow (i : Fin p) :
      W.submatrix (fun a => (s,a)) (fun b => (i,b)) = T (Matrix.single s i 1) := by
    have hWherm := hW.isHermitian.eq
    ext a b
    have hw := congrFun (congrFun hWherm (s,a)) (i,b)
    have ht := congrFun (congrFun hH.eq (s,a)) (i,b)
    have hc := congrFun (congrFun (hcol i) b) a
    change star (W (i,b) (s,a)) = W (s,a) (i,b) at hw
    change star (T (Matrix.single i s 1) b a) = T (Matrix.single s i 1) a b at ht
    change W (i,b) (s,a) = T (Matrix.single i s 1) b a at hc
    rw [hc] at hw
    exact hw.symm.trans ht
  refine ⟨F,hF,?_⟩
  intro i
  constructor <;> ext a b
  · change T (Matrix.single i s 1) a b - F (Matrix.single i s 1) a b = 0
    have hf := congrFun (congrFun (choi_mapFromChoi W) (i,a)) (s,b)
    change F (Matrix.single i s 1) a b = W (i,a) (s,b) at hf
    rw [hf]
    exact sub_eq_zero.mpr (congrFun (congrFun (hcol i) a) b).symm
  · change T (Matrix.single s i 1) a b - F (Matrix.single s i 1) a b = 0
    have hf := congrFun (congrFun (choi_mapFromChoi W) (s,a)) (i,b)
    change F (Matrix.single s i 1) a b = W (s,a) (i,b) at hf
    rw [hf]
    exact sub_eq_zero.mpr (congrFun (congrFun (hrow i) a) b).symm

end PPTQubit
#print axioms PPTQubit.two_positive_choi_pivot_support

#print axioms PPTQubit.two_positive_choi_pivot_component
