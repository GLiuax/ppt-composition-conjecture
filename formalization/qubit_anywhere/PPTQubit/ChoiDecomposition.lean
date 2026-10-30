import PPTQubit.ChoiPivot
/-! Schur-complement construction for the Choi decomposition. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def pivotEmbedding {p q : ℕ} (s : Fin p) : Matrix (Fin p × Fin q) (Fin q) ℂ :=
  fun x b => (if x.1 = s then 1 else 0) * (1 : Matrix (Fin q) (Fin q) ℂ) x.2 b

theorem choi_mul_pivotEmbedding {p q : ℕ} (T : MatrixMap p q) (s : Fin p) :
    choi T * pivotEmbedding (q := q) s = choiPivotColumn T s := by
  ext ⟨i,a⟩ b
  simp [Matrix.mul_apply,Fintype.sum_prod_type,pivotEmbedding,Matrix.one_apply,
    choi,choiPivotColumn,apply_ite]

theorem pivotEmbedding_choi_pivot {p q : ℕ} (T : MatrixMap p q) (s : Fin p) :
    (pivotEmbedding (q := q) s).conjTranspose * choi T * pivotEmbedding (q := q) s =
      T (Matrix.single s s 1) := by
  rw [Matrix.mul_assoc,choi_mul_pivotEmbedding]
  ext a b
  simp [Matrix.mul_apply,Fintype.sum_prod_type,pivotEmbedding,Matrix.one_apply,
    choiPivotColumn,Matrix.conjTranspose_apply,apply_ite]

theorem quadratic_colMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℂ) (z : n → ℂ) :
    star z ⬝ᵥ W.mulVec z =
      ((show Matrix n (Fin 1) ℂ from fun i _ => z i).conjTranspose * W *
       (show Matrix n (Fin 1) ℂ from fun i _ => z i)) 0 0 := by
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,dotProduct,Matrix.mulVec,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

theorem schur_pivot_matrix_identity {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (W : Matrix n n ℂ) (D : Matrix n m ℂ)
    (G : Matrix m m ℂ) (Z : Matrix n (Fin 1) ℂ)
    (hW : W.IsHermitian) (hG : G.IsHermitian)
    (hGinv : G * (D.conjTranspose * W * D) * G = G) :
    let E := W * D
    let K := D * G * E.conjTranspose * Z
    (Z-K).conjTranspose * W * (Z-K) = Z.conjTranspose * (W-E*G*E.conjTranspose) * Z := by
  dsimp only
  let E := W * D
  let K := D * G * E.conjTranspose * Z
  change (Z-K).conjTranspose * W * (Z-K) = Z.conjTranspose * (W-E*G*E.conjTranspose) * Z
  have hE : E.conjTranspose = D.conjTranspose * W := by
    simp only [E,Matrix.conjTranspose_mul,hW.eq]
  have hWK : W*K = E*G*E.conjTranspose*Z := by
    simp only [K,E,Matrix.mul_assoc]
  have hKW : K.conjTranspose*W = Z.conjTranspose*E*G*E.conjTranspose := by
    simp only [K,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hG.eq,hE,
      E,Matrix.conjTranspose_mul,hW.eq,Matrix.mul_assoc]
  have hKWK : K.conjTranspose*W*K = Z.conjTranspose*E*G*E.conjTranspose*Z := by
    calc
      _ = Z.conjTranspose*E*(G*(D.conjTranspose*W*D)*G)*E.conjTranspose*Z := by
        simp only [K,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hG.eq,hE,
          E,Matrix.conjTranspose_mul,hW.eq,Matrix.mul_assoc]
      _ = _ := by rw [hGinv]
  calc
    _ = Z.conjTranspose*W*Z - Z.conjTranspose*(W*K) - (K.conjTranspose*W)*Z + K.conjTranspose*W*K := by
      simp only [Matrix.conjTranspose_sub,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_assoc]
      abel
    _ = Z.conjTranspose*(W-E*G*E.conjTranspose)*Z := by
      rw [hKWK,hWK,hKW]
      simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
      abel
theorem schmidt_rank_add_product {n m k : ℕ} (z : Fin n × Fin m → ℂ)
    (v : Fin n → ℂ) (w : Fin m → ℂ) (hz : SchmidtRankAtMost k z) :
    SchmidtRankAtMost (k+1) (fun x => z x + v x.1 * w x.2) := by
  obtain ⟨v',w',hv⟩ := hz
  refine ⟨Fin.lastCases v v',Fin.lastCases w w',?_⟩
  intro i a
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
  rw [← hv]

theorem pivotEmbedding_mulVec {p q : ℕ} (s : Fin p) (u : Fin q → ℂ)
    (i : Fin p) (a : Fin q) :
    (pivotEmbedding s).mulVec u (i,a) = (if i=s then 1 else 0) * u a := by
  by_cases h : i = s <;> simp [pivotEmbedding,Matrix.mulVec,dotProduct,Matrix.one_apply,apply_ite,h]

theorem choi_pivot_residual_kpositive {p q k : ℕ} (T : MatrixMap p q)
    (hT : IsKPositiveMap (k+1) T) (hH : (choi T).IsHermitian)
    (s : Fin p) (G : Matrix (Fin q) (Fin q) ℂ) (hG : G.PosSemidef)
    (hGinv : G * T (Matrix.single s s 1) * G = G) :
    IsKPositiveMap k (T - mapFromChoi (choiPivot T s G)) := by
  let W := choi T
  let D := pivotEmbedding (q := q) s
  let E := W*D
  let F := mapFromChoi (choiPivot T s G)
  have hE : E = choiPivotColumn T s := choi_mul_pivotEmbedding T s
  have hpivot : choi F = E*G*E.conjTranspose := by
    change choi (mapFromChoi (choiPivot T s G)) = _
    rw [choi_mapFromChoi]
    simp only [choiPivot,hE]
  have hmat : choi (T-F) = W-E*G*E.conjTranspose := by
    ext ⟨i,a⟩ ⟨j,b⟩
    change T (Matrix.single i j 1) a b - F (Matrix.single i j 1) a b = _
    change choi T (i,a) (j,b) - choi F (i,a) (j,b) = _
    rw [hpivot]
    rfl
  have hP : (E*G*E.conjTranspose).PosSemidef := hG.mul_mul_conjTranspose_same E
  apply choi_kblock_implies_kpositive
  · rw [hmat]
    exact hH.sub hP.isHermitian
  · rw [hmat]
    have hBlock := kpositive_implies_choi_kblock T hT
    intro z hz
    let Z : Matrix (Fin p × Fin q) (Fin 1) ℂ := fun x _ => z x
    let t : Fin q → ℂ := fun a => (G*E.conjTranspose*Z) a 0
    let z' : Fin p × Fin q → ℂ := fun x => z x - (if x.1=s then 1 else 0) * t x.2
    have hz' : SchmidtRankAtMost (k+1) z' := by
      have hs := schmidt_rank_add_product z (fun i => -(if i=s then (1:ℂ) else 0)) t hz
      simpa only [z',neg_mul,sub_eq_add_neg] using hs
    have hK : ∀ x, (D*G*E.conjTranspose*Z) x 0 = (if x.1=s then 1 else 0) * t x.2 := by
      intro ⟨i,a⟩
      by_cases h : i = s <;> simp [D,pivotEmbedding,Matrix.mul_apply,Matrix.one_apply,t,apply_ite,Matrix.mul_assoc,h]
    have hZ : (show Matrix (Fin p × Fin q) (Fin 1) ℂ from fun x _ => z' x) =
        Z-D*G*E.conjTranspose*Z := by
      ext x u
      fin_cases u
      change z' x = z x - (D*G*E.conjTranspose*Z) x 0
      rw [hK]
    have hGI : G*(D.conjTranspose*W*D)*G = G := by
      rw [pivotEmbedding_choi_pivot]
      exact hGinv
    have hquad : star z' ⬝ᵥ W.mulVec z' = star z ⬝ᵥ (W-E*G*E.conjTranspose).mulVec z := by
      rw [quadratic_colMatrix,quadratic_colMatrix,hZ]
      have heq := schur_pivot_matrix_identity W D G Z hH hG.isHermitian hGI
      exact congrFun (congrFun heq 0) 0
    have hh := hBlock z' hz'
    change 0 ≤ star z' ⬝ᵥ W.mulVec z' at hh
    rw [hquad] at hh
    exact hh

/-- Choi decomposition at any chosen input index, including singular pivot
blocks. The original Choi operator is explicitly assumed Hermitian. -/
theorem choi_decomposition_step {p q k : ℕ} (T : MatrixMap p q)
    (hT : IsKPositiveMap (k+1) T) (hH : (choi T).IsHermitian)
    (hk : 1 ≤ k) (s : Fin p) :
    ∃ F : MatrixMap p q, IsCompletelyPositiveMap F ∧ IsKPositiveMap k (T-F) ∧
      (∀ i, (T-F) (Matrix.single i s 1) = 0 ∧ (T-F) (Matrix.single s i 1) = 0) ∧
      (∀ t, (∀ j, T (Matrix.single t j 1) = 0) →
        ∀ j, F (Matrix.single t j 1) = 0 ∧ F (Matrix.single j t 1) = 0) := by
  have h2 : IsKPositiveMap 2 T := kpositive_mono T hH hT (by omega)
  obtain ⟨G,hG,hGBG,hBGB,hs⟩ := two_positive_choi_pivot_support T h2 hH s
  let W := choiPivot T s G
  have hW : W.PosSemidef := hG.mul_mul_conjTranspose_same (choiPivotColumn T s)
  let F : MatrixMap p q := mapFromChoi W
  have hF : IsCompletelyPositiveMap F := by
    apply choi_positive_implies_complete_positive
    change (choi (mapFromChoi W)).PosSemidef
    rw [choi_mapFromChoi]
    exact hW
  have hR : IsKPositiveMap k (T-F) := choi_pivot_residual_kpositive T hT hH s G hG hGBG
  have hcol (i : Fin p) :
      W.submatrix (fun a => (i,a)) (fun b => (s,b)) = T (Matrix.single i s 1) := by
    rw [choiPivot_block]
    have hB : (T (Matrix.single s s 1)).IsHermitian := (two_positive_choi_diagonal T h2 s).isHermitian
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
  refine ⟨F,hF,hR,?_,?_⟩
  · intro i
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
  · intro t ht j
    have hzero := ht s
    have hzeroRow : W.submatrix (fun a => (t,a)) (fun b => (j,b)) = 0 := by
      rw [choiPivot_block,hzero]
      simp
    have hzeroCol : W.submatrix (fun a => (j,a)) (fun b => (t,b)) = 0 := by
      rw [choiPivot_block,hzero]
      simp
    constructor <;> ext a b
    · have hf := congrFun (congrFun (choi_mapFromChoi W) (t,a)) (j,b)
      change F (Matrix.single t j 1) a b = W (t,a) (j,b) at hf
      rw [hf]
      exact congrFun (congrFun hzeroRow a) b
    · have hf := congrFun (congrFun (choi_mapFromChoi W) (j,a)) (t,b)
      change F (Matrix.single j t 1) a b = W (j,a) (t,b) at hf
      rw [hf]
      exact congrFun (congrFun hzeroCol a) b

end PPTQubit
#print axioms PPTQubit.schur_pivot_matrix_identity

#print axioms PPTQubit.choi_pivot_residual_kpositive

#print axioms PPTQubit.choi_decomposition_step
