import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
The auxiliary qutrit operator in Sec. S3 of the manuscript.

The theorem auxiliary_lift_exists proves the qutrit lift from the two
positive input blocks for every finite dimension, including singular B.
It proves the existence and properties of the generalized inverse and the
necessary support relations, rather than assuming them.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
noncomputable section

namespace PPTQubit

set_option linter.unusedSimpArgs false

abbrev Block (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def delta {n : ℕ} (A X Y G : Block n) : Block n :=
  A - X * G * X - Y * G * Y

def aux {n : ℕ} (A B X Y G : Block n) : Matrix (Fin 3) (Fin 3) (Block n) :=
  !![X * G * X + (1 / 2 : ℂ) • delta A X Y G,
     -(1 / 2 : ℂ) • (X * G * Y + Y * G * X), X;
     -(1 / 2 : ℂ) • (X * G * Y + Y * G * X),
     Y * G * Y + (1 / 2 : ℂ) • delta A X Y G, -Y;
     X, -Y, B]

def V : Matrix (Fin 2) (Fin 3) ℂ :=
  !![1, -Complex.I, 0; 0, 0, 1]

def transfer {n : ℕ} (Q : Matrix (Fin 3) (Fin 3) (Block n)) :
    Matrix (Fin 2) (Fin 2) (Block n) :=
  fun i j => ∑ k, ∑ l, (V i k * star (V j l)) • Q k l

theorem scalar_recovery (a u v w z : ℂ) :
 u + (1/2:ℂ) * (a-u-v) +
 (-(Complex.I*((1/2:ℂ)*z)) + -(Complex.I*((1/2:ℂ)*w))) +
 (Complex.I*((1/2:ℂ)*z)+Complex.I*((1/2:ℂ)*w) +
 (v + (1/2:ℂ)*(a-u-v))) = a := by
  ring

theorem block_symm {n : ℕ} (A B X Y G : Block n) :
    (aux A B X Y G).transpose = aux A B X Y G := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem recov {n : ℕ} (A B X Y G : Block n) :
    transfer (aux A B X Y G) =
      !![A, X + Complex.I • Y; X - Complex.I • Y, B] := by
  ext i j a b
  fin_cases i <;> fin_cases j <;>
    simp [transfer, V, aux, delta, Fin.sum_univ_succ]
  all_goals try (simp only [sub_eq_add_neg]; done)
  simpa only [one_div] using scalar_recovery (A a b)
    ((X * G * X) a b) ((Y * G * Y) a b)
    ((Y * G * X) a b) ((X * G * Y) a b)

def gramBlocks {n : ℕ} (B X Y G : Block n) : Matrix (Fin 3) (Fin 3) (Block n) :=
  !![X * G * X, -(X * G * Y), X * G * B;
     -(Y * G * X), Y * G * Y, -(Y * G * B);
     B * G * X, -(B * G * Y), B * G * B]

def residualBlocks {n : ℕ} (A X Y G : Block n) :
    Matrix (Fin 3) (Fin 3) (Block n) :=
  let D := delta A X Y G
  let W := Y * G * X - X * G * Y
  !![(1/2 : ℂ) • D, -(1/2 : ℂ) • W, 0;
     (1/2 : ℂ) • W, (1/2 : ℂ) • D, 0;
     0, 0, 0]

theorem aux_split {n : ℕ} (A B X Y G : Block n)
    (hXB : X * G * B = X) (hYB : Y * G * B = Y)
    (hBX : B * G * X = X) (hBY : B * G * Y = Y)
    (hBB : B * G * B = B) :
    aux A B X Y G = gramBlocks B X Y G + residualBlocks A X Y G := by
  ext i j a b
  fin_cases i <;> fin_cases j <;>
    dsimp [aux, gramBlocks, residualBlocks, delta, Matrix.vecCons,
      Matrix.vecHead, Matrix.vecTail, Matrix.add_apply, Matrix.sub_apply,
      Matrix.neg_apply, Matrix.smul_apply]
  all_goals simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ,
    show (2 : Fin 3) = Fin.succ (1 : Fin 2) by decide, hXB, hYB, hBX, hBY, hBB,
    smul_eq_mul, Matrix.zero_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.neg_apply, Matrix.smul_apply, add_zero, neg_neg]
  all_goals ring

def flatten {n : ℕ} (Q : Matrix (Fin 3) (Fin 3) (Block n)) :
    Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ :=
  fun ia jb => Q ia.1 jb.1 ia.2 jb.2

def flatten2 {n : ℕ} (Q : Matrix (Fin 2) (Fin 2) (Block n)) :
    Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ :=
  fun ia jb => Q ia.1 jb.1 ia.2 jb.2

def productToSum {n : ℕ} (ia : Fin 2 × Fin n) : Fin n ⊕ Fin n :=
  if ia.1 = 0 then Sum.inl ia.2 else Sum.inr ia.2

def sumToProduct {n : ℕ} : Fin n ⊕ Fin n → Fin 2 × Fin n
  | Sum.inl a => (0, a)
  | Sum.inr a => (1, a)

theorem input_block_encoding {n : ℕ} (A B C D : Block n) :
    flatten2 !![A, C; D, B] =
      (Matrix.fromBlocks A C D B).submatrix productToSum productToSum := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases j <;> rfl

theorem input_block_encoding_reverse {n : ℕ} (A B C D : Block n) :
    Matrix.fromBlocks A C D B =
      (flatten2 !![A, C; D, B]).submatrix sumToProduct sumToProduct := by
  ext (a | a) (b | b) <;> rfl

theorem input_block_psd_iff {n : ℕ} (A B C D : Block n) :
    (flatten2 !![A, C; D, B]).PosSemidef ↔
      (Matrix.fromBlocks A C D B).PosSemidef := by
  constructor
  · intro h
    rw [input_block_encoding_reverse]
    exact h.submatrix sumToProduct
  · intro h
    rw [input_block_encoding]
    exact h.submatrix productToSum

def liftedV {n : ℕ} : Matrix (Fin 2 × Fin n) (Fin 3 × Fin n) ℂ :=
  Matrix.kronecker V (1 : Block n)

theorem transfer_is_congruence {n : ℕ} (Q : Matrix (Fin 3) (Fin 3) (Block n)) :
    flatten2 (transfer Q) = liftedV * flatten Q * (liftedV (n := n)).conjTranspose := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change (∑ k, ∑ l, (V i k * star (V j l)) * Q k l a b) =
    ∑ p : Fin 3 × Fin n, (∑ q : Fin 3 × Fin n,
      liftedV (i,a) q * flatten Q q p) * star (liftedV (j,b) p)
  simp [liftedV, flatten, Matrix.kronecker_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, apply_ite, ite_mul, mul_ite,
    mul_assoc, mul_comm, mul_left_comm]
  exact Finset.sum_comm

def qutritPartialTranspose {n : ℕ}
    (Q : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) :
    Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ :=
  fun ia jb => Q (jb.1, ia.2) (ia.1, jb.2)

theorem auxiliary_pt_invariant {n : ℕ} (A B X Y G : Block n) :
    qutritPartialTranspose (flatten (aux A B X Y G)) = flatten (aux A B X Y G) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change (aux A B X Y G) j i a b = (aux A B X Y G) i j a b
  have h := congrFun (congrFun (block_symm A B X Y G) i) j
  change (aux A B X Y G) j i = (aux A B X Y G) i j at h
  exact congrFun (congrFun h a) b

def Kmat {n : ℕ} (B X Y : Block n) :
    Matrix (Fin 3 × Fin n) (Fin n) ℂ :=
  fun ia b => (![X, -Y, B] ia.1) ia.2 b

def gramRaw {n : ℕ} (B X Y G : Block n) : Matrix (Fin 3) (Fin 3) (Block n) :=
  fun i j => ![X, -Y, B] i * G * (![X, -Y, B] j).conjTranspose

theorem gram_raw_flatten {n : ℕ} (B X Y G : Block n) :
    flatten (gramRaw B X Y G) = Kmat B X Y * G * (Kmat B X Y).conjTranspose := by
  ext ⟨i,a⟩ ⟨j,b⟩
  rfl

theorem gram_raw_blocks {n : ℕ} (B X Y G : Block n)
    (hB : B.IsHermitian) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    gramRaw B X Y G = gramBlocks B X Y G := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp [gramRaw, gramBlocks, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail]
  all_goals simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ,
    show (2 : Fin 3) = Fin.succ (1 : Fin 2) by decide,
    Matrix.conjTranspose_neg, hX.eq, hY.eq, hB.eq, neg_mul, mul_neg,
    Matrix.neg_apply, neg_neg]

theorem gram_psd {n : ℕ} (B X Y G : Block n)
    (hB : B.IsHermitian) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hG : G.PosSemidef) : (flatten (gramBlocks B X Y G)).PosSemidef := by
  rw [← gram_raw_blocks B X Y G hB hX hY, gram_raw_flatten]
  exact hG.mul_mul_conjTranspose_same (Kmat B X Y)

def scalarEmbed {n : ℕ} (c : Fin 3 → ℂ) :
    Matrix (Fin 3 × Fin n) (Fin n) ℂ :=
  fun ia b => if ia.2 = b then c ia.1 else 0

theorem scalar_embed_formula {n : ℕ} (c : Fin 3 → ℂ) (H : Block n) :
    scalarEmbed c * H * (scalarEmbed c).conjTranspose =
      fun ia jb => (c ia.1 * star (c jb.1)) * H ia.2 jb.2 := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change (∑ k, (∑ l, scalarEmbed c (i,a) l * H l k) *
      star (scalarEmbed c (j,b) k)) = _
  simp [scalarEmbed, apply_ite, mul_ite, ite_mul, Finset.sum_mul, mul_assoc, mul_comm,
    mul_left_comm]

def cplus : Fin 3 → ℂ := ![(1/2 : ℂ), Complex.I / 2, 0]
def cminus : Fin 3 → ℂ := ![(1/2 : ℂ), -Complex.I / 2, 0]

def residualOf {n : ℕ} (D W : Block n) : Matrix (Fin 3) (Fin 3) (Block n) :=
  !![(1/2 : ℂ) • D, -(1/2 : ℂ) • W, 0;
     (1/2 : ℂ) • W, (1/2 : ℂ) • D, 0;
     0, 0, 0]

theorem residual_factorization {n : ℕ} (D W : Block n) :
    flatten (residualOf D W) =
      scalarEmbed (n := n) cplus * (D - Complex.I • W) * (scalarEmbed (n := n) cplus).conjTranspose +
      scalarEmbed (n := n) cminus * (D + Complex.I • W) * (scalarEmbed (n := n) cminus).conjTranspose := by
  have starTwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    change star (2 : ℂ) = 2
    simp
  have hp := scalar_embed_formula cplus (D - Complex.I • W)
  have hm := scalar_embed_formula cminus (D + Complex.I • W)
  apply Eq.trans ?_ (congrArg₂
    (fun (P Q : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) => P + Q) hp hm).symm
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases j <;>
    dsimp [flatten, residualOf, cplus, cminus, Matrix.vecCons, Matrix.vecHead,
      Matrix.vecTail, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply]
  all_goals simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ,
    show (2 : Fin 3) = Fin.succ (1 : Fin 2) by decide,
    Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
    Matrix.zero_apply, smul_eq_mul, map_div, map_neg, map_zero, map_one,
    Complex.star_def, Complex.conj_I, Complex.conj_ofNat, map_ofNat]
  all_goals ring_nf
  all_goals simp [Complex.I_sq, starTwo]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals ring

theorem residual_psd {n : ℕ} (D W : Block n)
    (hminus : (D - Complex.I • W).PosSemidef)
    (hplus : (D + Complex.I • W).PosSemidef) :
    (flatten (residualOf D W)).PosSemidef := by
  rw [residual_factorization]
  exact (hminus.mul_mul_conjTranspose_same (scalarEmbed (n := n) cplus)).add
    (hplus.mul_mul_conjTranspose_same (scalarEmbed (n := n) cminus))

theorem aux_psd {n : ℕ} (A B X Y G : Block n)
    (hB : B.IsHermitian) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hG : G.PosSemidef)
    (hXB : X * G * B = X) (hYB : Y * G * B = Y)
    (hBX : B * G * X = X) (hBY : B * G * Y = Y)
    (hBB : B * G * B = B)
    (hminus : (delta A X Y G - Complex.I • (Y * G * X - X * G * Y)).PosSemidef)
    (hplus : (delta A X Y G + Complex.I • (Y * G * X - X * G * Y)).PosSemidef) :
    (flatten (aux A B X Y G)).PosSemidef := by
  rw [aux_split A B X Y G hXB hYB hBX hBY hBB]
  change (flatten (gramBlocks B X Y G) +
    flatten (residualOf (delta A X Y G) (Y * G * X - X * G * Y))).PosSemidef
  exact (gram_psd B X Y G hB hX hY hG).add
    (residual_psd (delta A X Y G) (Y * G * X - X * G * Y) hminus hplus)

theorem complex_block_plus {n : ℕ} (X Y G : Block n) :
    (X + Complex.I • Y) * G * (X - Complex.I • Y) =
      X * G * X + Y * G * Y + Complex.I • (Y * G * X - X * G * Y) := by
  simp only [add_mul, sub_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_sub, neg_one_smul, smul_neg, smul_smul,
    Complex.I_mul_I, neg_smul, one_smul]
  abel

theorem complex_block_minus {n : ℕ} (X Y G : Block n) :
    (X - Complex.I • Y) * G * (X + Complex.I • Y) =
      X * G * X + Y * G * Y - Complex.I • (Y * G * X - X * G * Y) := by
  simp only [add_mul, sub_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_sub, neg_one_smul, smul_neg, smul_smul,
    Complex.I_mul_I, neg_smul, one_smul]
  abel

theorem schur_from_positive {n : ℕ} (A B C G : Block n)
    (hG : G.IsHermitian) (hGBG : G * B * G = G)
    (hR : (Matrix.fromBlocks A C C.conjTranspose B).PosSemidef) :
    (A - C * G * C.conjTranspose).PosSemidef := by
  let T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    Matrix.fromBlocks 1 0 (-(G * C.conjTranspose)) 1
  have h := (hR.conjTranspose_mul_mul_same T).submatrix
    (Sum.inl : Fin n → Fin n ⊕ Fin n)
  have heq : (T.conjTranspose * Matrix.fromBlocks A C C.conjTranspose B * T).submatrix
      (Sum.inl : Fin n → Fin n ⊕ Fin n) (Sum.inl : Fin n → Fin n ⊕ Fin n) =
      A - C * G * C.conjTranspose := by
    dsimp only [T]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hG.eq, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add, neg_mul, mul_neg]
    change A + -(C * G * C.conjTranspose) +
      -((C + -(C * G * B)) * (G * C.conjTranspose)) =
        A - C * G * C.conjTranspose
    have hz : (C + -(C * G * B)) * (G * C.conjTranspose) = 0 := by
      calc
        _ = C * (G - G * B * G) * C.conjTranspose := by noncomm_ring
        _ = 0 := by rw [hGBG]; simp
    rw [hz]
    abel
  rw [heq] at h
  exact h

theorem psd_zero_diagonal {m : Type} [Fintype m] [DecidableEq m]
    (H : Matrix m m ℂ) (hH : H.PosSemidef) (i j : m)
    (hzero : H i i = 0) : H i j = 0 := by
  let f : Fin 2 → m := ![i,j]
  have hdet : 0 ≤ (H.submatrix f f).det := (hH.submatrix f).det_nonneg
  have hc : H j i = star (H i j) := (hH.isHermitian.apply j i).symm
  have heq : (H.submatrix f f).det = -((Complex.normSq (H i j)) : ℂ) := by
    rw [Matrix.det_fin_two]
    simp [Matrix.submatrix, f, hzero, hc, Complex.mul_conj]
  rw [heq] at hdet
  have hreal : 0 ≤ -Complex.normSq (H i j) := by
    have h := (Complex.nonneg_iff.mp hdet).1
    simpa using h
  have hz : Complex.normSq (H i j) = 0 :=
    le_antisymm (neg_nonneg.mp hreal) (Complex.normSq_nonneg _)
  exact Complex.normSq_eq_zero.mp hz

theorem positive_block_support {n : ℕ} (A B C G : Block n)
    (hB : B.IsHermitian) (hG : G.IsHermitian) (hBGB : B * G * B = B)
    (hR : (Matrix.fromBlocks A C C.conjTranspose B).PosSemidef) :
    C * G * B = C := by
  let E : Block n := 1 - G * B
  have hEB : E.conjTranspose * B = 0 := by
    dsimp [E]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, hB.eq, hG.eq, sub_mul, one_mul, hBGB, sub_self]
  let T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    Matrix.fromBlocks 1 0 0 E
  have hR' : (Matrix.fromBlocks A (C * E) (E.conjTranspose * C.conjTranspose)
      (0 : Block n)).PosSemidef := by
    have h := hR.conjTranspose_mul_mul_same T
    dsimp only [T] at h
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply] at h
    simpa only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
      Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, mul_assoc, hEB] using h
  have hCE : C * E = 0 := by
    ext a b
    let H := Matrix.fromBlocks A (C * E) (E.conjTranspose * C.conjTranspose)
      (0 : Block n)
    have hzero : H (Sum.inr b) (Sum.inr b) = 0 := by rfl
    have hrow := psd_zero_diagonal H hR' (Sum.inr b) (Sum.inl a) hzero
    have hherm := hR'.isHermitian.apply (Sum.inl a) (Sum.inr b)
    change star (H (Sum.inr b) (Sum.inl a)) = (C * E) a b at hherm
    simpa only [hrow, star_zero, Matrix.zero_apply] using hherm.symm
  dsimp [E] at hCE
  have heq : C * G * B = C - C * (1 - G * B) := by noncomm_ring
  rw [hCE] at heq
  simpa using heq


theorem auxiliary_certificate {n : ℕ} (A B X Y G : Block n)
    (hB : B.IsHermitian) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hG : G.PosSemidef)
    (hXB : X * G * B = X) (hYB : Y * G * B = Y)
    (hBB : B * G * B = B)
    (hSchurC : (A - (X + Complex.I • Y) * G * (X - Complex.I • Y)).PosSemidef)
    (hSchurAdj : (A - (X - Complex.I • Y) * G * (X + Complex.I • Y)).PosSemidef) :
    (flatten (aux A B X Y G)).PosSemidef ∧
    (aux A B X Y G).transpose = aux A B X Y G ∧
    transfer (aux A B X Y G) =
      !![A, X + Complex.I • Y; X - Complex.I • Y, B] := by
  have hBX : B * G * X = X := by
    have h := congrArg Matrix.conjTranspose hXB
    simpa only [Matrix.conjTranspose_mul, hB.eq, hX.eq, hG.isHermitian.eq, mul_assoc] using h
  have hBY : B * G * Y = Y := by
    have h := congrArg Matrix.conjTranspose hYB
    simpa only [Matrix.conjTranspose_mul, hB.eq, hY.eq, hG.isHermitian.eq, mul_assoc] using h
  have hm : (delta A X Y G - Complex.I • (Y * G * X - X * G * Y)).PosSemidef := by
    have heq : A - (X + Complex.I • Y) * G * (X - Complex.I • Y) =
        delta A X Y G - Complex.I • (Y * G * X - X * G * Y) := by
      rw [complex_block_plus]
      dsimp [delta]
      abel
    rw [← heq]
    exact hSchurC
  have hp : (delta A X Y G + Complex.I • (Y * G * X - X * G * Y)).PosSemidef := by
    have heq : A - (X - Complex.I • Y) * G * (X + Complex.I • Y) =
        delta A X Y G + Complex.I • (Y * G * X - X * G * Y) := by
      rw [complex_block_minus]
      dsimp [delta]
      abel
    rw [← heq]
    exact hSchurAdj
  exact ⟨aux_psd A B X Y G hB hX hY hG hXB hYB hBX hBY hBB hm hp,
    block_symm A B X Y G, recov A B X Y G⟩

theorem auxiliary_from_positive_blocks {n : ℕ} (A B X Y G : Block n)
    (hB : B.IsHermitian) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hG : G.PosSemidef) (hGBG : G * B * G = G)
    (hXB : X * G * B = X) (hYB : Y * G * B = Y)
    (hBGB : B * G * B = B)
    (hR : (Matrix.fromBlocks A (X + Complex.I • Y) (X - Complex.I • Y) B).PosSemidef)
    (hRPT : (Matrix.fromBlocks A (X - Complex.I • Y) (X + Complex.I • Y) B).PosSemidef) :
    (flatten (aux A B X Y G)).PosSemidef ∧
    (aux A B X Y G).transpose = aux A B X Y G ∧
    transfer (aux A B X Y G) =
      !![A, X + Complex.I • Y; X - Complex.I • Y, B] := by
  have hC : (X + Complex.I • Y).conjTranspose = X - Complex.I • Y := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hX.eq, hY.eq,
      Complex.star_def, sub_eq_add_neg]
  have hC' : (X - Complex.I • Y).conjTranspose = X + Complex.I • Y := by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hX.eq, hY.eq,
      Complex.star_def]
  have hsC : (A - (X + Complex.I • Y) * G * (X - Complex.I • Y)).PosSemidef := by
    have h := schur_from_positive A B (X + Complex.I • Y) G hG.isHermitian hGBG
      (by simpa only [hC] using hR)
    simpa only [hC] using h
  have hsC' : (A - (X - Complex.I • Y) * G * (X + Complex.I • Y)).PosSemidef := by
    have h := schur_from_positive A B (X - Complex.I • Y) G hG.isHermitian hGBG
      (by simpa only [hC'] using hRPT)
    simpa only [hC'] using h
  exact auxiliary_certificate A B X Y G hB hX hY hG hXB hYB hBGB hsC hsC'

theorem auxiliary_physical_certificate {n : ℕ} (A B X Y G : Block n)
    (hB : B.IsHermitian) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hG : G.PosSemidef) (hGBG : G * B * G = G)
    (hXB : X * G * B = X) (hYB : Y * G * B = Y)
    (hBGB : B * G * B = B)
    (hR : (Matrix.fromBlocks A (X + Complex.I • Y) (X - Complex.I • Y) B).PosSemidef)
    (hRPT : (Matrix.fromBlocks A (X - Complex.I • Y) (X + Complex.I • Y) B).PosSemidef) :
    (flatten (aux A B X Y G)).PosSemidef ∧
    qutritPartialTranspose (flatten (aux A B X Y G)) = flatten (aux A B X Y G) ∧
    liftedV * flatten (aux A B X Y G) * (liftedV (n := n)).conjTranspose =
      flatten2 !![A, X + Complex.I • Y; X - Complex.I • Y, B] := by
  have h := auxiliary_from_positive_blocks A B X Y G hB hX hY hG hGBG hXB hYB hBGB hR hRPT
  refine ⟨h.1, auxiliary_pt_invariant A B X Y G, ?_⟩
  calc
    _ = flatten2 (transfer (aux A B X Y G)) := (transfer_is_congruence _).symm
    _ = _ := congrArg flatten2 h.2.2

theorem psd_commuting_generalized_inverse {n : ℕ} (B : Block n) (hB : B.PosSemidef) :
    ∃ G : Block n, G.PosSemidef ∧ G * B * G = G ∧ B * G * B = B ∧ G * B = B * G := by
  let hH := hB.isHermitian
  let U : Block n := hH.eigenvectorUnitary
  let d : Fin n → ℂ := fun i => (hH.eigenvalues i : ℂ)
  let f : Fin n → ℂ := fun i => ((hH.eigenvalues i)⁻¹ : ℝ)
  let D : Block n := Matrix.diagonal d
  let F : Block n := Matrix.diagonal f
  let G : Block n := U * F * U.conjTranspose
  have hU : U.conjTranspose * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hBd : B = U * D * U.conjTranspose := by
    simpa only [U, D, d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_apply] using hH.spectral_theorem
  have hF : F.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    apply Complex.nonneg_iff.mpr
    constructor
    · change 0 ≤ (hH.eigenvalues i)⁻¹
      exact inv_nonneg.mpr (hB.eigenvalues_nonneg i)
    · rfl
  have hdfd : D * F * D = D := by
    dsimp only [D, F]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    dsimp [d, f]
    rw [Complex.ofReal_inv]
    by_cases he : (hH.eigenvalues i : ℂ) = 0
    · simp [he]
    · simp [he, mul_assoc]
  have hfdf : F * D * F = F := by
    dsimp only [D, F]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    dsimp [d, f]
    rw [Complex.ofReal_inv]
    by_cases he : (hH.eigenvalues i : ℂ) = 0
    · simp [he]
    · simp [he, mul_assoc]
  have hmul (S T : Block n) :
      (U * S * U.conjTranspose) * (U * T * U.conjTranspose) =
        U * (S * T) * U.conjTranspose := by
    calc
      _ = U * S * (U.conjTranspose * U) * T * U.conjTranspose := by noncomm_ring
      _ = _ := by rw [hU]; simp [mul_assoc]
  refine ⟨G, hF.mul_mul_conjTranspose_same U, ?_, ?_, ?_⟩
  · rw [hBd]
    change (U * F * U.conjTranspose) * (U * D * U.conjTranspose) *
      (U * F * U.conjTranspose) = U * F * U.conjTranspose
    rw [hmul F D, hmul (F * D) F, hfdf]
  · rw [hBd]
    change (U * D * U.conjTranspose) * (U * F * U.conjTranspose) *
      (U * D * U.conjTranspose) = U * D * U.conjTranspose
    rw [hmul D F, hmul (D * F) D, hdfd]
  · rw [hBd]
    change (U * F * U.conjTranspose) * (U * D * U.conjTranspose) =
      (U * D * U.conjTranspose) * (U * F * U.conjTranspose)
    rw [hmul F D, hmul D F]
    have hcomm : F * D = D * F := by
      dsimp only [F, D]
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    rw [hcomm]

theorem psd_generalized_inverse {n : ℕ} (B : Block n) (hB : B.PosSemidef) :
    ∃ G : Block n, G.PosSemidef ∧ G * B * G = G ∧ B * G * B = B := by
  obtain ⟨G, hG, hGBG, hBGB, _⟩ := psd_commuting_generalized_inverse B hB
  exact ⟨G, hG, hGBG, hBGB⟩



theorem auxiliary_generalized_inverse {n : ℕ} (A B X Y G : Block n)
    (hB : B.IsHermitian) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hG : G.PosSemidef) (hGBG : G * B * G = G) (hBGB : B * G * B = B)
    (hR : (Matrix.fromBlocks A (X + Complex.I • Y) (X - Complex.I • Y) B).PosSemidef)
    (hRPT : (Matrix.fromBlocks A (X - Complex.I • Y) (X + Complex.I • Y) B).PosSemidef) :
    (flatten (aux A B X Y G)).PosSemidef ∧
    qutritPartialTranspose (flatten (aux A B X Y G)) = flatten (aux A B X Y G) ∧
    liftedV * flatten (aux A B X Y G) * (liftedV (n := n)).conjTranspose =
      flatten2 !![A, X + Complex.I • Y; X - Complex.I • Y, B] := by
  have hC : (X + Complex.I • Y).conjTranspose = X - Complex.I • Y := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hX.eq, hY.eq,
      Complex.star_def, sub_eq_add_neg]
  have hC' : (X - Complex.I • Y).conjTranspose = X + Complex.I • Y := by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hX.eq, hY.eq,
      Complex.star_def]
  have hs : (X + Complex.I • Y) * G * B = X + Complex.I • Y :=
    positive_block_support A B (X + Complex.I • Y) G hB hG.isHermitian hBGB
      (by simpa only [hC] using hR)
  have hs' : (X - Complex.I • Y) * G * B = X - Complex.I • Y :=
    positive_block_support A B (X - Complex.I • Y) G hB hG.isHermitian hBGB
      (by simpa only [hC'] using hRPT)
  have hXB : X * G * B = X := by
    ext a b
    have hp := congrFun (congrFun hs a) b
    have hm := congrFun (congrFun hs' a) b
    simp only [add_mul, sub_mul, smul_mul_assoc, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul] at hp hm
    linear_combination (1/2 : ℂ) * hp + (1/2 : ℂ) * hm
  have hYB : Y * G * B = Y := by
    ext a b
    have hp := congrFun (congrFun hs a) b
    have hm := congrFun (congrFun hs' a) b
    simp only [add_mul, sub_mul, smul_mul_assoc, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul] at hp hm
    have hh : Complex.I * ((Y * G * B) a b - Y a b) = 0 := by
      linear_combination (1/2 : ℂ) * hp - (1/2 : ℂ) * hm
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left Complex.I_ne_zero)
  exact auxiliary_physical_certificate A B X Y G hB hX hY hG hGBG hXB hYB hBGB hR hRPT

theorem auxiliary_lift_exists {n : ℕ} (A B X Y : Block n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hR : (Matrix.fromBlocks A (X + Complex.I • Y) (X - Complex.I • Y) B).PosSemidef)
    (hRPT : (Matrix.fromBlocks A (X - Complex.I • Y) (X + Complex.I • Y) B).PosSemidef) :
    ∃ G : Block n,
      G.PosSemidef ∧ G * B * G = G ∧ B * G * B = B ∧
      (flatten (aux A B X Y G)).PosSemidef ∧
      qutritPartialTranspose (flatten (aux A B X Y G)) = flatten (aux A B X Y G) ∧
      liftedV * flatten (aux A B X Y G) * (liftedV (n := n)).conjTranspose =
        flatten2 !![A, X + Complex.I • Y; X - Complex.I • Y, B] := by
  have hB : B.PosSemidef := by
    have hb := hR.submatrix (Sum.inr : Fin n → Fin n ⊕ Fin n)
    change B.PosSemidef at hb
    exact hb
  obtain ⟨G, hG, hGBG, hBGB⟩ := psd_generalized_inverse B hB
  exact ⟨G, hG, hGBG, hBGB, auxiliary_generalized_inverse A B X Y G
    hB.isHermitian hX hY hG hGBG hBGB hR hRPT⟩


theorem auxiliary_positive_definite_corner {n : ℕ} (A B X Y : Block n)
    (hB : B.PosDef) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hR : (Matrix.fromBlocks A (X + Complex.I • Y) (X - Complex.I • Y) B).PosSemidef)
    (hRPT : (Matrix.fromBlocks A (X - Complex.I • Y) (X + Complex.I • Y) B).PosSemidef) :
    (flatten (aux A B X Y B⁻¹)).PosSemidef ∧
    qutritPartialTranspose (flatten (aux A B X Y B⁻¹)) = flatten (aux A B X Y B⁻¹) ∧
    liftedV * flatten (aux A B X Y B⁻¹) * (liftedV (n := n)).conjTranspose =
      flatten2 !![A, X + Complex.I • Y; X - Complex.I • Y, B] := by
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  have hGB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  have hBG : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hdet
  have hGBG : B⁻¹ * B * B⁻¹ = B⁻¹ := by rw [hGB, one_mul]
  have hXB : X * B⁻¹ * B = X := by rw [mul_assoc, hGB, mul_one]
  have hYB : Y * B⁻¹ * B = Y := by rw [mul_assoc, hGB, mul_one]
  have hBGB : B * B⁻¹ * B = B := by rw [hBG, one_mul]
  exact auxiliary_physical_certificate A B X Y B⁻¹ hB.posSemidef.isHermitian hX hY
    hB.posSemidef.inv hGBG hXB hYB hBGB hR hRPT

end PPTQubit

#print axioms PPTQubit.schur_from_positive
#print axioms PPTQubit.input_block_psd_iff
#print axioms PPTQubit.auxiliary_lift_exists
#print axioms PPTQubit.auxiliary_physical_certificate
#print axioms PPTQubit.auxiliary_positive_definite_corner

#print axioms PPTQubit.psd_commuting_generalized_inverse
