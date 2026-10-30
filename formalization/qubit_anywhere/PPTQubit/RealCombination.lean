import PPTQubit.MinorRank
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
The full-column-rank real-combination step in Section S2.

The full-rank existence theorem is proved for arbitrary finite dimensions.
The proof uses the rank/minor equivalence in MinorRank and polynomial
continuation from real to complex pencil parameters.
-/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def realCombination {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ) (u : Fin p → ℝ) :
    Matrix (Fin r) (Fin m) ℂ :=
  ∑ i, (u i : ℂ) • C i

theorem realCombination_single {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ) (i : Fin p) :
    realCombination C (Pi.single i 1) = C i := by
  classical
  simp [realCombination, Pi.single_apply]

theorem realCombination_add {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ) (u v : Fin p → ℝ) :
    realCombination C (u + v) = realCombination C u + realCombination C v := by
  simp [realCombination, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

theorem realCombination_smul {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ) (t : ℝ) (u : Fin p → ℝ) :
    realCombination C (t • u) = (t : ℂ) • realCombination C u := by
  ext a b
  simp only [realCombination, Matrix.sum_apply, Matrix.smul_apply, Pi.smul_apply,
    Complex.ofReal_mul, Finset.mul_sum, mul_assoc, smul_eq_mul]

theorem maximal_real_combination {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ) :
    ∃ u : Fin p → ℝ, ∀ v : Fin p → ℝ,
      (realCombination C v).rank ≤ (realCombination C u).rank := by
  classical
  let P : ℕ → Prop := fun k => ∃ u : Fin p → ℝ, (realCombination C u).rank = k
  have hp0 : P 0 := by
    refine ⟨0, ?_⟩
    simp [realCombination]
  obtain ⟨u, hu⟩ := Nat.findGreatest_spec (Nat.zero_le m) hp0
  refine ⟨u, ?_⟩
  intro v
  rw [hu]
  exact Nat.le_findGreatest (Matrix.rank_le_width (realCombination C v)) ⟨v, rfl⟩

theorem maximal_real_combination_pencil {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ) (u : Fin p → ℝ)
    (hmax : ∀ v : Fin p → ℝ, (realCombination C v).rank ≤ (realCombination C u).rank)
    (i : Fin p) (t : ℝ) :
    (realCombination C u + (t : ℂ) • C i).rank ≤ (realCombination C u).rank := by
  simpa only [realCombination_add, realCombination_smul, realCombination_single] using
    hmax (u + t • (Pi.single i (1 : ℝ) : Fin p → ℝ))

theorem complex_polynomial_vanishing_on_reals (p : Polynomial ℂ)
    (h : ∀ t : ℝ, p.eval (t : ℂ) = 0) :
    p = 0 := by
  by_contra hp
  have hinfinite : {z : ℂ | p.IsRoot z}.Infinite :=
    (Set.infinite_range_of_injective Complex.ofReal_injective).mono (by
      rintro z ⟨t, rfl⟩
      exact h t)
  exact (Polynomial.finite_setOf_isRoot hp).not_infinite hinfinite

theorem determinant_pencil_vanishing_on_reals {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, (A + (t : ℂ) • B).det = 0) (z : ℂ) :
    (A + z • B).det = 0 := by
  let P : Matrix (Fin n) (Fin n) (Polynomial ℂ) :=
    A.map (Polynomial.C (R := ℂ)) +
      (Polynomial.X : Polynomial ℂ) • B.map (Polynomial.C (R := ℂ))
  have heval (w : ℂ) : P.det.eval w = (A + w • B).det := by
    have hmap := (Polynomial.evalRingHom w).map_det P
    change P.det.eval w = _ at hmap
    rw [hmap]
    congr 1
    ext i j
    simp [P, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact mul_comm _ _
  have hp : P.det = 0 := complex_polynomial_vanishing_on_reals P.det (by
    intro t
    rw [heval]
    exact h t)
  rw [← heval, hp]
  simp

theorem minor_pencil_vanishing_on_reals {r m n : ℕ}
    (A B : Matrix (Fin r) (Fin m) ℂ)
    (rows : Fin n → Fin r) (cols : Fin n → Fin m)
    (h : ∀ t : ℝ, ((A + (t : ℂ) • B).submatrix rows cols).det = 0)
    (z : ℂ) :
    ((A + z • B).submatrix rows cols).det = 0 := by
  have hsub (w : ℂ) :
      (A + w • B).submatrix rows cols =
        A.submatrix rows cols + w • B.submatrix rows cols := by
    ext i j
    rfl
  rw [hsub]
  apply determinant_pencil_vanishing_on_reals
  intro t
  rw [← hsub]
  exact h t

theorem rank_le_one_of_cols_in_line {r m : ℕ}
    (A : Matrix (Fin r) (Fin m) ℂ) (v : Fin r → ℂ)
    (h : ∀ j, ∃ c : ℂ, c • v = A.col j) : A.rank ≤ 1 := by
  have hspan : Submodule.span ℂ (Set.range A.col) ≤ Submodule.span ℂ {v} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨c, hc⟩ := h j
    rw [← hc]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton v))
  rw [Matrix.rank_eq_finrank_span_cols]
  have hd := Submodule.finrank_mono hspan
  have hs := finrank_span_le_card (R := ℂ) ({v} : Set (Fin r → ℂ))
  simpa using le_trans hd hs

theorem rank_le_zero_of_one_minors_zero {r m : ℕ}
    (A : Matrix (Fin r) (Fin m) ℂ)
    (h : ∀ (rows : Fin 1 → Fin r) (cols : Fin 1 → Fin m),
      (A.submatrix rows cols).det = 0) : A.rank ≤ 0 := by
  have hA : A = 0 := by
    ext i j
    have hv := h (fun _ => i) (fun _ => j)
    simpa [Matrix.det_fin_one] using hv
  simp [hA]

theorem rank_le_one_of_two_minors_zero {r m : ℕ}
    (A : Matrix (Fin r) (Fin m) ℂ)
    (h : ∀ (rows : Fin 2 → Fin r) (cols : Fin 2 → Fin m),
      (A.submatrix rows cols).det = 0) : A.rank ≤ 1 := by
  classical
  by_cases hz : A = 0
  · simp [hz]
  · have hex : ∃ a b, A a b ≠ 0 := by
      by_contra hab
      push Not at hab
      apply hz
      ext a b
      exact hab a b
    obtain ⟨a, j, hpivot⟩ := hex
    apply rank_le_one_of_cols_in_line A (A.col j)
    intro b
    refine ⟨A a b / A a j, ?_⟩
    funext c
    have hv := h (fun x => if x = 0 then a else c)
      (fun x => if x = 0 then j else b)
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply, if_true, Fin.isValue] at hv
    have heq : A a j * A c b = A a b * A c j := sub_eq_zero.mp hv
    change (A a b / A a j) * A c j = A c b
    apply mul_left_cancel₀ hpivot
    calc
      A a j * ((A a b / A a j) * A c j) = A a b * A c j := by
        field_simp
      _ = A a j * A c b := heq.symm

theorem rank_le_one_iff_two_minors_zero {r m : ℕ}
    (A : Matrix (Fin r) (Fin m) ℂ) :
    A.rank ≤ 1 ↔
      ∀ (rows : Fin 2 → Fin r) (cols : Fin 2 → Fin m),
        (A.submatrix rows cols).det = 0 := by
  constructor
  · intro hr rows cols
    apply large_minor_det_zero
    omega
  · exact rank_le_one_of_two_minors_zero A

theorem maximal_real_pencil_large_minors_zero {p r m n : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ) (u : Fin p → ℝ)
    (hmax : ∀ v : Fin p → ℝ, (realCombination C v).rank ≤ (realCombination C u).rank)
    (i : Fin p) (hn : (realCombination C u).rank < n)
    (rows : Fin n → Fin r) (cols : Fin n → Fin m) (z : ℂ) :
    ((realCombination C u + z • C i).submatrix rows cols).det = 0 := by
  apply minor_pencil_vanishing_on_reals
  intro t
  apply large_minor_det_zero
  exact lt_of_le_of_lt (maximal_real_combination_pencil C u hmax i t) hn

theorem real_combinations_cross {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ)
    (h : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i)
    (u v : Fin p → ℝ) :
    (realCombination C u).conjTranspose * realCombination C v =
      (realCombination C v).conjTranspose * realCombination C u := by
  simp only [realCombination, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [h j i, mul_comm]

theorem positive_marginal_no_common_kernel {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (x : Fin m → ℂ) (hx : ∀ i, (C i).mulVec x = 0) :
    x = 0 := by
  have hzero : (∑ i, (C i).conjTranspose * C i).mulVec x = 0 := by
    rw [Matrix.sum_mulVec]
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Matrix.mulVec_mulVec, hx i, Matrix.mulVec_zero]
  apply (Matrix.mulVec_injective_iff_isUnit.mpr hpos.isUnit)
  simpa using hzero

theorem full_rank_one_column {p r : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin 1) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef) :
    ∃ u : Fin p → ℝ, Function.Injective (realCombination C u).mulVec := by
  have hsome : ∃ i, (C i).mulVec (fun _ => 1) ≠ 0 := by
    by_contra h
    push Not at h
    have hzero := positive_marginal_no_common_kernel C hpos (fun _ => 1) h
    have hvalue := congrFun hzero (0 : Fin 1)
    norm_num at hvalue
  obtain ⟨i, hi⟩ := hsome
  have hrow : ∃ a : Fin r, C i a 0 ≠ 0 := by
    by_contra h
    push Not at h
    apply hi
    funext a
    simp [Matrix.mulVec, dotProduct, h a]
  obtain ⟨a, ha⟩ := hrow
  have hinj : Function.Injective (C i).mulVec := by
    intro x y hxy
    have hvalue := congrFun hxy a
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one] at hvalue
    have hscalar : x 0 = y 0 := mul_left_cancel₀ ha hvalue
    funext b
    fin_cases b
    exact hscalar
  refine ⟨Pi.single i 1, ?_⟩
  simpa only [realCombination_single] using hinj

theorem complex_pencil_gram {r m : ℕ}
    (A B : Matrix (Fin r) (Fin m) ℂ)
    (hAB : A.conjTranspose * B = B.conjTranspose * A) :
    (A + Complex.I • B).conjTranspose * (A + Complex.I • B) =
      A.conjTranspose * A + B.conjTranspose * B := by
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_I, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  simp only [smul_add, neg_smul]
  rw [hAB]
  simp only [neg_one_smul, smul_neg, smul_smul, Complex.I_mul_I]
  abel

theorem complex_pencil_kernel {r m : ℕ}
    (A B : Matrix (Fin r) (Fin m) ℂ)
    (hAB : A.conjTranspose * B = B.conjTranspose * A)
    (x : Fin m → ℂ) :
    (A + Complex.I • B).mulVec x = 0 ↔
      A.mulVec x = 0 ∧ B.mulVec x = 0 := by
  constructor
  · intro hx
    have hg : (A.conjTranspose * A + B.conjTranspose * B).mulVec x = 0 := by
      rw [← complex_pencil_gram A B hAB, ← Matrix.mulVec_mulVec, hx,
        Matrix.mulVec_zero]
    have hs : star x ⬝ᵥ (A.conjTranspose * A).mulVec x +
        star x ⬝ᵥ (B.conjTranspose * B).mulVec x = 0 := by
      rw [← dotProduct_add, ← Matrix.add_mulVec, hg, dotProduct_zero]
    have ha := (Matrix.posSemidef_conjTranspose_mul_self A).dotProduct_mulVec_nonneg x
    have hb := (Matrix.posSemidef_conjTranspose_mul_self B).dotProduct_mulVec_nonneg x
    obtain ⟨ha0, hb0⟩ := (add_eq_zero_iff_of_nonneg ha hb).mp hs
    constructor
    · apply dotProduct_star_self_eq_zero.mp
      simpa only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.star_mulVec] using ha0
    · apply dotProduct_star_self_eq_zero.mp
      simpa only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.star_mulVec] using hb0
  · rintro ⟨ha, hb⟩
    simp [Matrix.add_mulVec, Matrix.smul_mulVec, ha, hb]

theorem kernel_inclusion_of_complex_pencil_rank {r m : ℕ}
    (A B : Matrix (Fin r) (Fin m) ℂ)
    (hAB : A.conjTranspose * B = B.conjTranspose * A)
    (hrank : (A + Complex.I • B).rank ≤ A.rank)
    (x : Fin m → ℂ) (hx : A.mulVec x = 0) : B.mulVec x = 0 := by
  let F := Matrix.toLin' A
  let G := Matrix.toLin' (A + Complex.I • B)
  have hF : A.rank = Module.finrank ℂ F.range := by
    rw [Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun ℂ (Fin r))
      (Pi.basisFun ℂ (Fin m)), Matrix.toLin_eq_toLin']
  have hG : (A + Complex.I • B).rank = Module.finrank ℂ G.range := by
    rw [Matrix.rank_eq_finrank_range_toLin (A + Complex.I • B)
      (Pi.basisFun ℂ (Fin r)) (Pi.basisFun ℂ (Fin m)), Matrix.toLin_eq_toLin']
  have hker : G.ker ≤ F.ker := by
    intro y hy
    change (A + Complex.I • B).mulVec y = 0 at hy
    change A.mulVec y = 0
    exact (complex_pencil_kernel A B hAB y).mp hy |>.1
  have hdim : Module.finrank ℂ F.ker ≤ Module.finrank ℂ G.ker := by
    have hFdim := LinearMap.finrank_range_add_finrank_ker F
    have hGdim := LinearMap.finrank_range_add_finrank_ker G
    rw [hG, hF] at hrank
    omega
  have heq : G.ker = F.ker := Submodule.eq_of_le_of_finrank_le hker hdim
  have hxF : x ∈ F.ker := hx
  have hxG : x ∈ G.ker := heq.symm ▸ hxF
  change (A + Complex.I • B).mulVec x = 0 at hxG
  exact (complex_pencil_kernel A B hAB x).mp hxG |>.2

theorem full_rank_of_maximal_kernel_common {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (hcommon : ∀ u : Fin p → ℝ,
      (∀ v : Fin p → ℝ, (realCombination C v).rank ≤ (realCombination C u).rank) →
      ∀ x, (realCombination C u).mulVec x = 0 → ∀ i, (C i).mulVec x = 0) :
    ∃ u : Fin p → ℝ, Function.Injective (realCombination C u).mulVec := by
  obtain ⟨u, hmax⟩ := maximal_real_combination C
  refine ⟨u, ?_⟩
  intro x y hxy
  have hzero : (realCombination C u).mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (positive_marginal_no_common_kernel C hpos (x - y)
    (hcommon u hmax (x - y) hzero))

theorem full_rank_of_complex_pencil_bound {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i)
    (hpencil : ∀ u : Fin p → ℝ,
      (∀ v : Fin p → ℝ, (realCombination C v).rank ≤ (realCombination C u).rank) →
      ∀ i, (realCombination C u + Complex.I • C i).rank ≤ (realCombination C u).rank) :
    ∃ u : Fin p → ℝ, Function.Injective (realCombination C u).mulVec := by
  apply full_rank_of_maximal_kernel_common C hpos
  intro u hmax x hx i
  have hcross_i :
      (realCombination C u).conjTranspose * C i =
      (C i).conjTranspose * realCombination C u := by
    simpa only [realCombination_single] using
      (real_combinations_cross C hcross u (Pi.single i 1))
  exact kernel_inclusion_of_complex_pencil_rank (realCombination C u) (C i)
    hcross_i (hpencil u hmax i) x hx

theorem full_rank_of_real_to_complex_pencil_principle {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i)
    (hpencil : ∀ A B : Matrix (Fin r) (Fin m) ℂ,
      (∀ t : ℝ, (A + (t : ℂ) • B).rank ≤ A.rank) →
      (A + Complex.I • B).rank ≤ A.rank) :
    ∃ u : Fin p → ℝ, Function.Injective (realCombination C u).mulVec := by
  apply full_rank_of_complex_pencil_bound C hpos hcross
  intro u hmax i
  apply hpencil
  exact maximal_real_combination_pencil C u hmax i

theorem full_rank_of_rank_from_minors {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i)
    (hminors : ∀ (M : Matrix (Fin r) (Fin m) ℂ) (k : ℕ),
      (∀ (rows : Fin (k + 1) → Fin r) (cols : Fin (k + 1) → Fin m),
        (M.submatrix rows cols).det = 0) → M.rank ≤ k) :
    ∃ u : Fin p → ℝ, Function.Injective (realCombination C u).mulVec := by
  apply full_rank_of_complex_pencil_bound C hpos hcross
  intro u hmax i
  apply hminors
  intro rows cols
  exact maximal_real_pencil_large_minors_zero C u hmax i (Nat.lt_succ_self _)
    rows cols Complex.I

theorem full_rank_real_combination {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i) :
    ∃ u : Fin p → ℝ, Function.Injective (realCombination C u).mulVec :=
  full_rank_of_rank_from_minors C hpos hcross rank_le_of_minors_zero

theorem full_rank_real_combination_rank {p r m : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin m) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i) :
    ∃ u : Fin p → ℝ, (realCombination C u).rank = m := by
  obtain ⟨u, hu⟩ := full_rank_real_combination C hpos hcross
  refine ⟨u, ?_⟩
  rw [Matrix.rank_eq_finrank_range_toLin (realCombination C u)
    (Pi.basisFun ℂ (Fin r)) (Pi.basisFun ℂ (Fin m)), Matrix.toLin_eq_toLin']
  rw [LinearMap.finrank_range_of_inj (show Function.Injective
    (Matrix.toLin' (realCombination C u)) from hu),
    Module.finrank_pi, Fintype.card_fin]

theorem full_rank_two_columns {p r : ℕ}
    (C : Fin p → Matrix (Fin r) (Fin 2) ℂ)
    (hpos : (∑ i, (C i).conjTranspose * C i).PosDef)
    (hcross : ∀ i j, (C i).conjTranspose * C j = (C j).conjTranspose * C i) :
    ∃ u : Fin p → ℝ, Function.Injective (realCombination C u).mulVec :=
  full_rank_real_combination C hpos hcross

end PPTQubit
#print axioms PPTQubit.rank_le_one_of_cols_in_line
#print axioms PPTQubit.rank_le_zero_of_one_minors_zero
#print axioms PPTQubit.rank_le_one_of_two_minors_zero
#print axioms PPTQubit.rank_le_one_iff_two_minors_zero
#print axioms PPTQubit.full_rank_two_columns
#print axioms PPTQubit.realCombination_single
#print axioms PPTQubit.realCombination_add
#print axioms PPTQubit.realCombination_smul
#print axioms PPTQubit.maximal_real_combination
#print axioms PPTQubit.maximal_real_combination_pencil
#print axioms PPTQubit.complex_polynomial_vanishing_on_reals
#print axioms PPTQubit.determinant_pencil_vanishing_on_reals
#print axioms PPTQubit.minor_pencil_vanishing_on_reals
#print axioms PPTQubit.submatrix_rank_le
#print axioms PPTQubit.large_minor_det_zero
#print axioms PPTQubit.maximal_real_pencil_large_minors_zero
#print axioms PPTQubit.real_combinations_cross
#print axioms PPTQubit.positive_marginal_no_common_kernel
#print axioms PPTQubit.full_rank_one_column
#print axioms PPTQubit.complex_pencil_gram
#print axioms PPTQubit.complex_pencil_kernel
#print axioms PPTQubit.kernel_inclusion_of_complex_pencil_rank
#print axioms PPTQubit.full_rank_of_maximal_kernel_common
#print axioms PPTQubit.full_rank_of_complex_pencil_bound
#print axioms PPTQubit.full_rank_of_real_to_complex_pencil_principle
#print axioms PPTQubit.full_rank_of_rank_from_minors
#print axioms PPTQubit.full_rank_real_combination
#print axioms PPTQubit.full_rank_real_combination_rank
