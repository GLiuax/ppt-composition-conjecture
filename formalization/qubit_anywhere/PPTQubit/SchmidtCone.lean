import PPTQubit.Schmidt
import Mathlib.Analysis.LocallyConvex.Separation
/-! Convex cone operations for bounded Schmidt number and strict cone separation. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem schmidt_rank_scale {a b k : ℕ} (z : Fin a × Fin b → ℂ)
    (c : ℂ) (hz : SchmidtRankAtMost k z) : SchmidtRankAtMost k (fun x => c*z x) := by
  obtain ⟨v,w,h⟩ := hz
  refine ⟨fun t i => c*v t i,w,?_⟩
  intro i j
  simp only [h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem schmidt_number_real_smul {a b k : ℕ}
    (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hQ : SchmidtNumberAtMost k Q) (c : ℝ) (hc : 0 ≤ c) :
    SchmidtNumberAtMost k (c • Q) := by
  obtain ⟨r,z,hQ,hz⟩ := hQ
  refine ⟨r,fun t x => (Real.sqrt c : ℂ)*z t x,?_,fun t => schmidt_rank_scale (z t) _ (hz t)⟩
  rw [hQ]
  ext x y
  simp only [Matrix.smul_apply,Matrix.sum_apply,pureProjector,
    StarMul.star_mul,Complex.star_def,Complex.conj_ofReal]
  change (c : ℂ) * (∑ t, z t x * star (z t y)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hs : (Real.sqrt c : ℂ) * (Real.sqrt c : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt hc]
  change (c : ℂ) * (z t x * star (z t y)) = _
  rw [← hs]
  simp only [Complex.star_def]
  ring

theorem schmidt_number_add {a b k : ℕ}
    (Q R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hQ : SchmidtNumberAtMost k Q) (hR : SchmidtNumberAtMost k R) :
    SchmidtNumberAtMost k (Q+R) := by
  have h : ∀ i : Fin 2, SchmidtNumberAtMost k (![Q,R] i) := by intro i; fin_cases i <;> assumption
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using schmidt_number_finite_sum ![Q,R] h

def SchmidtCone {a b : ℕ} (k : ℕ) : Set (Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :=
  {Q | SchmidtNumberAtMost k Q}

theorem schmidtCone_zero {a b k : ℕ} : (0 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ∈ SchmidtCone k := by
  refine ⟨0,fun s => Fin.elim0 s,?_,?_⟩
  · simp
  · intro s; exact Fin.elim0 s

theorem schmidtCone_convex {a b k : ℕ} : Convex ℝ (SchmidtCone (a := a) (b := b) k) := by
  intro Q hQ R hR c d hc hd hcd
  exact schmidt_number_add _ _ (schmidt_number_real_smul Q hQ c hc) (schmidt_number_real_smul R hR d hd)

theorem closed_cone_strict_separation {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    (C : Set E) (hconv : Convex ℝ C) (hclosed : IsClosed C) (hzero : (0:E) ∈ C)
    (hscale : ∀ (c : ℝ), 0 ≤ c → ∀ y ∈ C, c • y ∈ C)
    (x : E) (hx : x ∉ C) :
    ∃ f : E →L[ℝ] ℝ, f x < 0 ∧ ∀ y ∈ C, 0 ≤ f y := by
  obtain ⟨f,u,hx,hu⟩ := geometric_hahn_banach_point_closed hconv hclosed hx
  have hu0 : u < 0 := by simpa using hu 0 hzero
  refine ⟨f,lt_trans hx hu0,?_⟩
  intro y hy
  by_contra h
  have hyneg : f y < 0 := lt_of_not_ge h
  let t : ℝ := u / f y + 1
  have ht : 0 ≤ t := by
    dsimp [t]
    have hdiv : 0 ≤ (-u) / (-f y) := div_nonneg (by linarith) (by linarith)
    have hdiv' : 0 ≤ u / f y := by simpa using hdiv
    linarith
  have hh := hu (t • y) (hscale t ht y hy)
  rw [map_smul] at hh
  have hdiv : u / f y * f y = u := div_mul_cancel₀ u (ne_of_lt hyneg)
  dsimp [t] at hh
  nlinarith
end PPTQubit
#print axioms PPTQubit.schmidtCone_convex
#print axioms PPTQubit.closed_cone_strict_separation
