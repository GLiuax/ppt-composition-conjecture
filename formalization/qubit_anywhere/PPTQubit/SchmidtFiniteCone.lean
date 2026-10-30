import PPTQubit.SchmidtCompact
import PPTQubit.FiniteConic
import Mathlib.Topology.Algebra.Module.FiniteDimension
set_option maxHeartbeats 800000
open Matrix
open scoped BigOperators
noncomputable section
namespace PPTQubit

def realTrace {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →L[ℝ] ℝ where
  toFun Q := Q.trace.re
  map_add' A B := by simp [Matrix.trace_add]
  map_smul' c A := by
    simp only [Matrix.trace_smul]
    exact Complex.smul_re c A.trace
  cont := by
    simp only [Matrix.trace, Matrix.diag]
    fun_prop

theorem unit_projector_realTrace_lower {a b : ℕ} {u : Fin a × Fin b → ℂ}
    (hu : u ∈ Metric.sphere 0 1) : 1 ≤ realTrace (pureProjector u) := by
  have hn : ‖u‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hu
  have he : ∃ i, 1 ≤ ‖u i‖ := by
    by_contra hh
    push Not at hh
    have hlt : ‖u‖ < 1 := (pi_norm_lt_iff (x := u) (r := (1 : ℝ)) (by norm_num)).mpr hh
    linarith
  obtain ⟨i,hi⟩ := he
  have hsq : 1 ≤ Complex.normSq (u i) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (u i)]
  have hsum : Complex.normSq (u i) ≤ ∑ j, Complex.normSq (u j) := by
    apply Finset.single_le_sum (s := Finset.univ) (f := fun j => Complex.normSq (u j))
    · intro j hj
      exact Complex.normSq_nonneg _
    · exact Finset.mem_univ i
  have htrace : realTrace (pureProjector u) = ∑ j, Complex.normSq (u j) := by
    change (∑ j : Fin a × Fin b, u j * star (u j)).re = _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change (u j * star (u j)).re = Complex.normSq (u j)
    simp [Complex.mul_conj]
  linarith



theorem schmidtCone_eq_finiteConicHull {a b k : ℕ} :
    SchmidtCone (a := a) (b := b) k =
      finiteConicHull (pureProjector '' SchmidtUnitVectors (a := a) (b := b) k) := by
  classical
  ext Q
  constructor
  · intro hQ
    obtain ⟨r,c,u,hc,hu,heq⟩ := schmidt_number_normalized_expansion Q hQ
    by_cases hne : (SchmidtUnitVectors (a := a) (b := b) k).Nonempty
    · obtain ⟨u0,hu0⟩ := hne
      let c' : Fin r → ℝ := fun i => if u i ∈ SchmidtUnitVectors k then c i else 0
      let u' : Fin r → Fin a × Fin b → ℂ := fun i => if u i ∈ SchmidtUnitVectors k then u i else u0
      refine ⟨r,c',fun i => pureProjector (u' i),?_,?_,?_⟩
      · intro i
        by_cases hi : u i ∈ SchmidtUnitVectors k <;> simp [c',hi,hc i]
      · intro i
        refine ⟨u' i,?_,rfl⟩
        by_cases hi : u i ∈ SchmidtUnitVectors k <;> simp [u',hi,hu0]
      · rw [heq]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hunit : u i ∈ SchmidtUnitVectors k
        · simp only [c',u',if_pos hunit]
          ext i j
          simp only [Matrix.smul_apply,Complex.real_smul]
          exact Complex.coe_smul _ _
        · have hz : u i = 0 ∧ c i = 0 := (hu i).resolve_left hunit
          simp only [c',u',if_neg hunit,hz.2]
          ext i j
          apply Complex.ext <;> simp [Matrix.smul_apply,Complex.mul_re,Complex.mul_im,Complex.smul_re,Complex.smul_im]
    · have hc0 : ∀ i, c i = 0 := by
        intro i
        have hnot : u i ∉ SchmidtUnitVectors k := by
          intro h
          exact hne ⟨u i,h⟩
        exact ((hu i).resolve_left hnot).2
      have hzero : Q = 0 := by
        rw [heq]
        apply Finset.sum_eq_zero
        intro i hi
        rw [hc0 i]
        ext i j
        apply Complex.ext <;> simp [Matrix.smul_apply,Complex.mul_re,Complex.mul_im,Complex.smul_re,Complex.smul_im]
      rw [hzero]
      refine ⟨0,Fin.elim0,Fin.elim0,by simp,by simp,by simp⟩
  · rintro ⟨r,c,z,hc,hz,hQ⟩
    rw [hQ]
    apply schmidt_number_finite_sum
    intro i
    obtain ⟨u,hu,he⟩ := hz i
    rw [← he]
    apply schmidt_number_real_smul _ _ (c i) (hc i)
    exact ⟨1,fun _ => u,by simp,fun _ => hu.2⟩

end PPTQubit
#print axioms PPTQubit.schmidtCone_eq_finiteConicHull
