import PPTQubit.Endpoints
/-! Elementary separability cone operations and positive tensor products. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem separable_add {a b : ℕ} (X Y : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hX : IsSeparable X) (hY : IsSeparable Y) : IsSeparable (X + Y) := by
  have h : ∀ i : Fin 2, IsSeparable (![X,Y] i) := by intro i; fin_cases i <;> assumption
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using separable_finite_sum ![X,Y] h

theorem separable_nonneg_smul {a b : ℕ} (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hX : IsSeparable X) (t : ℝ) (ht : 0 ≤ t) : IsSeparable ((t : ℂ) • X) := by
  obtain ⟨r,v,w,hsum⟩ := hX
  refine ⟨r,fun s i => (Real.sqrt t : ℂ) * v s i,w,?_⟩
  intro i a j b
  simp only [Matrix.smul_apply,smul_eq_mul,hsum,Finset.mul_sum,StarMul.star_mul,
    Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro s _
  have hs : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt ht]
  calc
    _ = ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) * (v s i * w s a * star (v s j * w s b)) := by rw [hs]; simp only [StarMul.star_mul,Complex.star_def]
    _ = _ := by simp only [StarMul.star_mul,Complex.star_def]; ring

theorem separable_tensor_positive {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ)
    (B : Matrix (Fin b) (Fin b) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    IsSeparable (Matrix.kronecker A B) := by
  obtain ⟨r,v,hv⟩ := positive_pure_expansion A hA
  obtain ⟨s,w,hw⟩ := positive_pure_expansion B hB
  let e : Fin (r*s) ≃ Fin r × Fin s := finProdFinEquiv.symm
  refine ⟨r*s,fun k => v (e k).1,fun k => w (e k).2,?_⟩
  intro i a j b
  change A i j * B a b = _
  simp only [hv,hw,Matrix.sum_apply,pureProjector,Finset.sum_mul,Finset.mul_sum]
  calc
    _ = ∑ k : Fin r × Fin s, (v k.1 i * w k.2 a) * star (v k.1 j * w k.2 b) := by
      rw [Fintype.sum_prod_type,Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      simp only [StarMul.star_mul]
      ring
    _ = _ := (e.sum_comp _).symm

theorem separable_positive {a b : ℕ} (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hX : IsSeparable X) : X.PosSemidef := by
  obtain ⟨r,v,w,hsum⟩ := hX
  have heq : X = ∑ s, pureProjector (fun i => v s i.1 * w s i.2) := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simpa only [Matrix.sum_apply,pureProjector] using hsum i a j b
  rw [heq]
  apply Finset.sum_induction
  · intro A B hA hB; exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro s _; exact pureProjector_positive _

theorem tensor_positive {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ)
    (B : Matrix (Fin b) (Fin b) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.kronecker A B).PosSemidef :=
  separable_positive _ (separable_tensor_positive A B hA hB)

end PPTQubit