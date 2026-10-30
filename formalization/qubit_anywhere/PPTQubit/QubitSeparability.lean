import PPTQubit.GeneralDecomposition
/-! Real product-state decompositions of positive operators fixed by qubit partial transpose. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

theorem real_qubit_annihilator_product {m : ℕ}
    (psi : Fin 2 × Fin m → ℂ) (alpha : Fin 2 → ℝ)
    (hpsi : psi ≠ 0) (ha : alpha ≠ 0)
    (hrel : ∀ a, ∑ i, (alpha i : ℂ) * psi (i, a) = 0) :
    ∃ (v : Fin 2 → ℝ) (w : Fin m → ℂ),
      v ≠ 0 ∧ w ≠ 0 ∧ ∀ i a, psi (i, a) = (v i : ℂ) * w a := by
  have hf : ∃ (v : Fin 2 → ℝ) (w : Fin m → ℂ),
      v ≠ 0 ∧ ∀ i a, psi (i, a) = (v i : ℂ) * w a := by
    by_cases h0 : alpha 0 = 0
    · have h1 : alpha 1 ≠ 0 := by
        intro h1
        apply ha
        funext i
        fin_cases i <;> assumption
      have hzero (a : Fin m) : psi (1, a) = 0 := by
        have h := hrel a
        simp only [Fin.sum_univ_two, h0, Complex.ofReal_zero, zero_mul, zero_add] at h
        exact (mul_eq_zero.mp h).resolve_left (Complex.ofReal_ne_zero.mpr h1)
      refine ⟨![1, 0], fun a => psi (0, a), ?_, ?_⟩
      · intro h
        have hh := congrFun h (0 : Fin 2)
        norm_num at hh
      · intro i a
        fin_cases i <;> simp [hzero]
    · have hn : (alpha 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
      have hfirst (a : Fin m) : psi (0, a) = ((-alpha 1 / alpha 0 : ℝ) : ℂ) * psi (1, a) := by
        have h := hrel a
        simp only [Fin.sum_univ_two] at h
        rw [Complex.ofReal_div, Complex.ofReal_neg, div_mul_eq_mul_div]
        apply (eq_div_iff hn).mpr
        linear_combination h
      refine ⟨![-alpha 1 / alpha 0, 1], fun a => psi (1, a), ?_, ?_⟩
      · intro h
        have hh := congrFun h (1 : Fin 2)
        norm_num at hh
      · intro i a
        fin_cases i
        · exact hfirst a
        · simp
  obtain ⟨v, w, hv, hprod⟩ := hf
  refine ⟨v, w, hv, ?_, hprod⟩
  intro hw
  apply hpsi
  funext ⟨i, a⟩
  simp only [hprod, hw, Pi.zero_apply, mul_zero]

/-- Finite sums of positive product rank-one operators, without trace normalization. -/
def IsSeparable {p m : Type*} (Q : Matrix (p × m) (p × m) ℂ) : Prop :=
  ∃ (r : ℕ) (v : Fin r → p → ℂ) (w : Fin r → m → ℂ),
    ∀ i a j b, Q (i, a) (j, b) =
      ∑ s, (v s i * w s a) * star (v s j * w s b)

theorem qubit_pt_invariant_product_decomposition {m : ℕ}
    (Q : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ)
    (hQ : Q.PosSemidef) (hpt : partialTransposeFirst Q = Q) :
    ∃ (v : Fin Q.rank → Fin 2 → ℝ) (w : Fin Q.rank → Fin m → ℂ),
      (∀ s, v s ≠ 0 ∧ w s ≠ 0) ∧
      ∀ i a j b, Q (i, a) (j, b) =
        ∑ s, ((v s i : ℂ) * w s a) * star ((v s j : ℂ) * w s b) := by
  classical
  obtain ⟨psi, alpha, hsum, hrel⟩ := pt_invariant_real_hyperplane_decomposition (p := 0) Q hQ hpt
  have hf (s : Fin Q.rank) :=
    real_qubit_annihilator_product (psi s) (alpha s) (hrel s).1 (hrel s).2.1 (hrel s).2.2
  choose v w hv hw hprod using hf
  refine ⟨v, w, fun s => ⟨hv s, hw s⟩, ?_⟩
  intro i a j b
  rw [hsum]
  simp only [hprod]

theorem qubit_pt_invariant_separable {m : ℕ}
    (Q : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ)
    (hQ : Q.PosSemidef) (hpt : partialTransposeFirst Q = Q) : IsSeparable Q := by
  obtain ⟨v, w, _, hsum⟩ := qubit_pt_invariant_product_decomposition Q hQ hpt
  exact ⟨Q.rank, fun s i => (v s i : ℂ), w, hsum⟩

end PPTQubit
#print axioms PPTQubit.qubit_pt_invariant_product_decomposition
#print axioms PPTQubit.qubit_pt_invariant_separable
