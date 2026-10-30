import PPTQubit.ChoiDecomposition
/-! Iterated Choi decomposition and trivial lifting on an arbitrary finite list. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def TrivialOnList {p q : ℕ} (T : MatrixMap p q) (L : List (Fin p)) : Prop :=
  ∀ s ∈ L, ∀ i, T (Matrix.single i s 1) = 0 ∧ T (Matrix.single s i 1) = 0

theorem completely_positive_choi {p q : ℕ} (T : MatrixMap p q)
    (hT : IsCompletelyPositiveMap T) : (choi T).PosSemidef := by
  have h := hT p (pureProjector (vectorize (1 : Matrix (Fin p) (Fin p) ℂ))) (pureProjector_positive _)
  rw [applySecond_pure_choi,Matrix.transpose_one,localCongruence_identity] at h
  exact h

theorem completely_positive_add {p q : ℕ} (T S : MatrixMap p q)
    (hT : IsCompletelyPositiveMap T) (hS : IsCompletelyPositiveMap S) :
    IsCompletelyPositiveMap (T+S) := by
  intro n Q hQ
  have he : applySecond (T+S) Q = applySecond T Q + applySecond S Q := by
    ext ⟨i,a⟩ ⟨j,b⟩
    rfl
  rw [he]
  exact (hT n Q hQ).add (hS n Q hQ)

theorem completely_positive_zero {p q : ℕ} : IsCompletelyPositiveMap (0 : MatrixMap p q) := by
  intro n Q hQ
  have he : applySecond (0 : MatrixMap p q) Q = 0 := by ext ⟨i,a⟩ ⟨j,b⟩; rfl
  rw [he]
  exact Matrix.PosSemidef.zero

theorem choi_sub {p q : ℕ} (T S : MatrixMap p q) :
    choi (T-S) = choi T - choi S := by ext ⟨i,a⟩ ⟨j,b⟩; rfl

/-- If the initial map is (k+1)-positive, up to k chosen rows and columns
can be removed while reducing positivity by one for each removed index. -/
theorem choi_decomposition_list {p q : ℕ} (L : List (Fin p)) :
    ∀ (k : ℕ) (T : MatrixMap p q), IsKPositiveMap (k+1) T → (choi T).IsHermitian →
      L.length ≤ k → ∃ F : MatrixMap p q,
        IsCompletelyPositiveMap F ∧ IsKPositiveMap (k+1-L.length) (T-F) ∧ TrivialOnList (T-F) L := by
  induction L with
  | nil =>
      intro k T hT hH hlen
      refine ⟨0,completely_positive_zero,?_,?_⟩
      · simpa using hT
      · simp [TrivialOnList]
  | cons s L ih =>
      intro k T hT hH hlen
      have hL : L.length ≤ k := by simp only [List.length_cons] at hlen; omega
      obtain ⟨F0,hF0,hR0,hzero0⟩ := ih k T hT hH hL
      let R0 := T-F0
      let j := k-L.length
      have hj : 1 ≤ j := by dsimp [j]; simp only [List.length_cons] at hlen; omega
      have he0 : k+1-L.length = j+1 := by dsimp [j]; omega
      have hR0' : IsKPositiveMap (j+1) R0 := by simpa only [R0,he0] using hR0
      have hHR0 : (choi R0).IsHermitian := by
        dsimp only [R0]
        rw [choi_sub]
        exact hH.sub (completely_positive_choi F0 hF0).isHermitian
      obtain ⟨F1,hF1,hR1,hnew,hkeep⟩ := choi_decomposition_step R0 hR0' hHR0 hj s
      let F := F0+F1
      have hF : IsCompletelyPositiveMap F := completely_positive_add F0 F1 hF0 hF1
      have hmap : T-F = R0-F1 := by
        dsimp only [F,R0]
        ext X i j
        simp only [LinearMap.sub_apply,LinearMap.add_apply,Matrix.sub_apply,Matrix.add_apply]
        ring
      refine ⟨F,hF,?_,?_⟩
      · have he : k+1-(s::L).length = j := by dsimp [j]; omega
        rw [he,hmap]
        exact hR1
      · rw [hmap]
        intro t ht i
        simp only [List.mem_cons] at ht
        rcases ht with hts | htL
        · subst t
          exact hnew i
        · have hz := hzero0 t htL
          have hf := hkeep t (fun j => (hz j).2) i
          constructor
          · change R0 (Matrix.single i t 1) - F1 (Matrix.single i t 1) = 0
            rw [hf.2,sub_zero]
            exact (hz i).1
          · change R0 (Matrix.single t i 1) - F1 (Matrix.single t i 1) = 0
            rw [hf.1,sub_zero]
            exact (hz i).2
end PPTQubit
#print axioms PPTQubit.choi_decomposition_list
