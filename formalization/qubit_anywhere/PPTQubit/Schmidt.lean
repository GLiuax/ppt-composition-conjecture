import PPTQubit.Swapping
/-! Finite Schmidt-rank decompositions and 2-EB action on Schmidt-number-two inputs. -/
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace PPTQubit

def SchmidtRankAtMost {a b : ℕ} (k : ℕ) (z : Fin a × Fin b → ℂ) : Prop :=
  ∃ (v : Fin k → Fin a → ℂ) (w : Fin k → Fin b → ℂ),
    ∀ i j, z (i,j) = ∑ t, v t i * w t j

def SchmidtNumberAtMost {a b : ℕ} (k : ℕ)
    (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : Prop :=
  ∃ (r : ℕ) (z : Fin r → Fin a × Fin b → ℂ),
    Q = ∑ t, pureProjector (z t) ∧ ∀ t, SchmidtRankAtMost k (z t)

theorem schmidt_rank_succ {a b k : ℕ} (z : Fin a × Fin b → ℂ)
    (hz : SchmidtRankAtMost k z) : SchmidtRankAtMost (k+1) z := by
  obtain ⟨v,w,hv⟩ := hz
  refine ⟨Fin.lastCases 0 v,Fin.lastCases 0 w,?_⟩
  intro i j
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc,Fin.lastCases_last,Pi.zero_apply,mul_zero,add_zero]
  exact hv i j

theorem schmidt_rank_mono {a b k l : ℕ} (z : Fin a × Fin b → ℂ)
    (hz : SchmidtRankAtMost k z) (hkl : k ≤ l) : SchmidtRankAtMost l z := by
  induction l, hkl using Nat.le_induction with
  | base => exact hz
  | succ l hl ih => exact schmidt_rank_succ z ih

theorem schmidt_number_mono {a b k l : ℕ}
    (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hQ : SchmidtNumberAtMost k Q) (hkl : k ≤ l) : SchmidtNumberAtMost l Q := by
  obtain ⟨r,z,hQ,hz⟩ := hQ
  exact ⟨r,z,hQ,fun t => schmidt_rank_mono (z t) (hz t) hkl⟩

theorem schmidt_number_positive {a b k : ℕ}
    (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hQ : SchmidtNumberAtMost k Q) : Q.PosSemidef := by
  obtain ⟨r,z,hQ,hz⟩ := hQ
  rw [hQ]
  apply Finset.sum_induction
  · intro A B hA hB; exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro i _; exact pureProjector_positive (z i)

theorem schmidt_one_iff_separable {a b : ℕ}
    (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    SchmidtNumberAtMost 1 Q ↔ IsSeparable Q := by
  constructor
  · rintro ⟨r,z,hQ,hz⟩
    choose v w hv using hz
    refine ⟨r,fun t => v t 0,fun t => w t 0,?_⟩
    intro i a j b
    rw [hQ]
    simp only [Matrix.sum_apply,pureProjector,hv,Fin.sum_univ_one]
  · rintro ⟨r,v,w,hQ⟩
    refine ⟨r,fun t x => v t x.1 * w t x.2,?_,?_⟩
    · ext ⟨i,a⟩ ⟨j,b⟩
      simpa only [Matrix.sum_apply,pureProjector] using hQ i a j b
    · intro t
      refine ⟨fun _ => v t,fun _ => w t,?_⟩
      intro i j
      simp only [Fin.sum_univ_one]

theorem schmidt_rank_le_reference {a b : ℕ} (z : Fin a × Fin b → ℂ) :
    SchmidtRankAtMost a z := by
  refine ⟨fun t i => if i=t then 1 else 0,fun t j => z (t,j),?_⟩
  intro i j
  simp

theorem schmidt_rank_le_system {a b : ℕ} (z : Fin a × Fin b → ℂ) :
    SchmidtRankAtMost b z := by
  refine ⟨fun t i => z (i,t),fun t j => if j=t then 1 else 0,?_⟩
  intro i j
  simp

theorem positive_schmidt_bound_reference {a b : ℕ}
    (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hQ : Q.PosSemidef) :
    SchmidtNumberAtMost a Q := by
  obtain ⟨r,z,hz⟩ := positive_pure_expansion Q hQ
  exact ⟨r,z,hz,fun t => schmidt_rank_le_reference (z t)⟩

theorem positive_schmidt_bound_system {a b : ℕ}
    (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hQ : Q.PosSemidef) :
    SchmidtNumberAtMost b Q := by
  obtain ⟨r,z,hz⟩ := positive_pure_expansion Q hQ
  exact ⟨r,z,hz,fun t => schmidt_rank_le_system (z t)⟩

theorem schmidt_rank_matrix_bound {a b k : ℕ} (z : Fin a × Fin b → ℂ)
    (hz : SchmidtRankAtMost k z) :
    Matrix.rank (show Matrix (Fin a) (Fin b) ℂ from fun i j => z (i,j)) ≤ k := by
  obtain ⟨v,w,hv⟩ := hz
  let A : Matrix (Fin a) (Fin k) ℂ := fun i t => v t i
  let B : Matrix (Fin k) (Fin b) ℂ := fun t j => w t j
  have heq : (show Matrix (Fin a) (Fin b) ℂ from fun i j => z (i,j)) = A * B := by
    ext i j
    exact hv i j
  rw [heq]
  exact le_trans (Matrix.rank_mul_le_left A B) (by simpa using Matrix.rank_le_card_width A)

theorem schmidt_number_finite_sum {ι : Type*} [Fintype ι] {a b k : ℕ}
    (Q : ι → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hQ : ∀ i, SchmidtNumberAtMost k (Q i)) : SchmidtNumberAtMost k (∑ i, Q i) := by
  classical
  choose r z he hz using hQ
  let κ := (i : ι) × Fin (r i)
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ,fun s => z (e s).1 (e s).2,?_,fun s => hz (e s).1 (e s).2⟩
  ext x y
  simp only [Matrix.sum_apply,he,pureProjector]
  calc
    _ = ∑ t : κ, z t.1 t.2 x * star (z t.1 t.2 y) := (Fintype.sum_sigma _).symm
    _ = _ := (e.sum_comp _).symm

theorem schmidt_rank_local_first {a b k n : ℕ} (U : Matrix (Fin n) (Fin a) ℂ)
    (z : Fin a × Fin b → ℂ) (hz : SchmidtRankAtMost k z) :
    SchmidtRankAtMost k (fun x => ∑ i, U x.1 i * z (i,x.2)) := by
  obtain ⟨v,w,hv⟩ := hz
  refine ⟨fun t i => ∑ j, U i j * v t j,w,?_⟩
  intro i j
  simp only [hv,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro s _
  ring

theorem schmidt_number_local_first {a b k n : ℕ} (U : Matrix (Fin n) (Fin a) ℂ)
    (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hQ : SchmidtNumberAtMost k Q) :
    SchmidtNumberAtMost k (localCongruence U Q) := by
  obtain ⟨r,z,hQ,hz⟩ := hQ
  rw [hQ,localCongruence_sum]
  apply schmidt_number_finite_sum
  intro t
  rw [localCongruence_pure]
  refine ⟨1,fun _ x => ∑ i, U x.1 i * z t (i,x.2),?_,?_⟩
  · simp only [Fin.sum_univ_one]
  · intro s
    exact schmidt_rank_local_first U (z t) (hz t)

/-- Complete positivity is stated in its operational form on every reference. -/
def IsCompletelyPositiveMap {p q : ℕ} (T : MatrixMap p q) : Prop :=
  ∀ (n : ℕ) (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ),
    Q.PosSemidef → (applySecond T Q).PosSemidef

theorem ppt_map_completely_positive {p q : ℕ} (T : MatrixMap p q) (hT : IsPPTMap T) :
    IsCompletelyPositiveMap T := by
  intro n Q hQ
  exact (ppt_map_applySecond T hT Q hQ).1

theorem completely_positive_preserves_schmidt_number {p q n k : ℕ}
    (T : MatrixMap p q) (hT : IsCompletelyPositiveMap T)
    (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ)
    (hQ : SchmidtNumberAtMost k Q) : SchmidtNumberAtMost k (applySecond T Q) := by
  obtain ⟨r,z,hQ,hz⟩ := hQ
  rw [hQ,map_sum]
  apply schmidt_number_finite_sum
  intro t
  obtain ⟨v,w,hv⟩ := hz t
  let U : Matrix (Fin n) (Fin k) ℂ := fun a i => v i a
  let z' : Fin k × Fin p → ℂ := fun x => w x.1 x.2
  have he : z t = fun x => ∑ i, U x.1 i * z' (i,x.2) := by
    funext ⟨i,a⟩
    exact hv i a
  rw [he,← localCongruence_pure,applySecond_localCongruence]
  apply schmidt_number_local_first
  exact positive_schmidt_bound_reference _ (hT k _ (pureProjector_positive z'))

theorem two_eb_pure_schmidt_two {p q n : ℕ} (T : MatrixMap p q)
    (hT : IsTwoEntanglementBreaking T) (z : Fin n × Fin p → ℂ)
    (hz : SchmidtRankAtMost 2 z) : IsSeparable (applySecond T (pureProjector z)) := by
  obtain ⟨v,w,hz⟩ := hz
  let U : Matrix (Fin n) (Fin 2) ℂ := fun a i => v i a
  let z' : Fin 2 × Fin p → ℂ := fun x => w x.1 x.2
  have hz' : z = fun x => ∑ i, U x.1 i * z' (i,x.2) := by
    funext ⟨i,a⟩
    exact hz i a
  rw [hz',← localCongruence_pure,applySecond_localCongruence]
  exact localCongruence_separable U _ (hT (pureProjector z') (pureProjector_positive z'))

theorem two_eb_schmidt_two {p q n : ℕ} (T : MatrixMap p q)
    (hT : IsTwoEntanglementBreaking T)
    (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ)
    (hQ : SchmidtNumberAtMost 2 Q) : IsSeparable (applySecond T Q) := by
  obtain ⟨r,z,hQ,hz⟩ := hQ
  rw [hQ,map_sum]
  exact separable_finite_sum _ (fun t => two_eb_pure_schmidt_two T hT (z t) (hz t))

theorem ppt_pair_schmidt_two {p q r n : ℕ} (S : MatrixMap p q) (T : MatrixMap q r)
    (hS : IsPPTMap S) (hT : IsPPTMap T)
    (Q : Matrix (Fin n × Fin p) (Fin n × Fin p) ℂ)
    (hQ : SchmidtNumberAtMost 2 Q) : IsSeparable (applySecond (T.comp S) Q) :=
  two_eb_schmidt_two (T.comp S) (ppt_composition_two_entanglement_breaking S T hS hT) Q hQ
end PPTQubit
#print axioms PPTQubit.ppt_pair_schmidt_two

#print axioms PPTQubit.completely_positive_preserves_schmidt_number
