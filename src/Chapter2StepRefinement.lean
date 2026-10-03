import Chapter2ElementaryFiniteSum
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Intervals

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A finite endpoint set has an increasing enumeration, extended constantly
beyond its last point. This supplies a common grid, rather than assuming one. -/
theorem finite_endpoint_grid {α : Type*} [LinearOrder α] (s : Finset α) (hs : s.Nonempty) :
    ∃ (N : ℕ) (u : ℕ → α), StrictMonoOn u (Iic N) ∧
      ∀ x ∈ s, ∃ k ≤ N, u k = x := by
  classical
  let N := s.card-1
  have hpos : 0 < s.card := Finset.card_pos.2 hs
  have hcard : s.card = N+1 := by dsimp [N]; omega
  let e := s.orderEmbOfFin hcard
  let u := fun k => e ⟨min k N,by omega⟩
  refine ⟨N,u,?_,?_⟩
  · intro i hi j hj hij
    change i ≤ N at hi
    change j ≤ N at hj
    apply e.strictMono
    change min i N < min j N
    simpa only [min_eq_left hi,min_eq_left hj] using hij
  · intro x hx
    have hx' : x ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨k,hk⟩ := hx'
    refine ⟨k.val,by omega,?_⟩
    simpa only [u,min_eq_left (show k.val ≤ N by omega)] using hk

/-- Telescoping on the cells selected by two endpoint indices. -/
theorem grid_selected_increment_sum (f : ℕ → ℝ) (N k l : ℕ) (hkl : k ≤ l) (hl : l ≤ N) :
    (∑ j ∈ Finset.range N, if k ≤ j ∧ j < l then f (j+1)-f j else 0) = f l-f k := by
  classical
  have he : (Finset.range N).filter (fun j => k ≤ j ∧ j < l) = Finset.Ico k l := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  rw [← Finset.sum_filter,he,Finset.sum_Ico_eq_sub _ hkl,
    Finset.sum_range_sub,Finset.sum_range_sub]
  ring

/-- Refining one holding interval onto a finite time grid leaves its gain
unchanged, for every price path; no probabilistic hypothesis is used. -/
theorem elementary_increment_refinement {α : Type*} [LinearOrder α]
    (N : ℕ) (u : ℕ → α) (hu : StrictMonoOn u (Iic N))
    (k l : ℕ) (hk : k ≤ N) (hl : l ≤ N) (hkl : k ≤ l)
    (X : α → ℝ) (t : α) (g : ℝ) :
    g * (X (min (u l) t)-X (min (u k) t)) =
      ∑ j ∈ Finset.range N,
        (Ico (u k) (u l)).indicator (fun _ => g) (u j) *
          (X (min (u (j+1)) t)-X (min (u j) t)) := by
  have h := grid_selected_increment_sum (fun j => X (min (u j) t)) N k l hkl hl
  rw [← h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ N := (Finset.mem_range.1 hj).le
  have he : u j ∈ Ico (u k) (u l) ↔ k ≤ j ∧ j < l :=
    and_congr (hu.le_iff_le hk hj') (hu.lt_iff_lt hj' hl)
  by_cases hp : k ≤ j ∧ j < l
  · rw [if_pos hp,indicator_of_mem (he.2 hp)]
  · rw [if_neg hp,indicator_of_notMem (fun hn => hp (he.1 hn)),mul_zero,zero_mul]

/-- Any finite elementary representation can be evaluated on one common
endpoint grid. This is the pathwise algebra used for representation independence. -/
theorem finite_step_common_grid {α ι : Type*} [LinearOrder α]
    (s : Finset ι) (a b : ι → α) (hab : ∀ i ∈ s, a i ≤ b i)
    (ha : α) :
    ∃ (N : ℕ) (u : ℕ → α), StrictMonoOn u (Iic N) ∧
      ∀ (G : ι → ℝ) (X : α → ℝ) (t : α),
        (∑ i ∈ s, G i * (X (min (b i) t)-X (min (a i) t))) =
          ∑ j ∈ Finset.range N,
            (∑ i ∈ s, (Ico (a i) (b i)).indicator (fun _ => G i) (u j)) *
              (X (min (u (j+1)) t)-X (min (u j) t)) := by
  classical
  let endpoints := insert ha (s.image a ∪ s.image b)
  obtain ⟨N,u,hu,hmem⟩ := finite_endpoint_grid endpoints (Finset.insert_nonempty _ _)
  refine ⟨N,u,hu,fun G X t => ?_⟩
  have he (i) (hi : i ∈ s) :
      G i * (X (min (b i) t)-X (min (a i) t)) =
      ∑ j ∈ Finset.range N, (Ico (a i) (b i)).indicator (fun _ => G i) (u j) *
        (X (min (u (j+1)) t)-X (min (u j) t)) := by
    obtain ⟨k,hk,hek⟩ := hmem (a i) (by simp only [endpoints,Finset.mem_insert,Finset.mem_union]; exact Or.inr (Or.inl (Finset.mem_image_of_mem a hi)))
    obtain ⟨l,hl,hel⟩ := hmem (b i) (by simp only [endpoints,Finset.mem_insert,Finset.mem_union]; exact Or.inr (Or.inr (Finset.mem_image_of_mem b hi)))
    have hkl : k ≤ l := (hu.le_iff_le hk hl).1 (by rw [hek,hel]; exact hab i hi)
    simpa only [hek,hel] using elementary_increment_refinement N u hu k l hk hl hkl X t (G i)
  rw [Finset.sum_congr rfl he,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact (Finset.sum_mul _ _ _).symm

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_endpoint_grid
#print axioms Asakura.Chapter2Complete.grid_selected_increment_sum
#print axioms Asakura.Chapter2Complete.elementary_increment_refinement
#print axioms Asakura.Chapter2Complete.finite_step_common_grid
