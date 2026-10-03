import Chapter2StepRefinement
import Chapter2ClippedLp
import Mathlib.Order.Interval.Set.Union

open Set
open scoped Classical
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

/-- The indicator of a half-open interval is a difference of two
threshold functions in the endpoints. -/
theorem interval_indicator_jump {α : Type*} [LinearOrder α]
    (a b t : α) (hab : a ≤ b) (g : ℝ) :
    (Ico a b).indicator (fun _ => g) t =
      g*((if t < b then (1:ℝ) else 0)-(if t < a then 1 else 0)) := by
  by_cases ha : a ≤ t
  · by_cases hb : t < b
    · simp [indicator_of_mem (show t ∈ Ico a b from ⟨ha,hb⟩),hb,not_lt.2 ha]
    · simp [indicator_of_notMem (show t ∉ Ico a b from fun h => hb h.2),hb,not_lt.2 ha]
  · have hta : t < a := not_le.1 ha
    have htb : t < b := hta.trans_le hab
    simp [indicator_of_notMem (show t ∉ Ico a b from fun h => ha h.1),hta,htb]

/-- The same grid refinement holds as an identity of step functions,
including every endpoint. -/
theorem interval_step_refinement {α : Type*} [LinearOrder α]
    (N : ℕ) (u : ℕ → α) (hu : StrictMonoOn u (Iic N))
    (k l : ℕ) (hk : k ≤ N) (hl : l ≤ N) (hkl : k ≤ l)
    (g : ℝ) (t : α) :
    (Ico (u k) (u l)).indicator (fun _ => g) t =
      ∑ j ∈ Finset.range N,
        (Ico (u j) (u (j+1))).indicator
          (fun _ => (Ico (u k) (u l)).indicator (fun _ => g) (u j)) t := by
  let X := fun x => if t < x then (1:ℝ) else 0
  have he := elementary_increment_refinement N u hu k l hk hl hkl X (u N) g
  have hm (j) (hj : j ≤ N) : min (u j) (u N) = u j :=
    min_eq_left (hu.monotoneOn hj (show N ∈ Iic N by change N ≤ N; exact le_rfl) hj)
  rw [hm k hk,hm l hl] at he
  rw [interval_indicator_jump _ _ _ (hu.monotoneOn hk hl hkl)]
  change g*(X (u l)-X (u k)) = _
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < N := Finset.mem_range.1 hj
  have hj1 : j+1 ≤ N := by omega
  rw [hm j hjn.le,hm (j+1) hj1,interval_indicator_jump _ _ _
    (hu.monotoneOn hjn.le hj1 (by omega))]

/-- A scalar map fixing zero acts on a step function by acting on its
coefficients on disjoint grid cells. This includes the truncations used
in the Lp density proof. -/
theorem grid_step_map {α : Type*} [LinearOrder α]
    (N : ℕ) (u : ℕ → α) (hu : StrictMonoOn u (Iic N))
    (G : ℕ → ℝ) (f : ℝ → ℝ) (hf : f 0 = 0) (t : α) :
    f (∑ j ∈ Finset.range N, (Ico (u j) (u (j+1))).indicator (fun _ => G j) t) =
      ∑ j ∈ Finset.range N, (Ico (u j) (u (j+1))).indicator (fun _ => f (G j)) t := by
  by_cases h : ∃ j ∈ Finset.range N, t ∈ Ico (u j) (u (j+1))
  · obtain ⟨j,hj,htj⟩ := h
    have hunique (i) (hi : i ∈ Finset.range N) (hij : i ≠ j) :
        t ∉ Ico (u i) (u (i+1)) := by
      intro hti
      have hin : i < N := Finset.mem_range.1 hi
      have hjn : j < N := Finset.mem_range.1 hj
      rcases lt_or_gt_of_ne hij with hij | hji
      · have hle := hu.monotoneOn (show i+1 ∈ Iic N by change i+1 ≤ N; omega)
          (show j ∈ Iic N from hjn.le) (show i+1 ≤ j by omega)
        exact (not_lt_of_ge (hle.trans htj.1)) hti.2
      · have hle := hu.monotoneOn (show j+1 ∈ Iic N by change j+1 ≤ N; omega)
          (show i ∈ Iic N from hin.le) (show j+1 ≤ i by omega)
        exact (not_lt_of_ge (hle.trans hti.1)) htj.2
    rw [Finset.sum_eq_single j (fun i hi hij => indicator_of_notMem (hunique i hi hij) _)
      (fun hn => (hn hj).elim)]
    rw [Finset.sum_eq_single j (fun i hi hij => indicator_of_notMem (hunique i hi hij) _)
      (fun hn => (hn hj).elim)]
    rw [indicator_of_mem htj,indicator_of_mem htj]
  · have hn (j) (hj : j ∈ Finset.range N) : t ∉ Ico (u j) (u (j+1)) :=
      fun ht => h ⟨j,hj,ht⟩
    rw [Finset.sum_eq_zero (fun j hj => indicator_of_notMem (hn j hj) _),hf,
      Finset.sum_eq_zero (fun j hj => indicator_of_notMem (hn j hj) _)]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.interval_indicator_jump
#print axioms Asakura.Chapter2Complete.interval_step_refinement
#print axioms Asakura.Chapter2Complete.grid_step_map
