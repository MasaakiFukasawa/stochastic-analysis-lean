import Chapter7RepeatedEvents
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Infinitely many disjoint intervals of a fixed positive length force
infinite occupation measure. This is the pathwise last step of the Brownian
occupation argument. -/
theorem infinite_interval_occupation
    (a : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ j,a j+δ ≤ a (j+1))
    (J : Set ℕ) (hJ : J.Infinite) (E : Set ℝ)
    (hE : ∀ j ∈ J,Ioc (a j) (a j+δ) ⊆ E) : volume E = ∞ := by
  have ham : Monotone a := (strictMono_nat_of_lt_succ (fun j => by linarith [hgap j])).monotone
  let S := fun j : J => Ioc (a j.val) (a j.val+δ)
  have hd : Pairwise (fun j k => Disjoint (S j) (S k)) := by
    intro j k hjk
    have hv : j.val ≠ k.val := fun h => hjk (Subtype.ext h)
    rcases lt_or_gt_of_ne hv with h | h
    · apply Set.disjoint_left.mpr
      intro x hx hy
      have hh := (hgap j.val).trans (ham (Nat.succ_le_of_lt h))
      exact (not_lt_of_ge (hx.2.trans hh)) hy.1
    · apply Set.disjoint_left.mpr
      intro x hx hy
      have hh := (hgap k.val).trans (ham (Nat.succ_le_of_lt h))
      exact (not_lt_of_ge (hy.2.trans hh)) hx.1
  have hS : volume (⋃ j : J,S j) = ∞ := by
    rw [measure_iUnion hd (fun _ => measurableSet_Ioc)]
    have hv j : volume (S j) = ENNReal.ofReal δ := by simp [S,Real.volume_Ioc]
    simp_rw [hv]
    letI : Infinite J := Set.infinite_coe_iff.mpr hJ
    exact ENNReal.tsum_const_eq_top_of_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))
  apply top_le_iff.mp
  rw [← hS]
  apply measure_mono
  intro x hx
  obtain ⟨j,hj⟩ := mem_iUnion.mp hx
  exact hE j.val j.property hj

end Asakura.Chapter7
