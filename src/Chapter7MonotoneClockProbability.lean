import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter7
set_option maxHeartbeats 1000000

/-- The finite-grid squeezing argument: monotonicity is in time, not in the
sequence index. In particular no almost-sure subsequence is required. -/
theorem monotone_clock_uniform_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → ℝ → Ω → ℝ)
    (hm : ∀ n w,MonotoneOn (fun t => A n t w) (Ici 0))
    (hp : ∀ t,0 ≤ t → TendstoInMeasure P (fun n => A n t) atTop (fun _ => t))
    (K : ℝ) (hK : 0 ≤ K) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {w | ∃ t ∈ Icc 0 K,ε ≤ |A n t w-t|}) atTop (𝓝 0) := by
  classical
  let δ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (K/δ)
  let E := fun (n : ℕ) (k : Fin (N+1)) => {w | ε/2 ≤ |A n ((k:ℕ)*δ) w-(k:ℕ)*δ|}
  have hb (n) : {w | ∃ t ∈ Icc 0 K,ε ≤ |A n t w-t|} ⊆ ⋃ k : Fin (N+1),E n k := by
    intro w hw
    obtain ⟨t,ht,he⟩ := hw
    by_contra hn
    have hn' : ∀ k : Fin (N+1),|A n ((k:ℕ)*δ) w-(k:ℕ)*δ| < ε/2 := by
      intro k
      have hk : w ∉ E n k := fun hk => hn (mem_iUnion.mpr ⟨k,hk⟩)
      exact lt_of_not_ge hk
    let k := Nat.floor (t/δ)
    have hf : (k:ℝ) ≤ t/δ := Nat.floor_le (div_nonneg ht.1 hδ.le)
    have hfu : t/δ < (k:ℝ)+1 := Nat.lt_floor_add_one (t/δ)
    have hkN : k < N := by
      have : (k:ℝ) < N := hf.trans_lt ((div_le_div_of_nonneg_right ht.2 hδ.le).trans_lt hN)
      exact_mod_cast this
    have hlow : (k:ℝ)*δ ≤ t := (le_div_iff₀ hδ).mp hf
    have hupp : t ≤ ((k:ℝ)+1)*δ := ((div_lt_iff₀ hδ).mp hfu).le
    have hmlo := hm n w (show (k:ℝ)*δ ∈ Ici 0 by simp only [mem_Ici]; positivity) ht.1 hlow
    have hmhi := hm n w ht.1 (show ((k:ℝ)+1)*δ ∈ Ici 0 by simp only [mem_Ici]; positivity) hupp
    have h1 := abs_lt.mp (hn' ⟨k,by omega⟩)
    have h2 := abs_lt.mp (hn' ⟨k+1,by omega⟩)
    simp only [Nat.cast_add,Nat.cast_one] at h2
    have hab : |A n t w-t| < ε := by
      apply abs_lt.mpr
      dsimp [δ] at hlow hupp hmlo hmhi h1 h2
      constructor <;> linarith
    exact (not_lt_of_ge he) hab
  have hsum : Tendsto (fun n => ∑ k : Fin (N+1),P (E n k)) atTop (𝓝 0) := by
    have hh (k : Fin (N+1)) := (tendstoInMeasure_iff_dist.mp
      (hp ((k:ℕ)*δ) (by positivity))) (ε/2) (half_pos hε)
    have ht := tendsto_finsetSum Finset.univ (fun k _ => hh k)
    simpa only [Real.dist_eq,Finset.sum_const_zero] using ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le)
  intro n
  exact (measure_mono (hb n)).trans (measure_iUnion_fintype_le P (E n))

end Asakura.Chapter7
