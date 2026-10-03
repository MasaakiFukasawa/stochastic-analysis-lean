import Chapter7FiniteDriftExtension
import Chapter7OriginalEstimatorDrift
import Chapter7BlockAdaptedness

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma finite_drift_integral_measurable {Ω : Type*} [MeasurableSpace Ω]
    (b : ℝ → Ω → ℝ) (T : ℝ) (hT : 0≤T)
    (hbc : ∀ w,ContinuousOn (fun r => b r w) (Icc 0 T))
    (hbm : ∀ r∈Icc 0 T,Measurable (b r)) (t : ℝ) (ht : t∈Icc 0 T) :
    Measurable (fun w => ∫ r in 0..t,b r w) := by
  have hc := (finite_drift_extension b T hT hbc).1
  have hm r : Measurable (finiteDriftExtension b T r) :=
    hbm _ ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩
  have hj := measurable_uncurry_of_continuous_of_measurable hc hm
  have hi := (hj.comp measurable_swap).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0:ℝ) t))
  have he w : (∫ r in Ioc 0 t,finiteDriftExtension b T r w)=∫ r in 0..t,b r w := by
    rw [← intervalIntegral.integral_of_le ht.1]
    exact finite_drift_integral b T t ht.1 ht.2 w
  simpa only [Function.comp_def,Function.uncurry_def,Prod.swap,he] using hi.measurable

lemma drifted_projection_measurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (b : ℝ → Ω → ℝ) (x : Ω → ℝ) (T : ℝ) (hT : 0≤T)
    (hbc : ∀ w,ContinuousOn (fun r => b r w) (Icc 0 T))
    (hbm : ∀ r∈Icc 0 T,Measurable (b r)) (hx : Measurable x)
    (t : ℝ) (ht : t∈Icc 0 T) : Measurable (driftedProjectionProcess B u b x t) := by
  apply (hx.add (finite_drift_integral_measurable b T hT hbc hbm t ht)).add
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul (((B.martingale j).adapted P B.F _
    (changed_time_finite _ ht.1)).mono (B.le _) le_rfl)

lemma grid_right_in_interval (T : ℝ) (hT : 0<T) (n : ℕ) (k : Fin (n+1)) :
    ((k:ℝ)+1)*(T/((n:ℝ)+1))∈Icc (0:ℝ) T := by
  have hd : 0<(n:ℝ)+1 := by positivity
  constructor
  · positivity
  · have hk : (k:ℝ)+1≤(n:ℝ)+1 := by exact_mod_cast Nat.succ_le_of_lt k.isLt
    calc
      _ ≤ ((n:ℝ)+1)*(T/((n:ℝ)+1)) := mul_le_mul_of_nonneg_right hk (by positivity)
      _ = T := by field_simp

lemma realized_process_entry_measurable {Ω : Type*} [MeasurableSpace Ω]
    (X Y : ℝ → Ω → ℝ) (T : ℝ) (hT : 0<T)
    (hX : ∀ t∈Icc 0 T,Measurable (X t)) (hY : ∀ t∈Icc 0 T,Measurable (Y t)) (n : ℕ) :
    Measurable (realizedProcessEntry X Y T (n+1)) := by
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro k _
  have hs := grid_left_in_interval T hT.le n k
  have he := grid_right_in_interval T hT n k
  simp only [Nat.cast_add,Nat.cast_one]
  exact ((hX _ he).sub (hX _ hs)).mul ((hY _ he).sub (hY _ hs))

end Asakura.Chapter7
