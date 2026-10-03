import Chapter2ItoStoppedInterval
import Chapter3IdentityItoIntegral
import Chapter12GaussianMartingaleTerminal

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The actual Ito integral of a deterministic interval indicator equals
the corresponding Brownian increment, simultaneously at all finite times. -/
theorem indicator_ito_finite_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (N : HalfClosedTime → Ω → ℝ) (hN : ContinuousM2Witness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W i)
      (fun z => (Ioc a b).indicator (fun _ => (1:ℝ)) z.2) N) :
    ∀ᵐ w ∂P, ∀ t, t < ⊤ →
      N t w = B.W i (min (realTimeClamp b) t) w-B.W i (min (realTimeClamp a) t) w := by
  obtain ⟨u,hu,hum,hut⟩ := exists_seq_strictMono_tendsto'
    (show (⊥ : HalfClosedTime)<⊤ from (show (0:EReal)<⊤ by simp))
  have huc (t : HalfClosedTime) (ht : t < ⊤) : ∃ n, t < u n :=
    (hut.eventually (lt_mem_nhds ht)).exists
  have hNl := continuous_m2_is_local P B.F B.mono B.le u hu.monotone
    (fun n => (hum n).2) huc N hN
  exact ito_stochastic_interval_identity P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null
    (B.W i) (B.W i) N (fun _ => 1) (B.martingale i) (B.martingale i) hNl
    (fun _ => measurable_const) (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => ha.trans hab)
    (fun _ => hab) (fun t => by by_cases h : realTimeClamp (T := ⊤) a ≤ t <;> simp [h])
    (fun t => by by_cases h : realTimeClamp (T := ⊤) b ≤ t <;> simp [h])
    (identity_ito_integral P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null (B.W i) (B.martingale i)) hNI

/-- Continuity at the terminal point identifies the L2 limit with the
increment at the fixed finite endpoints. -/
theorem indicator_ito_terminal_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (N : HalfClosedTime → Ω → ℝ) (hN : ContinuousM2Witness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W i)
      (fun z => (Ioc a b).indicator (fun _ => (1:ℝ)) z.2) N) :
    N ⊤ =ᵐ[P] fun w => B.W i (realTimeClamp b) w-B.W i (realTimeClamp a) w := by
  obtain ⟨u,hu,hum,hut⟩ := exists_seq_strictMono_tendsto'
    (show (⊥ : HalfClosedTime)<⊤ from (show (0:EReal)<⊤ by simp))
  have hbt : realTimeClamp (T := ⊤) b < ⊤ := by
    change (realTimeClamp (T := ⊤) b).val < (⊤:EReal)
    rw [real_time_clamp_eq b (ha.trans hab) le_top]
    exact EReal.coe_lt_top _
  have hev := hut.eventually (lt_mem_nhds hbt)
  filter_upwards [indicator_ito_finite_identity P B i a b ha hab N hN hNI] with w hw
  have hn : Tendsto (fun n => N (u n) w) atTop (𝓝 (N ⊤ w)) := (hN.path w).continuousAt.tendsto.comp hut
  have he : (fun n => N (u n) w) =ᶠ[atTop]
      fun _ => B.W i (realTimeClamp b) w-B.W i (realTimeClamp a) w := by
    filter_upwards [hev] with n hn
    rw [hw (u n) (hum n).2,min_eq_left hn.le,
      min_eq_left ((real_time_clamp_mono hab).trans hn.le)]
  exact tendsto_nhds_unique hn (tendsto_const_nhds.congr' he.symm)

end Asakura.Chapter12
