import Chapter12ItoIndicatorIdentity

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- An M2 Ito integral with integrand supported in (0,T] has terminal
value equal to its value at T, so no information after T is used. -/
theorem supported_ito_terminal_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (T : ℝ) (hT : 0 ≤ T) (f : ℝ → ℝ) (hf : Measurable f)
    (N : HalfClosedTime → Ω → ℝ) (hN : ContinuousM2Witness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W i)
      (fun z => (Ioc 0 T).indicator f z.2) N) :
    N ⊤ =ᵐ[P] N (realTimeClamp T) := by
  obtain ⟨u,hu,hum,hut⟩ := exists_seq_strictMono_tendsto'
    (show (⊥ : HalfClosedTime)<⊤ from (show (0:EReal)<⊤ by simp))
  have huc (t : HalfClosedTime) (ht : t < ⊤) : ∃ n, t < u n :=
    (hut.eventually (lt_mem_nhds ht)).exists
  have hNl := continuous_m2_is_local P B.F B.mono B.le u hu.monotone
    (fun n => (hum n).2) huc N hN
  have hNI' : ItoCovarianceFormula P B.F (B.W i)
      (fun z => (Ioc (0:ℝ) T).indicator (fun r => (Ioc (0:ℝ) T).indicator f r) z.2) N := by
    simpa only [Set.indicator_indicator,Set.inter_self] using hNI
  have he := ito_stochastic_interval_identity P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null
    (B.W i) N N (fun z => (Ioc 0 T).indicator f z.2) (B.martingale i) hNl hNl
    (fun _ => hf.indicator measurableSet_Ioc) (fun _ => 0) (fun _ => T)
    (fun _ => le_rfl) (fun _ => hT) (fun _ => hT)
    (fun t => by by_cases h : realTimeClamp (T := ⊤) 0 ≤ t <;> simp [h])
    (fun t => by by_cases h : realTimeClamp (T := ⊤) T ≤ t <;> simp [h]) hNI hNI'
  have hbt : realTimeClamp (T := ⊤) T < ⊤ := by
    change (realTimeClamp (T := ⊤) T).val < (⊤:EReal)
    rw [real_time_clamp_eq T hT le_top]
    exact EReal.coe_lt_top _
  have hz : realTimeClamp (T := (⊤:EReal)) 0 = ⊥ :=
    Subtype.ext (real_time_clamp_eq 0 le_rfl le_top)
  have hev := hut.eventually (lt_mem_nhds hbt)
  filter_upwards [he,hN.initial] with w hw h0
  have hn : Tendsto (fun n => N (u n) w) atTop (𝓝 (N ⊤ w)) :=
    (hN.path w).continuousAt.tendsto.comp hut
  have he' : (fun n => N (u n) w) =ᶠ[atTop] fun _ => N (realTimeClamp T) w := by
    filter_upwards [hev] with n hn
    rw [hw (u n) (hum n).2,min_eq_left hn.le,hz,min_bot_left,h0]
    simp
  exact tendsto_nhds_unique hn (tendsto_const_nhds.congr' he'.symm)

end Asakura.Chapter12
