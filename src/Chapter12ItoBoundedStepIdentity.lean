import Chapter12ItoIndicatorIdentity
import Chapter2ElementaryLocalCovariance
import Chapter2SignedDensityIntegral

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The actual Ito integral of G 1_(a,b] is the weighted Brownian
increment; this follows from chapter-2 covariance uniqueness. -/
theorem bounded_step_ito_finite_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (G : Ω → ℝ) (hGm : Measurable[B.F (realTimeClamp a)] G) (hG : MemLp G ∞ P)
    (N : HalfClosedTime → Ω → ℝ) (hN : ContinuousM2Witness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W i)
      (fun z => (Ioc a b).indicator (fun _ => G z.1) z.2) N) :
    ∀ᵐ w ∂P, ∀ t, t < ⊤ →
      N t w = G w*(B.W i (min (realTimeClamp b) t) w-B.W i (min (realTimeClamp a) t) w) := by
  obtain ⟨u,hu,hum,hut⟩ := exists_seq_strictMono_tendsto'
    (show (⊥ : HalfClosedTime)<⊤ from (show (0:EReal)<⊤ by simp))
  have huc (t : HalfClosedTime) (ht : t < ⊤) : ∃ n, t < u n :=
    (hut.eventually (lt_mem_nhds ht)).exists
  have hNl := continuous_m2_is_local P B.F B.mono B.le u hu.monotone
    (fun n => (hum n).2) huc N hN
  let Z := fun t w => G w*(B.W i (min (realTimeClamp b) t) w-B.W i (min (realTimeClamp a) t) w)
  have hZ := elementary_integral_local_martingale P B.F B.mono B.le (B.W i) (B.martingale i)
    (realTimeClamp a) (realTimeClamp b) (real_time_clamp_mono hab) G hGm hG
  apply local_covariance_separates P B.F B.mono B.le N Z hNl hZ
  intro Y hY
  obtain ⟨C,hC⟩ := local_covariance_witness_exists P B.F B.mono B.le B.null (B.W i) Y (B.martingale i) hY
  obtain ⟨D,hD,hDI⟩ := hNI Y C hY hC
  obtain ⟨E,hE⟩ := local_covariance_witness_exists P B.F B.mono B.le B.null Z Y hZ hY
  have he := elementary_local_integral_covariance P B.F B.mono B.le B.null (B.W i) Y C
    (B.martingale i) hY hC (realTimeClamp a) (realTimeClamp b) (real_time_clamp_mono hab) G hGm hG E hE
  refine ⟨D,E,hD,hE,?_⟩
  apply local_covariance_common_time_equality P (by simp : (0:EReal)<⊤) B.F N Y D E hNl hY hD
    (hE.continuous_open_paths P B.F Z Y E hZ hY)
  intro t ht
  obtain ⟨r,hr,hrT,rfl⟩ := finite_closed_time_real t ht
  obtain ⟨ν,hν,_,_,hνD⟩ := hDI r hr hrT
  filter_upwards [hνD,he] with w hw hv
  rw [hw,hv _ ht]
  change signedIntegralRaw (ν w) ((Ioc a b).indicator (fun _ => G w)) = _
  rw [signed_integral_indicator_const _ _ measurableSet_Ioc,hν w a b ha hab]

theorem bounded_step_ito_terminal_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (G : Ω → ℝ) (hGm : Measurable[B.F (realTimeClamp a)] G) (hG : MemLp G ∞ P)
    (N : HalfClosedTime → Ω → ℝ) (hN : ContinuousM2Witness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W i)
      (fun z => (Ioc a b).indicator (fun _ => G z.1) z.2) N) :
    N ⊤ =ᵐ[P] fun w => G w*(B.W i (realTimeClamp b) w-B.W i (realTimeClamp a) w) := by
  obtain ⟨u,_,hum,hut⟩ := exists_seq_strictMono_tendsto'
    (show (⊥ : HalfClosedTime)<⊤ from (show (0:EReal)<⊤ by simp))
  have hbt : realTimeClamp (T := ⊤) b < ⊤ := by
    change (realTimeClamp (T := ⊤) b).val < (⊤:EReal)
    rw [real_time_clamp_eq b (ha.trans hab) le_top]
    exact EReal.coe_lt_top _
  have hev := hut.eventually (lt_mem_nhds hbt)
  filter_upwards [bounded_step_ito_finite_identity P B i a b ha hab G hGm hG N hN hNI] with w hw
  have hn : Tendsto (fun n => N (u n) w) atTop (𝓝 (N ⊤ w)) := (hN.path w).continuousAt.tendsto.comp hut
  have he : (fun n => N (u n) w) =ᶠ[atTop]
      fun _ => G w*(B.W i (realTimeClamp b) w-B.W i (realTimeClamp a) w) := by
    filter_upwards [hev] with n hn
    rw [hw (u n) (hum n).2,min_eq_left hn.le,
      min_eq_left ((real_time_clamp_mono hab).trans hn.le)]
  exact tendsto_nhds_unique hn (tendsto_const_nhds.congr' he.symm)

end Asakura.Chapter12
