import Chapter4UnboundedElementaryCovariance
import Chapter4BrownianElementaryM2
import Chapter3IdentityItoIntegral
import Chapter2SignedDensityIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Covariance characterization of an unbounded elementary integral, once
its local-martingale property has been established. -/
theorem unbounded_elementary_ito_formula
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b)
    (G : Ω → ℝ) (hGa : Measurable[F (realTimeClamp a)] G)
    (hZ : LocalMProcessWitness P F (fun t w => G w*(X (min (realTimeClamp b) t) w-X (min (realTimeClamp a) t) w))) :
    ItoCovarianceFormula P F X (fun z => (Ioc a b).indicator (fun _ => G z.1) z.2)
      (fun t w => G w*(X (min (realTimeClamp b) t) w-X (min (realTimeClamp a) t) w)) := by
  intro Y C hY hC
  obtain ⟨D,hD⟩ := local_covariance_witness_exists P F hF hle hnull _ Y hZ hY
  refine ⟨D,hD,?_⟩
  intro d hd hdT
  obtain ⟨_,_,hform⟩ := identity_ito_integral P hT F hF hle hnull X hX Y C hY hC
  obtain ⟨ν,hν,hν0,_,_⟩ := hform d hd hdT
  refine ⟨ν,hν,hν0,ae_of_all _ (fun w => (integrable_const (G w)).indicator measurableSet_Ioc),?_⟩
  have he := unbounded_elementary_covariance P F hF hle hnull X Y C hX hY hC
    (realTimeClamp a) (realTimeClamp b) (real_time_clamp_mono hab) G hGa hZ D hD
    (realTimeClamp d) (real_time_below d hd hdT)
  filter_upwards [he] with w hw
  rw [hw,signed_integral_indicator_const _ _ measurableSet_Ioc,hν w a b ha hab]

/-- The elementary Brownian integral of any L2 left-endpoint coefficient
is both an M2 process and the Ito integral from Chapter 2. -/
theorem brownian_elementary_ito_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (b : ℝ) (hb : 0≤b) (hbT : (b:EReal)<T) (a : ℝ) (ha : a∈Icc 0 b)
    (G : Ω → ℝ) (hGa : Measurable[F (realTimeClamp a)] G) (hG : MemLp G 2 P) :
    let Z := fun t w => G w*(W (min (realTimeClamp b) t) w-W (min (realTimeClamp a) t) w)
    ContinuousM2Witness P F Z ∧ LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F W (fun z => (Ioc a b).indicator (fun _ => G z.1) z.2) Z := by
  dsimp only
  have hz := brownian_elementary_m2 P hT F hF hle hnull W A hW hA hclock b hb hbT a ha G hGa hG
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hl := continuous_m2_is_local P F hF hle (fun n => realTimeClamp (c n)) hct.monotone hcut hcc _ hz
  exact ⟨hz,hl,unbounded_elementary_ito_formula P hT F hF hle hnull W hW a b ha.1 ha.2 G hGa hl⟩

end Asakura.Chapter4
