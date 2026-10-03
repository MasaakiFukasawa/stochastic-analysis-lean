import Chapter4ODEPathVariation
import Chapter4ClockRegularity
import Chapter3C1WeightedProduct

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Every C1 deterministic function of the clock is an adapted locally
bounded-variation process, including nonmonotone matrix-exponential entries. -/
theorem C1_clock_adapted_variation
    {Ω : Type*} {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (A : ClosedTime T → Ω → ℝ)
    (hAa : ∀ t,t<⊤ → Measurable[F t] (A t))
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) :
    AdaptedLocalVariationWitness F (fun t w => v (A t w)) := by
  obtain ⟨_,hAc⟩ := clock_regular_from_identity A hclock
  have hvc w t (ht : t<⊤) := hv.continuous.continuousAt.comp (hAc w t ht)
  have hder := hv.continuous_deriv le_rfl
  apply ode_adapted_local_variation hT F hF (fun t w => v (A t w)) (fun r _ => deriv v r)
    (fun t ht => hv.continuous.measurable.comp (hAa t ht)) hvc
    (fun _ _ _ _ => hder.continuousOn)
  intro w r hr hrT
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨n,hn⟩ := hcc _ (real_time_below r hr.le hrT)
  have hrn : r<c n := by
    change (realTimeClamp r:EReal)<(realTimeClamp (c n):EReal) at hn
    rw [real_time_clamp_eq r hr.le hrT.le,real_time_clamp_eq (c n) (hc n).le (hcT n).le] at hn
    exact EReal.coe_lt_coe_iff.mp hn
  have he : (fun s => v (A (realTimeClamp s) w))=ᶠ[𝓝 r] v := by
    filter_upwards [isOpen_Ioo.mem_nhds (show r∈Ioo 0 (c n) from ⟨hr,hrn⟩)] with s hs
    rw [hclock w s hs.1.le ((EReal.coe_lt_coe hs.2).trans (hcT n))]
  exact ((hv.differentiable (by norm_num)).differentiableAt.hasDerivAt).congr_of_eventuallyEq he

end Asakura.Chapter4
