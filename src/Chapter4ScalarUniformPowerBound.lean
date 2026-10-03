import Chapter4PowerGronwall
import Chapter4VolterraPathLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- A bound depending on p, the horizon, coefficient growth and the initial
moment, but independent of any localization level. -/
theorem scalar_integral_uniform_power_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A N : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A) (hN : LocalMProcessWitness P F N)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (G : Ω × ℝ → ℝ)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hNI : ItoCovarianceFormula P F W G N)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (p : ℝ) (hp : 2≤p)
    (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (hYm : Measurable[m] Y) (hYi : MemLp Y (ENNReal.ofReal p) P)
    (ξ : Ω → ℝ) (hξm : Measurable[m] ξ) (hξi : MemLp ξ (ENNReal.ofReal p) P)
    (U : Ω × ℝ → ℝ) (hUm : Measurable[m.prod inferInstance] U) (hGm : Measurable[m.prod inferInstance] G)
    (K : ℝ) (hK : 0≤K)
    (hUg : ∀ w r,r∈Icc 0 R → |U (w,r)|^p≤K*(1+|Y w (projIcc 0 R hR r)|^p))
    (hGg : ∀ w r,r∈Icc 0 R → |G (w,r)|^p≤K*(1+|Y w (projIcc 0 R hR r)|^p))
    (hrep : ∀ᵐ w ∂P,∀ r,Y w r=ξ w+(∫ s in 0..r.val,U (w,s))+N (realTimeClamp r.val) w) :
    (∫ w,‖Y w‖^p ∂P)≤
      ((3:ℝ)^(p-1)*(∫ w,|ξ w|^p ∂P)+momentGrowthRate R p K*R)*Real.exp ((momentGrowthRate R p K+1)*R) := by
  letI : MeasurableSpace Ω := m
  have hp0 : 0<p := by linarith only [hp]
  let u := fun t => ∫ w,‖prefixPath hR (Y w) t‖^p ∂P
  have hu : Continuous u := prefix_power_moment_continuous P hR Y hYm p hp0 hYi
  have hh := moment_gronwall_bound R p K (∫ w,|ξ w|^p ∂P) hR hp hK
    (integral_nonneg (fun w => Real.rpow_nonneg (abs_nonneg _) _)) u hu
    (fun r => integral_nonneg (fun w => Real.rpow_nonneg (norm_nonneg _) _))
    (fun d hd => scalar_integral_prefix_power_estimate P hT F hF hle hnull W A N hW hA hN
      c hc hcm hcT hct hcut hcc hclock G hG hi hNI R hR hRT p hp Y hYm hYi ξ hξm hξi
      U hUm hGm K hK hUg hGg hrep d hd)
  simpa only [u,prefix_path_endpoint] using hh

end Asakura.Chapter4
