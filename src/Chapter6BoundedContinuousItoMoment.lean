import Chapter6ItoTerminalErrorBound
import Chapter6ContinuousItoGridLimit

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem bounded_continuous_ito_terminal_memLp {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d) (j : Fin d)
    (H N : HalfClosedTime → Ω → ℝ)
    (hHa : ∀ t,Measurable[B.F t] (H t)) (hHc : ∀ w,Continuous (fun t => H t w))
    (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W j) (fun z => H (realTimeClamp z.2) z.1) N)
    (K : ℝ) (hHb : ∀ t w,|H t w|≤K) (R : ℝ) (hR : 0≤R) :
    MemLp (N (realTimeClamp R)) 2 P := by
  let G := fun z : Ω × ℝ => H (realTimeClamp z.2) z.1
  have hGr w : Continuous (fun r => G (w,r)) := (hHc w).comp real_time_clamp_continuous
  have hGm : Measurable G := by
    have hm r : Measurable (H (realTimeClamp r)) := (hHa _).mono (B.le _) le_rfl
    simpa only [G,Function.comp_def,Function.uncurry_def,Prod.swap] using (measurable_uncurry_of_continuous_of_measurable hGr hm).comp measurable_swap
  have hGp r (hr : 0≤r) := continuous_adapted_real_progressive B.F B.mono G r hr
    (fun s _ => hHa _) (fun w => (hGr w).continuousOn)
  have hGi r (hr : 0≤r) : ∀ᵐ w ∂P,Integrable (fun s => G (w,s)^2) (volume.restrict (Ioc 0 r)) := ae_of_all _ (fun w =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mp (((hGr w).pow 2).continuousOn.intervalIntegrable_of_Icc hr))
  have hG2 : MemLp G 2 (P.prod (volume.restrict (Ioc 0 R))) := MemLp.of_bound hGm.aestronglyMeasurable K (ae_of_all _ (fun z => hHb _ _))
  exact (brownian_ito_terminal_square_bound P B j N G hN hNI hGp hGi R hR hG2).1

end Asakura.Chapter6
