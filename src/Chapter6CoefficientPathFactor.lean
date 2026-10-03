import Chapter6BrownianObservedPath

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem brownian_coefficient_ito_path_factor {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ)
    (b : ℝ × (Fin d → ℝ) → Fin d → ℝ) (hb : Continuous b)
    (R : ℝ) (hR : 0<R) (K : ℝ) (hK : 0≤K) (hbb : ∀ z,‖WithLp.toLp 2 (b z)‖≤K)
    (j : Fin d) (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W j)
      (fun z => stoppedBrownianCoefficient P B b R hR.le j (realTimeClamp z.2) z.1) N) :
    ∃ a : C(Icc (0:ℝ) R,Fin d → ℝ) → ℝ,Measurable a ∧
      N (realTimeClamp R)=ᵐ[P] a ∘ brownianObservedPath P B L x R hR.le := by
  let H := stoppedBrownianCoefficient P B b R hR.le
  let X := brownianObservedPath P B L x R hR.le
  obtain ⟨hHa,hHc,hHb,hrep⟩ := stopped_brownian_coefficient_regular P B b hb R hR.le K hbb
  have hHX r (hr : r∈Icc 0 R) : Measurable[MeasurableSpace.comap X inferInstance] (H j (realTimeClamp r)) := by
    letI : MeasurableSpace Ω := MeasurableSpace.comap X inferInstance
    have hm i := brownian_observed_path_recovers P B L x R hR.le r hr i
    have hm' : Measurable (fun w => b (r,fun i => B.W i (realTimeClamp r) w) j) :=
      (measurable_pi_apply j).comp (hb.measurable.comp (measurable_const.prodMk (measurable_pi_iff.mpr hm)))
    convert hm' using 1
    funext w
    exact hrep j w r hr
  exact bounded_ito_path_factor P B j (H j) N (hHa j) (hHc j) hN hNI R hR K hK
    (fun w r _ => (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => H i (realTimeClamp r) w)) j).trans (hHb _ _))
    X (brownian_observed_path_measurable P B L x R hR.le) hHX
    (fun r hr => brownian_observed_path_recovers P B L x R hR.le r hr j)

end Asakura.Chapter6
