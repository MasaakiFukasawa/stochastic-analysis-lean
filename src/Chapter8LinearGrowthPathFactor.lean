import Chapter6BrownianObservedPath
import Chapter8ContinuousStoppedCoefficient
import Chapter8DominatedItoPathFactor
import Chapter6BrownianPathEnvelope

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8
open Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

theorem linear_growth_coefficient_ito_path_factor {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ)
    (b : ℝ × (Fin d → ℝ) → Fin d → ℝ) (hb : Continuous b)
    (R : ℝ) (hR : 0<R) (K : ℝ) (hK : 0≤K) (hbb : ∀ z,‖WithLp.toLp 2 (b z)‖≤K*(1+‖WithLp.toLp 2 z.2‖))
    (j : Fin d) (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W j)
      (fun z => stoppedBrownianCoefficient P B b R hR.le j (realTimeClamp z.2) z.1) N) :
    ∃ a : C(Icc (0:ℝ) R,Fin d → ℝ) → ℝ,Measurable a ∧
      N (realTimeClamp R)=ᵐ[P] a ∘ brownianObservedPath P B L x R hR.le := by
  let H := stoppedBrownianCoefficient P B b R hR.le
  let X := brownianObservedPath P B L x R hR.le
  obtain ⟨hHa,hHc,hrep⟩ := continuous_stopped_brownian_coefficient_regular P B b hb R hR.le
  obtain ⟨G,hG,hGp,hGb⟩ := brownian_path_L2_envelope P B R hR.le
  let D := fun w => K*(1+G w)
  have hD : MemLp D 2 P := ((memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 P).add hG).const_mul K
  have hDp w : 0≤D w := mul_nonneg hK (by linarith [hGp w])
  have hbound w r (hr : r∈Icc 0 R) : |H j (realTimeClamp r) w|≤D w := by
    dsimp only [H]
    rw [hrep j w r hr]
    have hi := PiLp.norm_apply_le (WithLp.toLp 2 (b (r,fun i => B.W i (realTimeClamp r) w))) j
    exact hi.trans ((hbb _).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hGb w r hr)) hK))
  have hHX r (hr : r∈Icc 0 R) : Measurable[MeasurableSpace.comap X inferInstance] (H j (realTimeClamp r)) := by
    letI : MeasurableSpace Ω := MeasurableSpace.comap X inferInstance
    have hm i := brownian_observed_path_recovers P B L x R hR.le r hr i
    have hm' : Measurable (fun w => b (r,fun i => B.W i (realTimeClamp r) w) j) :=
      (measurable_pi_apply j).comp (hb.measurable.comp (measurable_const.prodMk (measurable_pi_iff.mpr hm)))
    convert hm' using 1
    funext w
    exact hrep j w r hr
  exact dominated_ito_path_factor P B j (H j) N (hHa j) (hHc j) hN hNI R hR D hD hDp hbound
    X (brownian_observed_path_measurable P B L x R hR.le) hHX
    (fun r hr => brownian_observed_path_recovers P B L x R hR.le r hr j)

end Asakura.Chapter8
