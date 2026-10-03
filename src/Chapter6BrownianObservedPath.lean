import Chapter6BrownianContinuousCoefficient
import Chapter6ItoPathFactor

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

noncomputable def brownianObservedPath {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ) (R : ℝ) (hR : 0≤R) :
    Ω → C(Icc (0:ℝ) R,Fin d → ℝ) := fun w => ⟨fun r => x+L (fun j => B.W j (realTimeClamp r.val) w),by
      apply continuous_const.add
      apply L.continuous.comp
      apply continuous_pi
      intro j
      have hc := open_path_stopped_continuous (B.W j) ((B.martingale j).path P B.F) R hR (EReal.coe_lt_top _) w
      have he : (fun r : Icc (0:ℝ) R => B.W j (realTimeClamp r.val) w)=
        (fun r : Icc (0:ℝ) R => B.W j (min (realTimeClamp R) (realTimeClamp r.val)) w) := by
        funext r
        rw [min_eq_right (real_time_clamp_mono r.property.2)]
      rw [he]
      exact hc.comp (real_time_clamp_continuous.comp continuous_subtype_val)⟩

theorem brownian_observed_path_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ) (R : ℝ) (hR : 0≤R) :
    Measurable (brownianObservedPath P B L x R hR) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  apply measurable_const.add
  apply L.continuous.measurable.comp
  exact measurable_pi_iff.mpr (fun j => ((B.martingale j).adapted P B.F _
    (changed_time_finite _ r.property.1)).mono (B.le _) le_rfl)

theorem brownian_observed_path_recovers {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ) (R : ℝ) (hR : 0≤R)
    (r : ℝ) (hr : r∈Icc 0 R) (j : Fin d) :
    Measurable[MeasurableSpace.comap (brownianObservedPath P B L x R hR) inferInstance]
      (B.W j (realTimeClamp r)) := by
  let X := brownianObservedPath P B L x R hR
  let G := MeasurableSpace.comap X inferInstance
  letI : MeasurableSpace Ω := G
  have hX : Measurable X := Measurable.of_comap_le le_rfl
  have hm : Measurable (fun w => L.symm (X w ⟨r,hr⟩-x) j) :=
    (measurable_pi_apply j).comp (L.symm.continuous.measurable.comp
      (((ContinuousMap.measurable_eval (⟨r,hr⟩ : Icc (0:ℝ) R)).comp hX).sub measurable_const))
  simpa only [X,brownianObservedPath,ContinuousMap.coe_mk,add_sub_cancel_left,L.symm_apply_apply] using hm

end Asakura.Chapter6
