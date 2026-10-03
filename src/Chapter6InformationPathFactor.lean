import Chapter6BrownianObservedPath
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The information entries are ordinary measurable functions of the
observed continuous path, constructed by time integration. -/
theorem information_entry_path_factor {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ)
    (b c : ℝ × (Fin d → ℝ) → Fin d → ℝ) (hb : Continuous b) (hc : Continuous c)
    (R : ℝ) (hR : 0≤R) :
    ∃ J : C(Icc (0:ℝ) R,Fin d → ℝ) → ℝ,Measurable J ∧
      (fun w => ∫ r in 0..R,∑ j,b (r,fun i => B.W i (realTimeClamp r) w) j*
        c (r,fun i => B.W i (realTimeClamp r) w) j)=J ∘ brownianObservedPath P B L x R hR := by
  let E := C(Icc (0:ℝ) R,Fin d → ℝ)
  let τ := fun r => finitePrefixTime (T := ⊤) R hR (realTimeClamp r)
  have hτ : Continuous τ := (finite_prefix_time_continuous R hR).comp real_time_clamp_continuous
  let f := fun z : E × ℝ => ∑ j,b (z.2,L.symm (z.1 (τ z.2)-x)) j*c (z.2,L.symm (z.1 (τ z.2)-x)) j
  have he : Continuous (fun z : E × ℝ => z.1 (τ z.2)) := continuous_fst.eval (hτ.comp continuous_snd)
  have hstate : Continuous (fun z : E × ℝ => (z.2,L.symm (z.1 (τ z.2)-x))) :=
    continuous_snd.prodMk (L.symm.continuous.comp (he.sub continuous_const))
  have hf : Continuous f := by
    apply continuous_finset_sum
    intro j _
    exact ((continuous_apply j).comp (hb.comp hstate)).mul ((continuous_apply j).comp (hc.comp hstate))
  let J := fun y : E => ∫ r in Ioc 0 R,f (y,r)
  have hJ : Measurable J := (hf.measurable.stronglyMeasurable.integral_prod_right').measurable
  refine ⟨J,hJ,?_⟩
  funext w
  rw [intervalIntegral.integral_of_le hR]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  have hτr : τ r=⟨r,⟨hr.1.le,hr.2⟩⟩ := Subtype.ext (finite_prefix_time_of_real R r hR ⟨hr.1.le,hr.2⟩ le_top)
  change (∑ j,b (r,fun i => B.W i (realTimeClamp r) w) j*c (r,fun i => B.W i (realTimeClamp r) w) j)=f (brownianObservedPath P B L x R hR w,r)
  simp only [f,hτr]
  change (∑ j,b (r,fun i => B.W i (realTimeClamp r) w) j*c (r,fun i => B.W i (realTimeClamp r) w) j)=
    ∑ j,b (r,L.symm ((x+L (fun i => B.W i (realTimeClamp r) w))-x)) j*c (r,L.symm ((x+L (fun i => B.W i (realTimeClamp r) w))-x)) j
  simp only [add_sub_cancel_left,L.symm_apply_apply]

end Asakura.Chapter6
