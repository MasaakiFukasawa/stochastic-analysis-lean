import Chapter4C12ClockIto
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false

/-- Regularity of a continuous function of time and a vector semimartingale. -/
theorem vector_time_integrand_regularity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω)
    (X A M : Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i,SemimartingaleDecomposition P F (X i) (A i) (M i))
    (R : ℝ) (hR : 0≤R) (ψ : ℝ × (Fin d → ℝ) → ℝ) (hψ : Continuous ψ) :
    let H := fun z : Ω × ℝ => ψ ((finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val,
      fun i => X i (realTimeClamp z.2) z.1)
    (∀ w,Measurable (fun r => H (w,r))) ∧
    (∀ r : ℝ,0≤r → (r:EReal)<T → Measurable[F (realTimeClamp r)] (fun w => H (w,r))) ∧
    (∀ b : ℝ,0≤b → (b:EReal)<T → ∀ w,ContinuousOn (fun r => H (w,r)) (Icc 0 b)) := by
  dsimp only
  have hK : Continuous (fun r : ℝ => (finitePrefixTime (T := T) R hR (realTimeClamp r)).val) :=
    continuous_subtype_val.comp ((finite_prefix_time_continuous R hR).comp real_time_clamp_continuous)
  have hfinite (r : ℝ) (hr : 0≤r) (hrT : (r:EReal)<T) : realTimeClamp (T := T) r<⊤ := by
    change (realTimeClamp r:EReal)<T
    rw [real_time_clamp_eq r hr hrT.le]
    exact hrT
  refine ⟨?_,?_,?_⟩
  · intro w
    exact hψ.measurable.comp (hK.measurable.prodMk (Measurable.of_eval fun i =>
      open_path_real_measurable _ ((hX i).continuous w)))
  · intro r hr hrT
    letI : MeasurableSpace Ω := F (realTimeClamp r)
    apply hψ.measurable.comp
    apply measurable_const.prodMk
    apply Measurable.of_eval
    intro i
    have he : X i (realTimeClamp r)=fun w => A i (realTimeClamp r) w+M i (realTimeClamp r) w :=
      funext ((hX i).decomposition _ (hfinite r hr hrT))
    change Measurable[F (realTimeClamp r)] (X i (realTimeClamp r))
    rw [he]
    exact ((hX i).variation.adapted _ (hfinite r hr hrT)).add
      ((hX i).martingale.adapted P F _ (hfinite r hr hrT))
  · intro b hb hbT w
    apply hψ.comp_continuousOn
    intro r hr
    apply ContinuousAt.continuousWithinAt
    exact hK.continuousAt.prodMk (continuousAt_pi.mpr fun i =>
      ((hX i).continuous w _ (hfinite r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hbT))).comp
        real_time_clamp_continuous.continuousAt)

end Asakura.Chapter4
