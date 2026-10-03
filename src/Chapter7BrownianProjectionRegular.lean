import Chapter7BrownianSecondMoments
import Chapter6AffineBrownianPaths

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- A real-time projection of Brownian increments, extended constantly before
zero, with joint measurability derived from its continuous sample paths. -/
theorem brownian_projection_regular {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) :
    let X := fun r w => ∑ j,u j*(B.W j (realTimeClamp (max 0 r)) w-B.W j (realTimeClamp 0) w)
    (∀ w,Continuous (fun r => X r w)) ∧ Measurable (fun z : Ω × ℝ => X z.2 z.1) := by
  classical
  cases d with
  | zero =>
    simp only [Finset.univ_eq_empty,Finset.sum_empty]
    exact ⟨fun _ => continuous_const,measurable_const⟩
  | succ d =>
    let X := fun r w => ∑ j,u j*(B.W j (realTimeClamp (max 0 r)) w-B.W j (realTimeClamp 0) w)
    let V := fun r w => ∑ j,u j*B.W j (realTimeClamp (max 0 r)) w
    have hv := Asakura.Chapter6.affine_brownian_regular P B (fun _ j => u j)
      (fun _ _ => 0) measurable_const
    have hvc (w : Ω) : Continuous (fun r => V r w) := by
      simpa only [zero_add,V,Function.comp_def] using (continuous_apply (0 : Fin (d+1))).comp (hv.2.1 w)
    have hvm (r : ℝ) : Measurable (V r) := by
      simpa only [zero_add,V,Function.comp_def] using (measurable_pi_apply (0 : Fin (d+1))).comp (hv.1 r)
    have he r w : X r w=V r w-V 0 w := by
      dsimp only [X,V,max_self]
      simp only [mul_sub,Finset.sum_sub_distrib,max_self]
    have hc (w : Ω) : Continuous (fun r => X r w) := by
      simp only [he]
      exact (hvc w).sub continuous_const
    have hm (r : ℝ) : Measurable (X r) := by
      have he' : X r=fun w => V r w-V 0 w := funext (he r)
      rw [he']
      exact (hvm r).sub (hvm 0)
    change (∀ w,Continuous (fun r => X r w)) ∧ Measurable (fun z : Ω × ℝ => X z.2 z.1)
    have hj : Measurable (Function.uncurry X) := measurable_uncurry_of_continuous_of_measurable hc hm
    refine ⟨hc,?_⟩
    simpa only [Function.comp_def,Function.uncurry_def,Prod.swap] using hj.comp measurable_swap

end Asakura.Chapter7
