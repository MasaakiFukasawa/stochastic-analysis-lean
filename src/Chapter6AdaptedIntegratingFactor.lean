import Chapter6IntegratingFactorPrimitive
import Chapter5ProgressiveDriftVariation
import Chapter4FinitePathLift
import Chapter3IncreasingAdaptedVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Construct the random integrating factor in A_loc from its actual
time integral, for coefficients of either sign. -/
theorem adapted_integrating_factor {Ω : Type*}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (α : ℝ → Ω → ℝ) (R : ℝ) (hR : 0≤R)
    (ha : ∀ r∈Icc 0 R,Measurable[F (realTimeClamp r)] (α r))
    (hc : ∀ w,Continuous (fun r => α r w)) :
    ∃ A : HalfClosedTime → Ω → ℝ,
      AdaptedLocalVariationWitness F A ∧ (∀ w,Continuous (fun t => A t w)) ∧
      (∀ t w,A t w=linearIntegratingFactor (fun r => α r w) (finitePrefixTime R hR t).val) ∧
      (∀ t w,A t w=1+∫ r in 0..(finitePrefixTime R hR t).val,α r w*A (realTimeClamp r) w) := by
  have hT : (0:EReal)<⊤ := by simp
  let H := fun z : Ω × ℝ => α z.2 z.1
  have hHp := continuous_adapted_real_progressive F hF H R hR ha (fun w => (hc w).continuousOn)
  obtain ⟨U,hU,hUc,hUe⟩ := progressive_integrable_drift_variation hT F hF R hR le_top H hHp
    (fun w => ((hc w).intervalIntegrable 0 R).1)
  let A := fun t w => Real.exp (U t w)
  have hAc w : Continuous (fun t => A t w) := Real.continuous_exp.comp (hUc w)
  have hAa t (ht : t<⊤) : Measurable[F t] (A t) := (hU.adapted t ht).exp
  have he t w : A t w=linearIntegratingFactor (fun r => α r w) (finitePrefixTime R hR t).val := by
    dsimp [A,linearIntegratingFactor]
    rw [hUe]
  let G := fun z : Ω × ℝ => α z.2 z.1*A (realTimeClamp z.2) z.1
  have hGc w : Continuous (fun r => G (w,r)) :=
    (hc w).mul ((hAc w).comp real_time_clamp_continuous)
  have hGp := continuous_adapted_real_progressive F hF G R hR
    (fun r hr => (ha r hr).mul (hAa _ (real_time_below r hr.1 (EReal.coe_lt_top r))))
    (fun w => (hGc w).continuousOn)
  obtain ⟨V,hV,hVc,hVe⟩ := progressive_integrable_drift_variation hT F hF R hR le_top G hGp
    (fun w => ((hGc w).intervalIntegrable 0 R).1)
  have hAV t w : A t w=1+V t w := by
    rw [he,hVe,integrating_factor_primitive _ (hc w)]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc 0 R := by
      have hz := (finitePrefixTime (T := ⊤) R hR t).property
      have hh : r∈Icc 0 (finitePrefixTime (T := ⊤) R hR t).val := by
        simpa only [uIcc_of_le hz.1] using hr
      exact ⟨hh.1,hh.2.trans hz.2⟩
    dsimp [G]
    rw [he,finite_prefix_time_of_real R r hR hr' le_top]
  have h1 := continuous_increasing_adapted_variation hT F hF (fun _ (_ : Ω) => (1:ℝ))
    (fun _ _ => measurable_const) (fun _ _ _ _ _ _ => le_rfl) (fun _ _ _ => continuousAt_const)
  have hAv : AdaptedLocalVariationWitness F A := by
    have heq : A=(fun t w => 1+V t w) := funext (fun t => funext (hAV t))
    rw [heq]
    exact h1.add hV hF
  refine ⟨A,hAv,hAc,he,?_⟩
  intro t w
  rw [hAV,hVe]

end Asakura.Chapter6
