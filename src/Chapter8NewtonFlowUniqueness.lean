import Chapter8ConstructedNewtonFlow
import Chapter8AdditiveUniqueness

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Two position-velocity solutions driven by the same continuous forcing
coincide. This identifies the constructed joint flow with any SDE realization
once its component integral equations have been obtained. -/
theorem newton_flow_unique {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g) (δ T : ℝ) (hT : 0≤T)
    (X Y : ℝ → E × E) (W : ℝ → E) (x : E × E)
    (hX : Continuous X) (hY : Continuous Y)
    (hqX : ∀ t∈Icc 0 T,(X t).1=x.1+∫ s in 0..t,(X s).2)
    (hqY : ∀ t∈Icc 0 T,(Y t).1=x.1+∫ s in 0..t,(Y s).2)
    (hvX : ∀ t∈Icc 0 T,(X t).2=x.2+(∫ s in 0..t,-g (X s).1-δ • (X s).2)+W t)
    (hvY : ∀ t∈Icc 0 T,(Y t).2=x.2+(∫ s in 0..t,-g (Y s).1-δ • (Y s).2)+W t) :
    ∀ t∈Icc 0 T,X t=Y t := by
  let b : (E × E) → (E × E) := fun z => (z.2,-g z.1-δ • z.2)
  have hb : LipschitzWith (max 1 (L+‖δ‖₊)) b := by
    simpa only [mul_one,Function.comp_def,Pi.neg_apply,b] using
      (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : E × E → E)).prodMk
        ((hg.comp LipschitzWith.prod_fst).neg.sub
          ((lipschitzWith_smul δ).comp LipschitzWith.prod_snd))
  have assemble (Z : ℝ → E × E) (hc : Continuous Z)
      (hq : ∀ t∈Icc 0 T,(Z t).1=x.1+∫ s in 0..t,(Z s).2)
      (hv : ∀ t∈Icc 0 T,(Z t).2=x.2+(∫ s in 0..t,-g (Z s).1-δ • (Z s).2)+W t) :
      ∀ t∈Icc 0 T,Z t=x+(∫ s in 0..t,b (Z s))+(0,W t) := by
    intro t ht
    have hi := (hb.continuous.comp hc).intervalIntegrable 0 t (μ := volume)
    have hi₁ := (ContinuousLinearMap.fst ℝ E E).intervalIntegral_comp_comm hi
    have hi₂ := (ContinuousLinearMap.snd ℝ E E).intervalIntegral_comp_comm hi
    apply Prod.ext
    · change (Z t).1=x.1+(∫ s in 0..t,b (Z s)).1+0
      change (∫ s in 0..t,(Z s).2)=(∫ s in 0..t,b (Z s)).1 at hi₁
      rw [add_zero,←hi₁]
      exact hq t ht
    · change (Z t).2=x.2+(∫ s in 0..t,b (Z s)).2+W t
      change (∫ s in 0..t,-g (Z s).1-δ • (Z s).2)=(∫ s in 0..t,b (Z s)).2 at hi₂
      rw [←hi₂]
      exact hv t ht
  exact additive_path_unique b _ hb X Y (fun t => (0,W t)) hX hY x T hT
    (assemble X hX hqX hvX) (assemble Y hY hqY hvY)

end Asakura.Chapter8
