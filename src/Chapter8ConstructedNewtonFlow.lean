import Chapter8MeasurableAdditiveFlow
import Chapter8NewtonFiniteTransport

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Construct the joint position-velocity solution map before applying the
Newton energy estimate. Both component integral equations follow from the
Banach-valued equation, rather than being postulated. -/
theorem constructed_newton_flow {E Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g) (δ T : ℝ) (hT : 0≤T)
    (W : ℝ → Ω → E) (hWm : ∀ t,Measurable (W t))
    (hWc : ∀ w,Continuous (fun t => W t w)) (hW0 : ∀ w,W 0 w=0) :
    ∃ X : ℝ → (E × E) → Ω → (E × E),
      (∀ t,Measurable (Function.uncurry (X t))) ∧
      (∀ x w,Continuous (fun t => X t x w)) ∧ (∀ x w,X 0 x w=x) ∧
      (∀ x w t,t∈Icc 0 T → (X t x w).1=x.1+∫ s in 0..t,(X s x w).2) ∧
      (∀ x w t,t∈Icc 0 T → (X t x w).2=x.2+
        (∫ s in 0..t,-g (X s x w).1-δ • (X s x w).2)+W t w) := by
  let b : (E × E) → (E × E) := fun z => (z.2,-g z.1-δ • z.2)
  have hb : LipschitzWith (max 1 (L+‖δ‖₊)) b := by
    simpa only [mul_one,Function.comp_def,Pi.neg_apply,b] using
      (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : E × E → E)).prodMk
        ((hg.comp LipschitzWith.prod_fst).neg.sub
          ((lipschitzWith_smul δ).comp LipschitzWith.prod_snd))
  obtain ⟨Y,hYm,hYc,hY⟩ := measurable_additive_flow_exists b _ hb
    (fun t w => ((0:E),W t w)) (fun t => measurable_const.prodMk (hWm t))
    (fun w => continuous_const.prodMk (hWc w)) T hT
  let X := fun t x w => Y x t w
  have he x w t (ht : t∈Icc 0 T) : X t x w=x+(∫ s in 0..t,b (X s x w))+(0,W t w) := hY x w t ht
  refine ⟨X,hYm,hYc,?_,?_,?_⟩
  · intro x w
    simpa only [intervalIntegral.integral_same,add_zero,hW0,Prod.mk_zero_zero] using he x w 0 ⟨le_rfl,hT⟩
  · intro x w t ht
    have h := congrArg Prod.fst (he x w t ht)
    have hi := (ContinuousLinearMap.fst ℝ E E).intervalIntegral_comp_comm
      ((hb.continuous.comp (hYc x w)).intervalIntegrable 0 t (μ := volume))
    change (∫ s in 0..t,(b (X s x w)).1)=(∫ s in 0..t,b (X s x w)).1 at hi
    simpa only [Prod.fst_add,add_zero,←hi,b] using h
  · intro x w t ht
    have h := congrArg Prod.snd (he x w t ht)
    have hi := (ContinuousLinearMap.snd ℝ E E).intervalIntegral_comp_comm
      ((hb.continuous.comp (hYc x w)).intervalIntegrable 0 t (μ := volume))
    change (∫ s in 0..t,(b (X s x w)).2)=(∫ s in 0..t,b (X s x w)).2 at hi
    simpa only [Prod.snd_add,←hi,b] using h

end Asakura.Chapter8
