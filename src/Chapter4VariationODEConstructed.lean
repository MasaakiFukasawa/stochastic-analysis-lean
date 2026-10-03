import Chapter4ConstructedODEExample
import Chapter3VariationChainRule

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The finite-variation approximating paths solve their actual Stieltjes
integral equation. This supplies the missing chain-rule step in the exercise. -/
theorem variation_ode_composition_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (A : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hAc : ∀ w t,t<⊤ → ContinuousAt (fun s => A s w) t)
    (hA0 : ∀ w,A ⊥ w=0)
    (φ f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hφ : ∀ x,HasDerivAt φ (f (φ x)) x)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n)) :
    ∃ I : ClosedTime T → Ω → ℝ,
      AdaptedLocalVariationWitness F I ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => I s w) t) ∧
      VariationIntegralFormula P c hc A (fun z => f (φ (A (realTimeClamp z.2) z.1))) I ∧
      ∀ᵐ w ∂P,∀ t,t<⊤ → φ (A t w)=φ 0+I t w := by
  have hφc := (ode_solution_c2 φ f hf hφ).continuous
  let H := fun t w => f (φ (A t w))
  have hreg := open_process_real_regularity F H
    (fun t ht => (hf.continuous.comp hφc).measurable.comp (hA.adapted t ht))
    (fun w t ht => (hf.continuous.comp hφc).continuousAt.comp (hAc w t ht))
  obtain ⟨I,hI,hIc,hIf⟩ := continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc A hA hAc
    (fun z => H (realTimeClamp z.2) z.1) hreg.1 hreg.2
  have hd : deriv φ=fun x => f (φ x) := funext (fun x => (hφ x).deriv)
  have hchain := continuous_variation_chain_rule P hT F hF hle A I hA hAc φ
    ((ode_solution_c2 φ f hf hφ).of_le (by norm_num)) c hc hcT hcc
    (by simpa only [hd] using hIf)
  refine ⟨I,hI,hIc,hIf,?_⟩
  filter_upwards [hchain] with w hw
  intro t ht
  simpa only [hA0] using hw t ht

/-- Pointwise convergence of the given driving approximations suffices:
no uniform convergence hypothesis on them is inserted. -/
theorem variation_ode_approximation_limit
    {Ω : Type*} {D : Type*} (A : ℕ → D → Ω → ℝ) (W : D → Ω → ℝ)
    (φ f : ℝ → ℝ) (hφ : ∀ x,HasDerivAt φ (f (φ x)) x)
    (hlim : ∀ t w,Tendsto (fun n => A n t w) atTop (𝓝 (W t w))) :
    ∀ t w,Tendsto (fun n => φ (A n t w)) atTop (𝓝 (φ (W t w))) := by
  intro t w
  exact (hφ (W t w)).continuousAt.tendsto.comp (hlim t w)

end Asakura.Chapter4
