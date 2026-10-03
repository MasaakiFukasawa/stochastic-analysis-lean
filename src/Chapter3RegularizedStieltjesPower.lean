import Chapter3SmoothPositivePower
import Chapter3VariationIntegrandCongruence

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The Stieltjes power substitution used by the regularized BDG proof,
for the actual signed integral, not merely an ordinary integral identity. -/
theorem regularized_stieltjes_power_chain
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (A I : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hAp : ∀ ω t, t < ⊤ → 0 ≤ A t ω)
    (ε r : ℝ) (hε : 0 < ε)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hI : VariationIntegralFormula P c hc A
      (fun z => r*(ε+A (realTimeClamp z.2) z.1)^(r-1)) I) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
      (ε+A t ω)^r = (ε+A ⊥ ω)^r+I t ω := by
  have ha : 0 < ε/4 := by positivity
  let f := fun x => positivePowerExtension (ε/4) r (ε+x)
  have hf : ContDiff ℝ 1 f := (positivePowerExtension_contDiff ha r 1).comp
    (contDiff_const.add contDiff_id)
  have hv x (hx : 0 ≤ x) : f x = (ε+x)^r :=
    (positivePowerExtension_value_deriv ha (by linarith : 2*(ε/4) < ε+x) r).1
  have hd x (hx : 0 ≤ x) : deriv f x = r*(ε+x)^(r-1) := by
    have hbase : HasDerivAt (positivePowerExtension (ε/4) r)
        (deriv (positivePowerExtension (ε/4) r) (ε+x)) (ε+x) :=
      ((positivePowerExtension_contDiff ha r 1).differentiable one_ne_zero).differentiableAt.hasDerivAt
    have hcomp := hbase.comp x ((hasDerivAt_id x).const_add ε)
    have he := (positivePowerExtension_value_deriv ha (by linarith : 2*(ε/4) < ε+x) r).2
    simpa only [he,mul_one,f,Function.comp_def] using hcomp.deriv
  have hI' : VariationIntegralFormula P c hc A
      (fun z => deriv f (A (realTimeClamp z.2) z.1)) I := by
    apply variation_integral_integrand_congr_on_domain P A I _ _ c hc hcT hI
    apply Filter.Eventually.of_forall
    intro ω s hs hsT
    have hst : realTimeClamp (T := T) s < ⊤ := by
      change (realTimeClamp s : EReal) < T
      rw [real_time_clamp_eq _ hs hsT.le]
      exact hsT
    exact (hd _ (hAp ω _ hst)).symm
  have h := continuous_variation_chain_rule P hT F hF hle A I hA hAc f hf c hc hcT hcc hI'
  filter_upwards [h] with ω hω
  intro t ht
  simpa only [hv _ (hAp ω t ht),hv _ (hAp ω ⊥ hT)] using hω t ht

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.regularized_stieltjes_power_chain
