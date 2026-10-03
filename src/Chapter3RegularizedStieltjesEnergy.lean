import Chapter3RegularizedStieltjesPower
import Chapter3VariationScalarIntegral

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The exact 2/p energy identity appearing in the p<2 BDG proof. -/
theorem regularized_stieltjes_energy_identity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (A I : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hAp : ∀ ω t, t < ⊤ → 0 ≤ A t ω)
    (hA0 : ∀ᵐ ω ∂P, A ⊥ ω = 0)
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hI : VariationIntegralFormula P c hc A
      (fun z => (ε+A (realTimeClamp z.2) z.1)^(p/2-1)) I) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
      I t ω = (2/p)*((ε+A t ω)^(p/2)-ε^(p/2)) := by
  have hi := variation_integral_scalar_multiple P A I _ c hc hI (p/2)
  have h := regularized_stieltjes_power_chain P hT F hF hle A (fun t ω => (p/2)*I t ω)
    hA hAc hAp ε (p/2) hε c hc hcT hcc hi
  filter_upwards [h,hA0] with ω hω h0
  intro t ht
  have he := hω t ht
  rw [h0,add_zero] at he
  field_simp [hp.ne']
  nlinarith

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.regularized_stieltjes_energy_identity
