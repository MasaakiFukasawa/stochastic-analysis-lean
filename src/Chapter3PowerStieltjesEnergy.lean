import Chapter3RegularizedStieltjesEnergy

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The unregularized Stieltjes energy substitution for p>2, valid also at A=0. -/
theorem power_stieltjes_energy_identity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (A I : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ᵐ ω ∂P, A ⊥ ω = 0)
    (p : ℝ) (hp : 2 < p)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hI : VariationIntegralFormula P c hc A
      (fun z => A (realTimeClamp z.2) z.1^(p/2-1)) I) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → I t ω = (2/p)*A t ω^(p/2) := by
  have hi := variation_integral_scalar_multiple P A I _ c hc hI (p/2)
  have hi' : VariationIntegralFormula P c hc A
      (fun z => deriv (fun x : ℝ => x^(p/2)) (A (realTimeClamp z.2) z.1))
      (fun t ω => (p/2)*I t ω) := by
    simpa only [Real.deriv_rpow_const] using hi
  have hf : ContDiff ℝ 1 (fun x : ℝ => x^(p/2)) :=
    Real.contDiff_rpow_const_of_le (n := 1) (by norm_num; linarith)
  have h := continuous_variation_chain_rule P hT F hF hle A (fun t ω => (p/2)*I t ω)
    hA hAc (fun x : ℝ => x^(p/2)) hf c hc hcT hcc hi'
  filter_upwards [h,hA0] with ω hω h0
  intro t ht
  have he := hω t ht
  rw [h0,Real.zero_rpow (by linarith : p/2 ≠ 0),zero_add] at he
  have hp0 : p ≠ 0 := by linarith
  field_simp [hp0]
  nlinarith

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.power_stieltjes_energy_identity
