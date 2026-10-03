import Chapter3VariationIntegratorCongruence
import Chapter2SignedDensityIntegral
import Chapter2ContinuousVariationAssociativity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Scalar multiplication in the actual signed Stieltjes integral. -/
theorem variation_integrand_scalar
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n,0 ≤ c n)
    (A I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ) (a : ℝ)
    (hI : VariationIntegralFormula P c hc A H I) :
    VariationIntegralFormula P c hc A (fun z => a*H z) (fun t w => a*I t w) := by
  intro n
  obtain ⟨ν,hs,hν,hi,he⟩ := hI n
  refine ⟨ν,hs,hν,hi.mono (fun w hw => hw.const_mul a),?_⟩
  filter_upwards [he] with w hw
  intro t
  rw [hw t]
  unfold signedCumulative
  have hind (r : ℝ) : (Iic (finitePrefixTime (c n) (hc n) t).val).indicator
      (fun r => a*H (w,r)) r =
      a*((Iic (finitePrefixTime (c n) (hc n) t).val).indicator (fun r => H (w,r)) r) := by
    by_cases hr : r ∈ Iic (finitePrefixTime (c n) (hc n) t).val <;> simp [hr]
  change a*signedIntegralRaw (ν w) _ = signedIntegralRaw (ν w) ((Iic _).indicator (fun r => a*H (w,r)))
  rw [funext hind]
  exact (signed_integral_const_mul (ν w) _ a).symm

/-- Rescaling the integrator is justified by the C¹ chain rule and
associativity, rather than by a formal differential manipulation. -/
theorem variation_scaled_integrator_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (A : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hAc : ∀ w t,t < ⊤ → ContinuousAt (fun s => A s w) t)
    (H : Ω × ℝ → ℝ)
    (hHa : ∀ r : ℝ,0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun w => H (w,r)))
    (hHc : ∀ b : ℝ,0 ≤ b → (b:EReal) < T → ∀ w,ContinuousOn (fun r => H (w,r)) (Icc 0 b))
    (c : ℕ → ℝ) (hc : ∀ n,0 ≤ c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal) < T)
    (hcc : ∀ t,t < ⊤ → ∃ n,t < realTimeClamp (T := T) (c n))
    (J : ClosedTime T → Ω → ℝ) (hJ : VariationIntegralFormula P c hc A H J) (a : ℝ) :
    ∃ I, AdaptedLocalVariationWitness F I ∧
      (∀ w t,t < ⊤ → ContinuousAt (fun s => I s w) t) ∧
      VariationIntegralFormula P c hc (fun t w => a*A t w) H I ∧
      (∀ᵐ w ∂P,∀ t,t < ⊤ → I t w = a*J t w) := by
  obtain ⟨U,V,W,hU,hV,hW,hUc,hVc,hWc,hu,hv,hw,he⟩ :=
    continuous_variation_associativity_constructed P F hF hnull c hc hcm hcT hcc A hA hAc
      H (fun _ => a) hHa (fun _ _ _ => measurable_const) hHc (fun _ _ _ _ => continuousOn_const)
  have hderiv : deriv (fun x : ℝ => a*x) = fun _ => a := by
    funext x
    simpa using ((hasDerivAt_id x).const_mul a).deriv
  have hchain := continuous_variation_chain_rule P hT F hF hle A U hA hAc
    (fun x => a*x) (contDiff_const.mul contDiff_id) c hc hcT hcc (by simpa [hderiv] using hu)
  have hscaled := variation_integrand_scalar P c hc A J H a hJ
  have hWJ := hw.unique P c hc hcc A W (fun t w => a*J t w) (fun z => H z*a)
    (by simpa only [mul_comm] using hscaled)
  refine ⟨V,hV,hVc,?_,?_⟩
  · apply variation_integral_integrator_increments_congr P U _ V H c hc hcT hv
    filter_upwards [hchain] with w hh
    intro s t hs ht
    linarith [hh s hs,hh t ht]
  · filter_upwards [he,hWJ] with w hh hj
    intro t ht
    exact (hh t ht).trans (hj t ht)

end Asakura.Chapter6
