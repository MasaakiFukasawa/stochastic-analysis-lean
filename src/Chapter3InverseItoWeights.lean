import Chapter3IdentityItoIntegral
import Chapter2ItoAssociativityConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The inverse-weight step of BDG: both stochastic integrals are
constructed and their composition is the original local martingale. -/
theorem continuous_inverse_ito_weights_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (G H : Ω × ℝ → ℝ)
    (hGa : ∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun ω => G (ω,r)))
    (hHa : ∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun ω => H (ω,r)))
    (hGc : ∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∀ ω, ContinuousOn (fun r => G (ω,r)) (Icc 0 b))
    (hHc : ∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∀ ω, ContinuousOn (fun r => H (ω,r)) (Icc 0 b))
    (hprod : ∀ ω (r : ℝ), 0 ≤ r → (r:EReal) < T → H (ω,r)*G (ω,r) = 1) :
    ∃ Y Z : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Y ∧ LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X G Y ∧ ItoCovarianceFormula P F Y H Z ∧
      (∀ᵐ ω ∂P, ∀ t, t < ⊤ → Z t ω = X t ω) := by
  obtain ⟨Y,Z,W,hY,hZ,hW,hy,hz,hw,he⟩ := continuous_adapted_ito_associativity_constructed
    P hT F hF hle hnull X hX G H hGa hHa hGc hHc
  have hw' := hw.congr_on_time_domain P F X W (fun z => H z*G z) (fun _ => 1) hprod
  have hx := identity_ito_integral P hT F hF hle hnull X hX
  have heW := hw'.unique P hT F hF hle hnull X W X (fun _ => 1) hX hW hX hx
  refine ⟨Y,Z,hY,hZ,hy,hz,?_⟩
  filter_upwards [he,heW] with ω heω hwω
  intro t ht
  exact (heω t ht).trans (hwω t ht)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.continuous_inverse_ito_weights_constructed
