import Chapter2ContinuousIntegrand
import Chapter2ItoAssociativity
import Chapter2ItoIntegrandEncoding

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- All three integrals in the associativity exercise are constructed
from continuous adapted integrands. Local square-energy membership and a measurable encoding beyond the time domain
are both constructed from continuity, not imposed as extra assumptions. -/
theorem continuous_adapted_ito_associativity_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (G H : Ω × ℝ → ℝ)
    (hGa : ∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun ω => G (ω,r)))
    (hHa : ∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun ω => H (ω,r)))
    (hGc : ∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∀ ω, ContinuousOn (fun r => G (ω,r)) (Icc 0 b))
    (hHc : ∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∀ ω, ContinuousOn (fun r => H (ω,r)) (Icc 0 b)) :
    ∃ Y Z W : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Y ∧ LocalMProcessWitness P F Z ∧ LocalMProcessWitness P F W ∧
      ItoCovarianceFormula P F X G Y ∧ ItoCovarianceFormula P F Y H Z ∧
      ItoCovarianceFormula P F X (fun z => H z*G z) W ∧
      (∀ᵐ ω ∂P, ∀ t, t < ⊤ → Z t ω = W t ω) := by
  obtain ⟨Y,hY,hy⟩ := continuous_adapted_ito_exists P hT F hF hle hnull X hX G hGa hGc
  obtain ⟨Z,hZ,hz⟩ := continuous_adapted_ito_exists P hT F hF hle hnull Y hY H hHa hHc
  obtain ⟨W,hW,hw⟩ := continuous_adapted_ito_exists P hT F hF hle hnull X hX (fun z => H z*G z)
    (fun r hr hrT => (hHa r hr hrT).mul (hGa r hr hrT))
    (fun b hb hbT ω => (hHc b hb hbT ω).mul (hGc b hb hbT ω))
  obtain ⟨G',hGm,hGe⟩ := continuous_local_measurable_encoding hT G hGc
  obtain ⟨H',hHm,hHe⟩ := continuous_local_measurable_encoding hT H hHc
  have hy' := hy.congr_on_time_domain P F X Y G G' (fun ω r hr hrT => (hGe ω r hr hrT).symm)
  have hz' := hz.congr_on_time_domain P F Y Z H H' (fun ω r hr hrT => (hHe ω r hr hrT).symm)
  have hw' := hw.congr_on_time_domain P F X W (fun z => H z*G z) (fun z => H' z*G' z)
    (fun ω r hr hrT => by rw [hGe ω r hr hrT,hHe ω r hr hrT])
  exact ⟨Y,Z,W,hY,hZ,hW,hy,hz,hw,ito_integral_associativity P hT F hF hle hnull
    X Y Z W G' H' hX hY hZ hW hGm hHm hy' hz' hw'⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_adapted_ito_associativity_constructed
