import Chapter2ContinuousVariationIntegral
import Chapter2VariationAssociativityProgressive
import Chapter2ContinuousSignedAssociativity
import Chapter2ContinuousIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem continuous_adapted_variation_exists
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (A : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (H : Ω × ℝ → ℝ)
    (ha : ∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun ω => H (ω,r)))
    (hcont : ∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∀ ω, ContinuousOn (fun r => H (ω,r)) (Icc 0 b)) :
    ∃ I : ClosedTime T → Ω → ℝ, AdaptedLocalVariationWitness F I ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => I s ω) t) ∧
      VariationIntegralFormula P c hc A H I := by
  obtain ⟨κ,hκ,hs,_,hconstruct⟩ := continuous_local_variation_integral_constructed
    P F hF hnull c hc hcm hcT hcc A hA hAc
  letI : ∀ n ω, IsFiniteMeasure (κ n ω) := hκ
  have hp n := continuous_adapted_real_progressive F hF H (c n) (hc n)
    (fun r hr => ha r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) (hcont (c n) (hc n) (hcT n))
  have hi n : ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (κ n ω) := .of_forall (fun ω =>
    continuous_integrable_compact_support (κ n ω) 0 (c n) _ (hcont (c n) (hc n) (hcT n) ω)
      ((hs n ω).mono (fun r hr => ⟨hr.1.le,hr.2⟩)))
  obtain ⟨ξ,I,hI,hIc,hξ,hdom,he⟩ := hconstruct H hp hi
  exact ⟨I,hI,hIc,variation_integral_formula_of_construction P c hc A I H κ ξ hs hξ hdom hi he⟩

/-- For continuous adapted H and G, all three finite-variation integrals
exist under the original assumptions, and their associativity follows
from the actual signed-measure density calculation. -/
theorem continuous_variation_associativity_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (A : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (H G : Ω × ℝ → ℝ)
    (hHa : ∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun ω => H (ω,r)))
    (hGa : ∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun ω => G (ω,r)))
    (hHc : ∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∀ ω, ContinuousOn (fun r => H (ω,r)) (Icc 0 b))
    (hGc : ∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∀ ω, ContinuousOn (fun r => G (ω,r)) (Icc 0 b)) :
    ∃ J K L : ClosedTime T → Ω → ℝ,
      AdaptedLocalVariationWitness F J ∧ AdaptedLocalVariationWitness F K ∧ AdaptedLocalVariationWitness F L ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => J s ω) t) ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => K s ω) t) ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => L s ω) t) ∧
      VariationIntegralFormula P c hc A G J ∧ VariationIntegralFormula P c hc J H K ∧
      VariationIntegralFormula P c hc A (fun z => H z*G z) L ∧
      (∀ᵐ ω ∂P, ∀ t, t < ⊤ → K t ω = L t ω) := by
  obtain ⟨J,hJ,hJc,hJform⟩ := continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc
    A hA hAc G hGa hGc
  obtain ⟨K,hK,hKc,hKform⟩ := continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc
    J hJ hJc H hHa hHc
  obtain ⟨L,hL,hLc,hLform⟩ := continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc
    A hA hAc (fun z => H z*G z) (fun r hr hrT => (hHa r hr hrT).mul (hGa r hr hrT))
    (fun b hb hbT ω => (hHc b hb hbT ω).mul (hGc b hb hbT ω))
  refine ⟨J,K,L,hJ,hK,hL,hJc,hKc,hLc,hJform,hKform,hLform,?_⟩
  apply variation_integral_associativity_progressive P F c hc hcT hcc A J K L H G _ _ hJform hKform hLform
  · intro n
    exact continuous_adapted_real_progressive F hF H (c n) (hc n)
      (fun r hr => hHa r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) (hHc (c n) (hc n) (hcT n))
  · intro n
    exact continuous_adapted_real_progressive F hF G (c n) (hc n)
      (fun r hr => hGa r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) (hGc (c n) (hc n) (hcT n))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_variation_associativity_constructed
