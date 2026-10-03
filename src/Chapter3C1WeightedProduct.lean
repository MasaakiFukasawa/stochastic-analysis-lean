import Chapter3VariationWeightProduct
import Chapter3VariationIntegratorCongruence
import Chapter3RegularizedWeightRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Derive X v(K) = v(K)·X + X v'(K)·K from actual integrals and the C¹ chain rule. -/
theorem C1_weighted_product_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X K : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hK : AdaptedLocalVariationWitness F K)
    (hKc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => K s ω) t)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v)
    (hV : AdaptedLocalVariationWitness F (fun t ω => v (K t ω)))
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n)) :
    ∃ Z L : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X (fun z => v (K (realTimeClamp z.2) z.1)) Z ∧
      AdaptedLocalVariationWitness F L ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => L s ω) t) ∧
      VariationIntegralFormula P c hc K
        (fun z => X (realTimeClamp z.2) z.1*deriv v (K (realTimeClamp z.2) z.1)) L ∧
      (∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω*v (K t ω) = Z t ω+L t ω) := by
  have hd := hv.continuous_deriv le_rfl
  have hVr := open_process_real_regularity F (fun t ω => v (K t ω))
    (fun t ht => hv.continuous.measurable.comp (hK.adapted t ht))
    (fun ω t ht => hv.continuous.continuousAt.comp (hKc ω t ht))
  have hDr := open_process_real_regularity F (fun t ω => deriv v (K t ω))
    (fun t ht => hd.measurable.comp (hK.adapted t ht))
    (fun ω t ht => hd.continuousAt.comp (hKc ω t ht))
  have hXr := open_process_real_regularity F X (hX.adapted P F) (hX.path P F)
  obtain ⟨Z,hZ,hz⟩ := continuous_adapted_ito_exists P hT F hF hle hnull X hX
    (fun z => v (K (realTimeClamp z.2) z.1)) hVr.1 hVr.2
  obtain ⟨J,I,L,hJ,hI,hL,hJc,hIc,hLc,hj,hi,hl,heIL⟩ :=
    continuous_variation_associativity_constructed P F hF hnull c hc hcm hcT hcc K hK hKc
      (fun z => X (realTimeClamp z.2) z.1) (fun z => deriv v (K (realTimeClamp z.2) z.1))
      hXr.1 hDr.1 hXr.2 hDr.2
  have hchain := continuous_variation_chain_rule P hT F hF hle K J hK hKc v hv c hc hcT hcc hj
  have hiV : VariationIntegralFormula P c hc (fun t ω => v (K t ω))
      (fun z => X (realTimeClamp z.2) z.1) I := by
    apply variation_integral_integrator_increments_congr P J (fun t ω => v (K t ω)) I _ c hc hcT hi
    filter_upwards [hchain] with ω hω
    intro s t hs ht
    linarith [hω s hs,hω t ht]
  have hprod := variation_weight_product_formula P hT F hF hle hnull X (fun t ω => v (K t ω)) Z I hX hV
    (fun ω t ht => hv.continuous.continuousAt.comp (hKc ω t ht)) hZ hz c hc hcT hcc hiV
  refine ⟨Z,L,hZ,hz,hL,hLc,hl,?_⟩
  filter_upwards [hprod,heIL] with ω hpω heω
  intro t ht
  rw [hpω t ht,heω t ht]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.C1_weighted_product_constructed
