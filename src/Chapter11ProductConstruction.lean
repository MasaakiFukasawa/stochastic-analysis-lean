import Chapter6SemimartingaleWeight
import Chapter3ProductFormula

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter6
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Construct every integral in the product rule from continuous
 semimartingale factors. No product decomposition is assumed. -/
theorem semimartingale_product_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X Y A B M N C : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hY : SemimartingaleDecomposition P F Y B N)
    (hC : LocalCovarianceWitness P F M N C)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n)) :
    ∃ I J U V : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F U ∧ LocalMProcessWitness P F V ∧
      VariationIntegralFormula P c hc A (fun z => Y (realTimeClamp z.2) z.1) I ∧
      VariationIntegralFormula P c hc B (fun z => X (realTimeClamp z.2) z.1) J ∧
      ItoCovarianceFormula P F M (fun z => Y (realTimeClamp z.2) z.1) U ∧
      ItoCovarianceFormula P F N (fun z => X (realTimeClamp z.2) z.1) V ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → X t w*Y t w=X ⊥ w*Y ⊥ w+I t w+J t w+U t w+V t w+C t w) := by
  have hXa t (ht : t<⊤) : Measurable[F t] (X t) := by
    have he : X t=fun w => A t w+M t w := funext (hX.decomposition t ht)
    rw [he]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)
  have hYa t (ht : t<⊤) : Measurable[F t] (Y t) := by
    have he : Y t=fun w => B t w+N t w := funext (hY.decomposition t ht)
    rw [he]
    exact (hY.variation.adapted t ht).add (hY.martingale.adapted P F t ht)
  obtain ⟨I,U,hIU,hI,hU⟩ := continuous_semimartingale_integral_exists P hT F hF hle hnull
    X A M Y hX hYa hY.continuous c hc hcm hcT hcc
  obtain ⟨J,V,hJV,hJ,hV⟩ := continuous_semimartingale_integral_exists P hT F hF hle hnull
    Y B N X hY hXa hX.continuous c hc hcm hcT hcc
  have hp := semimartingale_product_formula P hT F hF hle hnull X Y A B M N C
    (fun t w => I t w+U t w) (fun t w => J t w+V t w) hX hY hC c hc hcT hcc
    ⟨I,U,hIU,hI,hU⟩ ⟨J,V,hJV,hJ,hV⟩
  refine ⟨I,J,U,V,hIU.martingale,hJV.martingale,hI,hJ,hU,hV,?_⟩
  filter_upwards [hp] with w hw
  intro t ht
  have he := hw t ht
  linarith

end Asakura.Chapter11
