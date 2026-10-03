import Chapter3ProductFormula
import Chapter3ContinuousIntegralConstruction

open MeasureTheory Set
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The endpoint formula in the OU example uses the actual integral X dX,
constructed here from its variation and martingale parts. -/
theorem square_semimartingale_integral
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X A M C : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hC : LocalCovarianceWitness P F M M C)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n)) :
    ∃ I : ClosedTime T → Ω → ℝ,
      SemimartingaleIntegralFormula P F c hc A M (fun z => X (realTimeClamp z.2) z.1) I ∧
      ∀ᵐ w ∂P,∀ t,t<⊤ → I t w=((X t w)^2-(X ⊥ w)^2-C t w)/2 := by
  have ha t (ht : t<⊤) : Measurable[F t] (X t) := by
    have he : X t=fun w => A t w+M t w := funext (hX.decomposition t ht)
    rw [he]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)
  obtain ⟨I,J,hIJ,hI,hJ⟩ := continuous_semimartingale_integral_exists P hT F hF hle hnull
    X A M X hX ha hX.continuous c hc hcm hcT hcc
  have hK : SemimartingaleIntegralFormula P F c hc A M (fun z => X (realTimeClamp z.2) z.1) (fun t w => I t w+J t w) :=
    ⟨I,J,hIJ,hI,hJ⟩
  refine ⟨_,hK,?_⟩
  filter_upwards [semimartingale_product_formula P hT F hF hle hnull X X A A M M C
    (fun t w => I t w+J t w) (fun t w => I t w+J t w) hX hX hC c hc hcT hcc hK hK] with w hw
  intro t ht
  have hh := hw t ht
  nlinarith
end Asakura.Chapter8
