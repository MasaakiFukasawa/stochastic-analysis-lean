import Chapter6SemimartingaleWeight
import Chapter5ZeroIto
import Chapter6FiniteTimeDensity
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The discount product rule with the actual stochastic integral exposed.
The finite-variation weight can have a merely integrable time density. -/
theorem discount_product_with_variation {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (Y A M D : ClosedTime T → Ω → ℝ) (hY : SemimartingaleDecomposition P F Y A M)
    (hD : AdaptedLocalVariationWitness F D)
    (hDc : ∀ w t,t<⊤ → ContinuousAt (fun s => D s w) t)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n)) :
    ∃ I J N, SemimartingaleDecomposition P F (fun t w => I t w+N t w) I N ∧
      AdaptedLocalVariationWitness F J ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => J s w) t) ∧
      VariationIntegralFormula P c hc A (fun z => D (realTimeClamp z.2) z.1) I ∧
      VariationIntegralFormula P c hc D (fun z => Y (realTimeClamp z.2) z.1) J ∧
      ItoCovarianceFormula P F M (fun z => D (realTimeClamp z.2) z.1) N ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → Y t w*D t w=Y ⊥ w*D ⊥ w+I t w+J t w+N t w) := by
  have hzero := zero_local_process P hT F
  have hDD : SemimartingaleDecomposition P F D D (fun _ _ => 0) :=
    ⟨hD,hzero,hDc,fun _ _ _ => (add_zero _).symm⟩
  have hYa t (ht : t<⊤) : Measurable[F t] (Y t) := by
    have he : Y t=(fun w => A t w+M t w) := funext (hY.decomposition t ht)
    rw [he]
    exact (hY.variation.adapted t ht).add (hY.martingale.adapted P F t ht)
  obtain ⟨I,N,hIN,hI,hN⟩ := continuous_semimartingale_integral_exists P hT F hF hle hnull
    Y A M D hY hD.adapted hDc c hc hcm hcT hcc
  obtain ⟨J,W,hJW,hJ,hW⟩ := continuous_semimartingale_integral_exists P hT F hF hle hnull
    D D (fun _ _ => 0) Y hDD hYa hY.continuous c hc hcm hcT hcc
  have hW0 := integral_against_zero_martingale P hT F hF hle hnull W _ hJW.martingale hW
  have hC : LocalCovarianceWitness P F M (fun _ _ => 0) (fun _ _ => 0) := by
    refine ⟨?_,?_⟩
    · simpa only [mul_zero,sub_zero] using hzero
    · simpa only [zero_mul] using hD.toPathwise.smul F 0
  have hp := semimartingale_product_formula P hT F hF hle hnull Y D A D M (fun _ _ => 0)
    (fun _ _ => 0) (fun t w => I t w+N t w) (fun t w => J t w+W t w)
    hY hDD hC c hc hcT hcc ⟨I,N,hIN,hI,hN⟩ ⟨J,W,hJW,hJ,hW⟩
  refine ⟨I,J,N,hIN,hJW.variation,hJW.variation_continuous P F,hI,hJ,hN,?_⟩
  filter_upwards [hp,hW0] with w hw hw0
  intro t ht
  have he := hw t ht
  rw [hw0 t ht] at he
  linarith


end Asakura.Chapter12
#print axioms Asakura.Chapter12.discount_product_with_variation
