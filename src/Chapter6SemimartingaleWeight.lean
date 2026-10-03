import Chapter3ProductFormula
import Chapter3ContinuousIntegralConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Integration by parts with an adapted continuous finite-variation
weight; both variation integrals and the local martingale are constructed. -/
theorem semimartingale_weight_constructed {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (Y A M V : ClosedTime T → Ω → ℝ) (hY : SemimartingaleDecomposition P F Y A M)
    (hV : AdaptedLocalVariationWitness F V)
    (hVc : ∀ w t,t<⊤ → ContinuousAt (fun s => V s w) t)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n)) :
    ∃ I J N,LocalMProcessWitness P F N ∧
      VariationIntegralFormula P c hc A (fun z => V (realTimeClamp z.2) z.1) I ∧
      VariationIntegralFormula P c hc V (fun z => Y (realTimeClamp z.2) z.1) J ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → Y t w*V t w=Y ⊥ w*V ⊥ w+I t w+J t w+N t w) := by
  have hzero := zero_local_process P hT F
  have hVD : SemimartingaleDecomposition P F V V (fun _ _ => 0) :=
    ⟨hV,hzero,hVc,fun _ _ _ => (add_zero _).symm⟩
  have hYa t (ht : t<⊤) : Measurable[F t] (Y t) := by
    have he : Y t=(fun w => A t w+M t w) := funext (hY.decomposition t ht)
    rw [he]
    exact (hY.variation.adapted t ht).add (hY.martingale.adapted P F t ht)
  obtain ⟨I,U,hIU,hI,hU⟩ := continuous_semimartingale_integral_exists P hT F hF hle hnull
    Y A M V hY hV.adapted hVc c hc hcm hcT hcc
  obtain ⟨J,W,hJW,hJ,hW⟩ := continuous_semimartingale_integral_exists P hT F hF hle hnull
    V V (fun _ _ => 0) Y hVD hYa hY.continuous c hc hcm hcT hcc
  have hC : LocalCovarianceWitness P F M (fun _ _ => 0) (fun _ _ => 0) := by
    refine ⟨?_,?_⟩
    · simpa only [mul_zero,sub_zero] using hzero
    · simpa only [zero_mul] using hV.toPathwise.smul F 0
  have hp := semimartingale_product_formula P hT F hF hle hnull Y V A V M (fun _ _ => 0)
    (fun _ _ => 0) (fun t w => I t w+U t w) (fun t w => J t w+W t w)
    hY hVD hC c hc hcT hcc ⟨I,U,hIU,hI,hU⟩ ⟨J,W,hJW,hJ,hW⟩
  refine ⟨I,J,(fun t w => U t w+W t w),hIU.martingale.add P F hF hle hJW.martingale,hI,hJ,?_⟩
  filter_upwards [hp] with w hw
  intro t ht
  have he := hw t ht
  linarith

end Asakura.Chapter6
