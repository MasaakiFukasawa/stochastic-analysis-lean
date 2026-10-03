import Chapter3SemimartingaleFiniteSums
import Chapter3RegularizedWeightRegularity
import Chapter2SemimartingaleAssociativity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Upgrade the covariance's pathwise variation witness to the manuscript's
adapted Jordan decomposition, using its already proved stopped continuity. -/
theorem covariance_adapted_variation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    {X Y C : ClosedTime T → Ω → ℝ}
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C) : AdaptedLocalVariationWitness F C := by
  obtain ⟨τ,hs,hm,ht,hco,hv⟩ := hC.variation.localizers
  refine ⟨τ,hs,hm,ht,hco,?_⟩
  intro n
  obtain ⟨ha,hc⟩ := hC.stopped_regular P F hF hle hX hY (τ n) (hs n) (ht n)
  have hb ω : BoundedVariationOn (fun t => C (min (τ n ω) t) ω) univ := by
    obtain ⟨U,V,hU,hV,he⟩ := hv n ω
    simpa only [he] using increasing_difference_boundedVariation U V hU hV
  obtain ⟨U,V,hUa,hVa,hUc,hVc,hUm,hVm,he⟩ := adapted_continuous_jordan_decomposition F hF _ ha hc hb
  exact ⟨U,V,fun t => ⟨hUa t,hVa t⟩,fun ω => ⟨hUm ω,hVm ω⟩,
    fun ω t => ⟨(hUc ω).continuousAt.continuousWithinAt,(hVc ω).continuousAt.continuousWithinAt⟩,he⟩

/-- Construct a continuous adapted semimartingale integral by constructing
its variation and local-martingale components separately. -/
theorem continuous_semimartingale_integral_exists
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M H : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (ha : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hcont : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n)) :
    ∃ I J, SemimartingaleDecomposition P F (fun t ω => I t ω+J t ω) I J ∧
      VariationIntegralFormula P c hc A (fun z => H (realTimeClamp z.2) z.1) I ∧
      ItoCovarianceFormula P F M (fun z => H (realTimeClamp z.2) z.1) J := by
  obtain ⟨hra,hrc⟩ := open_process_real_regularity F H ha hcont
  obtain ⟨I,hI,hIc,hIf⟩ := continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc
    A hX.variation (hX.variation_continuous P F) (fun z => H (realTimeClamp z.2) z.1) hra hrc
  obtain ⟨J,hJ,hJf⟩ := continuous_adapted_ito_exists P hT F hF hle hnull M hX.martingale
    (fun z => H (realTimeClamp z.2) z.1) hra hrc
  exact ⟨I,J,⟨hI,hJ,fun ω t ht => (hIc ω t ht).add (hJ.path P F ω t ht),fun _ _ _ => rfl⟩,hIf,hJf⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.covariance_adapted_variation
#print axioms Asakura.Chapter3Complete.continuous_semimartingale_integral_exists
