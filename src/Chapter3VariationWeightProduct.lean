import Chapter3VariationCrossConvergence
import Chapter3PartitionProduct
import Chapter3ItoPrintedHypotheses
import Chapter3IncreasingIntegralBound
import Chapter3WrittenBDG

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Integration by parts against an arbitrary continuous finite-variation weight. -/
theorem variation_weight_product_formula
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X V Z I : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hV : AdaptedLocalVariationWitness F V)
    (hVc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => V s ω) t)
    (hZ : LocalMProcessWitness P F Z)
    (hZI : ItoCovarianceFormula P F X (fun z => V (realTimeClamp z.2) z.1) Z)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hI : VariationIntegralFormula P c hc V (fun z => X (realTimeClamp z.2) z.1) I) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω*V t ω = Z t ω+I t ω := by
  let U : Bool → ClosedTime T → Ω → ℝ := fun i => if i then V else X
  have hUm i t (ht : t < ⊤) : Measurable[F t] (U i t) := by
    cases i
    · exact hX.adapted P F t ht
    · exact hV.adapted t ht
  have hUc i ω t (ht : t < ⊤) : ContinuousAt (fun s => U i s ω) t := by
    cases i
    · exact hX.path P F ω t ht
    · exact hVc ω t ht
  obtain ⟨u,_,_,_,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  obtain ⟨τ,h0,hs,hm,ht,hco,hb,hL⟩ := common_oscillation_partition P F hF hle U hUm hUc
    (fun n => realTimeClamp (u n)) hum.monotone hut huc
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : ClosedTime T))
  have hct k : realTimeClamp (T := T) (c k) < ⊤ := by
    change (realTimeClamp (c k) : EReal) < T
    rw [real_time_clamp_eq _ (hc k) (hcT k).le]
    exact hcT k
  have hlz k := ito_approximation_from_essential_bounds P hT F hF hle hnull X V Z hX hZ hZI
    hV.adapted hVc τ hs hm ht h0 hco q (TopologicalSpace.denseRange_denseSeq _)
    (fun n j l => hL true n j (q l).val) _ (hct k)
  have ho := stopped_bound_interval_oscillation P X τ (fun n => (1/2:ℝ)^n)
    (fun n j => Filter.Eventually.of_forall (fun ω t => hb false n j ω t))
  have hli k := variation_integral_approximation P F hF V X I hV (hX.path P F) c hc hcT hI
    τ hm h0 hco ho k
  have hlq k := variation_cross_sum_uniform_zero P F V X (fun _ _ => 1) hV.toPathwise
    (fun _ _ _ => continuousAt_const) τ hm hco
    (fun n j => Filter.Eventually.of_forall (fun ω t => hb false n j ω t)) _ (hct k)
  filter_upwards [ae_all_iff.mpr hlz,ae_all_iff.mpr hli,ae_all_iff.mpr hlq,hX.initial P F]
    with ω hz hi hq hx0
  have hprod t (htop : t < ⊤) : X t ω*V t ω = Z t ω+I t ω := by
    obtain ⟨k,hk⟩ := hcc t htop
    have hmin : min (realTimeClamp (c k)) t = t := min_eq_right hk.le
    have hz' := (hz k).tendsto_at t
    have hi' := (hi k).tendsto_at t
    have hq' := (hq k).tendsto_at t
    simp only [hmin] at hz' hi' hq'
    have he n : V t ω*X t ω-V ⊥ ω*X ⊥ ω =
        partitionLinear (fun s => V s ω) (fun s => X s ω) (fun j => τ n j ω) t+
        partitionLinear (fun s => X s ω) (fun s => V s ω) (fun j => τ n j ω) t+
        partitionCross (fun s => V s ω) (fun s => X s ω) (fun _ => 1) (fun j => τ n j ω) t := by
      obtain ⟨N,hN⟩ := hco n ω t htop
      exact partition_product_identity (fun s => V s ω) (fun s => X s ω)
        (fun j => τ n j ω) (hm n ω) (h0 n ω) t N hN.le
    have hl := (hi'.add hz').add hq'
    change Tendsto (fun n => partitionLinear (fun s => V s ω) (fun s => X s ω) (fun j => τ n j ω) t+
      partitionLinear (fun s => X s ω) (fun s => V s ω) (fun j => τ n j ω) t+
      partitionCross (fun s => V s ω) (fun s => X s ω) (fun _ => 1) (fun j => τ n j ω) t)
      atTop (𝓝 (I t ω+Z t ω+0)) at hl
    simp_rw [← he] at hl
    have hid := tendsto_nhds_unique hl tendsto_const_nhds
    simp only [hx0,Pi.zero_apply,mul_zero,sub_zero,add_zero] at hid
    nlinarith
  exact hprod

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.variation_weight_product_formula
