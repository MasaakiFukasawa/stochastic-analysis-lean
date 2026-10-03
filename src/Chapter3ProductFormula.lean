import Chapter3PartitionProduct
import Chapter3UnweightedCovariationApproximation
import Chapter3CommonOscillationPartition
import Chapter3SemimartingaleIntegralApproximation

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The product specialization of Ito's formula, with both actual
semimartingale integrals and the actual covariance of the martingale parts. -/
theorem semimartingale_product_formula
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y A B M N C I J : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hY : SemimartingaleDecomposition P F Y B N)
    (hC : LocalCovarianceWitness P F M N C)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hI : SemimartingaleIntegralFormula P F c hc A M (fun z => Y (realTimeClamp z.2) z.1) I)
    (hJ : SemimartingaleIntegralFormula P F c hc B N (fun z => X (realTimeClamp z.2) z.1) J) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
      X t ω*Y t ω = X ⊥ ω*Y ⊥ ω+I t ω+J t ω+C t ω := by
  have hXm t (ht : t < ⊤) : Measurable[F t] (X t) := by
    have heq : X t = fun ω => A t ω+M t ω := funext (hX.decomposition t ht)
    rw [heq]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)
  have hYm t (ht : t < ⊤) : Measurable[F t] (Y t) := by
    have heq : Y t = fun ω => B t ω+N t ω := funext (hY.decomposition t ht)
    rw [heq]
    exact (hY.variation.adapted t ht).add (hY.martingale.adapted P F t ht)
  let V : Fin 6 → ClosedTime T → Ω → ℝ := ![A,B,M,N,X,Y]
  have hVm i t (ht : t < ⊤) : Measurable[F t] (V i t) := by
    fin_cases i
    · exact hX.variation.adapted t ht
    · exact hY.variation.adapted t ht
    · exact hX.martingale.adapted P F t ht
    · exact hY.martingale.adapted P F t ht
    · exact hXm t ht
    · exact hYm t ht
  have hVc i ω t (ht : t < ⊤) : ContinuousAt (fun s => V i s ω) t := by
    fin_cases i
    · exact hX.variation_continuous P F ω t ht
    · exact hY.variation_continuous P F ω t ht
    · exact hX.martingale.path P F ω t ht
    · exact hY.martingale.path P F ω t ht
    · exact hX.continuous ω t ht
    · exact hY.continuous ω t ht
  obtain ⟨u,_,_,_,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  obtain ⟨τ,h0,hs,hm,ht,hco,_,hL⟩ := common_oscillation_partition P F hF hle V hVm hVc
    (fun n => realTimeClamp (u n)) hum.monotone hut huc
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : ClosedTime T))
  have hq := TopologicalSpace.denseRange_denseSeq (Iio (⊤ : ClosedTime T))
  have hct k : realTimeClamp (T := T) (c k) < ⊤ := by
    change (realTimeClamp (c k) : EReal) < T
    rw [real_time_clamp_eq _ (hc k) (hcT k).le]
    exact hcT k
  have hli k := semimartingale_integral_approximation P hT F hF hle hnull X A M Y I hX
    hYm hY.continuous c hc hcT hcc hI τ hs hm ht h0 hco q hq (fun n j l => hL 5 n j (q l).val) _ (hct k)
  have hlj k := semimartingale_integral_approximation P hT F hF hle hnull Y B N X J hY
    hXm hX.continuous c hc hcT hcc hJ τ hs hm ht h0 hco q hq (fun n j l => hL 4 n j (q l).val) _ (hct k)
  have hlc k := unweighted_semimartingale_covariation_approximation P hT F hF hle hnull
    X Y A B M N C hX hY hC τ hs hm ht h0 hco q hq
    (fun n j l => hL 2 n j (q l).val) (fun n j l => hL 3 n j (q l).val)
    (fun n j l => hL 0 n j (q l).val) (fun n j l => hL 1 n j (q l).val) (c k) (hc k) (hcT k)
  have hc0 : ∀ᵐ ω ∂P, C ⊥ ω = 0 := by
    filter_upwards [hX.martingale.initial P F,hY.martingale.initial P F,hC.defect.initial P F]
      with ω hx hy hz
    change M ⊥ ω*N ⊥ ω-C ⊥ ω = 0 at hz
    rw [hx,hy] at hz
    simp only [Pi.zero_apply,zero_mul,zero_sub] at hz
    linarith
  filter_upwards [ae_all_iff.mpr hli,ae_all_iff.mpr hlj,ae_all_iff.mpr hlc,hc0]
    with ω hi hj hcv hz
  intro t htop
  obtain ⟨k,hk⟩ := hcc t htop
  have hmin : min (realTimeClamp (c k)) t = t := min_eq_right hk.le
  have hi' := (hi k).tendsto_at t
  have hj' := (hj k).tendsto_at t
  have hc' := (hcv k).tendsto_at t
  simp only [hmin,hz,sub_zero] at hi' hj' hc'
  have hl := (hi'.add hj').add hc'
  have he n : X t ω*Y t ω-X ⊥ ω*Y ⊥ ω =
      partitionLinear (fun s => X s ω) (fun s => Y s ω) (fun j => τ n j ω) t+
      partitionLinear (fun s => Y s ω) (fun s => X s ω) (fun j => τ n j ω) t+
      partitionCross (fun s => X s ω) (fun s => Y s ω) (fun _ => 1) (fun j => τ n j ω) t := by
    obtain ⟨L,hL⟩ := hco n ω t htop
    exact partition_product_identity (fun s => X s ω) (fun s => Y s ω) (fun j => τ n j ω) (hm n ω) (h0 n ω) t L hL.le
  change Tendsto (fun n =>
    partitionLinear (fun s => X s ω) (fun s => Y s ω) (fun j => τ n j ω) t+
    partitionLinear (fun s => Y s ω) (fun s => X s ω) (fun j => τ n j ω) t+
    partitionCross (fun s => X s ω) (fun s => Y s ω) (fun _ => 1) (fun j => τ n j ω) t)
    atTop (𝓝 (I t ω+J t ω+C t ω)) at hl
  simp_rw [← he] at hl
  have hid := tendsto_nhds_unique hl tendsto_const_nhds
  linarith

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.semimartingale_product_formula
