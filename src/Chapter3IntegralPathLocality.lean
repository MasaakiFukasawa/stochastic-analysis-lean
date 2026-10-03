import Chapter3CommonOscillationPartition
import Chapter3SemimartingaleIntegralApproximation

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- On one common full-measure set, equality of the entire integrand and
integrator paths implies equality of the actual semimartingale integrals.
No measurability of the path-equality event is assumed. -/
theorem semimartingale_integral_path_locality
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M H Z : Bool → ClosedTime T → Ω → ℝ)
    (hX : ∀ i, SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hHm : ∀ i t, t < ⊤ → Measurable[F t] (H i t))
    (hHc : ∀ i ω t, t < ⊤ → ContinuousAt (fun s => H i s ω) t)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hZ : ∀ i, SemimartingaleIntegralFormula P F c hc (A i) (M i)
      (fun z => H i (realTimeClamp z.2) z.1) (Z i)) :
    ∀ᵐ ω ∂P,
      (∀ t, t < ⊤ → H false t ω = H true t ω) →
      (∀ t, t < ⊤ → X false t ω = X true t ω) →
      ∀ t, t < ⊤ → Z false t ω = Z true t ω := by
  obtain ⟨u,_,_,_,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  obtain ⟨τ,h0,hs,hm,ht,hco,_,hL⟩ := common_oscillation_partition P F hF hle H hHm hHc
    (fun n => realTimeClamp (u n)) hum.monotone hut huc
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : ClosedTime T))
  have hct k : realTimeClamp (T := T) (c k) < ⊤ := by
    change (realTimeClamp (c k) : EReal) < T
    rw [real_time_clamp_eq _ (hc k) (hcT k).le]
    exact hcT k
  have hl i k := semimartingale_integral_approximation P hT F hF hle hnull
    (X i) (A i) (M i) (H i) (Z i) (hX i) (hHm i) (hHc i)
    c hc hcT hcc (hZ i) τ hs hm ht h0 hco q (TopologicalSpace.denseRange_denseSeq _)
    (fun n j l => hL i n j (q l).val) _ (hct k)
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hl i))] with ω hω
  intro hH hXX t htop
  obtain ⟨k,hk⟩ := hcc t htop
  have hmin : min (realTimeClamp (c k)) t = t := min_eq_right hk.le
  have h0lim := (hω false k).tendsto_at t
  have h1lim := (hω true k).tendsto_at t
  simp only [hmin] at h0lim h1lim
  have he n : (∑' j, H false (τ n j ω) ω*
      (X false (min (τ n (j+1) ω) t) ω-X false (min (τ n j ω) t) ω)) =
      (∑' j, H true (τ n j ω) ω*
      (X true (min (τ n (j+1) ω) t) ω-X true (min (τ n j ω) t) ω)) := by
    apply tsum_congr
    intro j
    rw [hH _ (ht n j ω),hXX _ ((min_le_right _ _).trans_lt htop),
      hXX _ ((min_le_right _ _).trans_lt htop)]
  simp_rw [he] at h0lim
  exact tendsto_nhds_unique h0lim h1lim

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.semimartingale_integral_path_locality
