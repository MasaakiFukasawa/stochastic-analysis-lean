import Chapter3ItoPrintedHypotheses
import Chapter3VariationIntegralApproximation
import Chapter3LinearApproximationSum
import Chapter2SemimartingaleAssociativity

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The semimartingale discrete-integral approximation, with both actual
component integrals and the manuscript's original dense-time L-infinity
partition condition. -/
theorem semimartingale_integral_approximation
    {Ω ι : Type*} [Countable ι] {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M H Z : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hZ : SemimartingaleIntegralFormula P F c hc A M (fun z => H (realTimeClamp z.2) z.1) Z)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτ : ∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t})
    (hτm : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτt : ∀ n j ω, τ n j ω < ⊤) (hτ0 : ∀ n ω, τ n 0 ω = ⊥)
    (hτc : ∀ n ω t, t < ⊤ → ∃ j, t < τ n j ω)
    (q : ι → Iio (⊤ : ClosedTime T)) (hq : DenseRange q)
    (hbH : ∀ n j i, eLpNorm (fun ω =>
      H (min (τ n (j+1) ω) (q i).val) ω-H (min (τ n j ω) (q i).val) ω) ∞ P ≤ ENNReal.ofReal ((1/2:ℝ)^n))
    (b : ClosedTime T) (hb : b < ⊤) :
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun n t => ∑' j, H (τ n j ω) ω*
        (X (min (τ n (j+1) ω) (min b t)) ω-X (min (τ n j ω) (min b t)) ω))
      (fun t => Z (min b t) ω) atTop := by
  obtain ⟨I,J,hZD,hI,hJ⟩ := hZ
  have hm := ito_approximation_from_essential_bounds P hT F hF hle hnull M H J
    hX.martingale hZD.martingale hJ hHm hHc τ hτ hτm hτt hτ0 hτc q hq hbH b hb
  have hh n j := stopped_dense_essential_bound P q hq H hHc (τ n j) (τ n (j+1))
    (fun ω => hτm n ω (Nat.le_succ j)) (hτt n (j+1)) ((1/2:ℝ)^n) (pow_nonneg (by norm_num) n) (hbH n j)
  have ho := stopped_bound_interval_oscillation P H τ (fun n => (1/2:ℝ)^n) hh
  obtain ⟨k,hk⟩ := hcc b hb
  have ha := variation_integral_approximation P F hF A H I hX.variation hHc c hc hcT hI
    τ hτm hτ0 hτc ho k
  filter_upwards [hm,ha] with ω hmω haω
  have hac := haω.comp (fun t => min b t)
  have hmin (t : ClosedTime T) : min (realTimeClamp (c k)) (min b t) = min b t :=
    min_eq_right ((min_le_left _ _).trans hk.le)
  simp only [Function.comp_def,hmin] at hac
  have hsum n t := linear_partition_sum_add (fun t => A t ω) (fun t => M t ω) (fun t => X t ω)
    (fun t => H t ω) (fun j => τ n j ω) (hτm n ω) b hb (hτc n ω)
    (fun s hs => hX.decomposition s (hs.trans_lt hb) ω) t
  have htarget t := hZD.decomposition (min b t) ((min_le_left _ _).trans_lt hb) ω
  simp_rw [hsum,htarget]
  exact uniform_limit_add _ _ _ _ hac hmω

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.semimartingale_integral_approximation
