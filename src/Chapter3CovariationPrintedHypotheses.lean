import Chapter3GeneralCovariationApproximation
import Chapter3PartitionEssentialBounds
import Chapter2ItoConstructionChoices

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Weighted covariation approximation directly from the printed dense-time
L-infinity conditions defining the three partition classes. -/
theorem covariation_approximation_from_essential_bounds
    {Ω ι : Type*} [Countable ι] {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y C H : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτ : ∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t})
    (hτmono : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτtop : ∀ n j ω, τ n j ω < ⊤) (hτ0 : ∀ n ω, τ n 0 ω = ⊥)
    (hcofinal : ∀ n ω b, b < ⊤ → ∃ N, b < τ n N ω)
    (q : ι → Iio (⊤ : ClosedTime T)) (hq : DenseRange q)
    (hbX : ∀ n j i, eLpNorm (fun ω =>
      X (min (τ n (j+1) ω) (q i).val) ω-X (min (τ n j ω) (q i).val) ω) ∞ P ≤ ENNReal.ofReal ((1/2:ℝ)^n))
    (hbY : ∀ n j i, eLpNorm (fun ω =>
      Y (min (τ n (j+1) ω) (q i).val) ω-Y (min (τ n j ω) (q i).val) ω) ∞ P ≤ ENNReal.ofReal ((1/2:ℝ)^n))
    (hbH : ∀ n j i, eLpNorm (fun ω =>
      H (min (τ n (j+1) ω) (q i).val) ω-H (min (τ n j ω) (q i).val) ω) ∞ P ≤ ENNReal.ofReal ((1/2:ℝ)^n))
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T) :
    ∀ᵐ ω ∂P,
      ∃ (hCv : BoundedVariationOn ((fun r => C (realTimeClamp r) ω) ∘ intervalClamp 0 d hd) univ)
        (hCr : ∀ x, ContinuousWithinAt ((fun r => C (realTimeClamp r) ω) ∘ intervalClamp 0 d hd) (Ici x) x),
      TendstoUniformly
        (fun n t => ∑' j, H (τ n j ω) ω*
          (X (min (τ n (j+1) ω) (min (realTimeClamp d) t)) ω-X (min (τ n j ω) (min (realTimeClamp d) t)) ω)*
          (Y (min (τ n (j+1) ω) (min (realTimeClamp d) t)) ω-Y (min (τ n j ω) (min (realTimeClamp d) t)) ω))
        (fun t => signedIntegralRaw
          (bvSigned ((fun r => C (realTimeClamp r) ω) ∘ intervalClamp 0 d hd) hCv hCr 0)
          ((Iic (finitePrefixTime d hd t).val).indicator (fun r => H (realTimeClamp r) ω))) atTop := by
  obtain ⟨c,_,_,_,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hx n j := stopped_dense_essential_bound P q hq X (hX.path P F)
    (τ n j) (τ n (j+1)) (fun ω => hτmono n ω (Nat.le_succ j)) (hτtop n (j+1))
    ((1/2:ℝ)^n) (pow_nonneg (by norm_num) n) (hbX n j)
  have hy n j := stopped_dense_essential_bound P q hq Y (hY.path P F)
    (τ n j) (τ n (j+1)) (fun ω => hτmono n ω (Nat.le_succ j)) (hτtop n (j+1))
    ((1/2:ℝ)^n) (pow_nonneg (by norm_num) n) (hbY n j)
  have hh n j := stopped_dense_essential_bound P q hq H hHc
    (τ n j) (τ n (j+1)) (fun ω => hτmono n ω (Nat.le_succ j)) (hτtop n (j+1))
    ((1/2:ℝ)^n) (pow_nonneg (by norm_num) n) (hbH n j)
  exact general_covariation_approximation P F hF hle hnull X Y C H hX hY hC hHm hHc
    (fun j => realTimeClamp (c j)) hct.monotone hcut hcc τ hτ hτmono hτtop hτ0 hcofinal hx hy
    (stopped_bound_interval_oscillation P H τ (fun n => (1/2:ℝ)^n) hh) d hd hdT

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.covariation_approximation_from_essential_bounds
