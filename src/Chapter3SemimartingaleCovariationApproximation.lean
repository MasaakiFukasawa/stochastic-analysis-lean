import Chapter3CovariationPrintedHypotheses
import Chapter3VariationCrossConvergence
import Chapter3CrossSumAlgebra
import Chapter3LinearApproximationSum
import Chapter2SemimartingaleDecomposition

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Weighted semimartingale covariation approximation. The finite-variation
and mixed terms are actual partition sums and vanish uniformly, leaving
the constructed signed covariance integral of the martingale parts. -/
theorem semimartingale_covariation_approximation
    {Ω ι : Type*} [Countable ι] {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y A B M N C H : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hY : SemimartingaleDecomposition P F Y B N)
    (hC : LocalCovarianceWitness P F M N C)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτ : ∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t})
    (hτmono : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτtop : ∀ n j ω, τ n j ω < ⊤) (hτ0 : ∀ n ω, τ n 0 ω = ⊥)
    (hcofinal : ∀ n ω b, b < ⊤ → ∃ N, b < τ n N ω)
    (q : ι → Iio (⊤ : ClosedTime T)) (hq : DenseRange q)
    (hbM : ∀ n j i, eLpNorm (fun ω =>
      M (min (τ n (j+1) ω) (q i).val) ω-M (min (τ n j ω) (q i).val) ω) ∞ P ≤ ENNReal.ofReal ((1/2:ℝ)^n))
    (hbN : ∀ n j i, eLpNorm (fun ω =>
      N (min (τ n (j+1) ω) (q i).val) ω-N (min (τ n j ω) (q i).val) ω) ∞ P ≤ ENNReal.ofReal ((1/2:ℝ)^n))
    (hbA : ∀ n j i, eLpNorm (fun ω =>
      A (min (τ n (j+1) ω) (q i).val) ω-A (min (τ n j ω) (q i).val) ω) ∞ P ≤ ENNReal.ofReal ((1/2:ℝ)^n))
    (hbB : ∀ n j i, eLpNorm (fun ω =>
      B (min (τ n (j+1) ω) (q i).val) ω-B (min (τ n j ω) (q i).val) ω) ∞ P ≤ ENNReal.ofReal ((1/2:ℝ)^n))
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
  have hcore := covariation_approximation_from_essential_bounds P hT F hF hle hnull
    M N C H hX.martingale hY.martingale hC hHm hHc τ hτ hτmono hτtop hτ0 hcofinal
    q hq hbM hbN hbH d hd hdT
  have hbm n j := stopped_dense_essential_bound P q hq M (hX.martingale.path P F)
    (τ n j) (τ n (j+1)) (fun ω => hτmono n ω (Nat.le_succ j)) (hτtop n (j+1))
    ((1/2:ℝ)^n) (pow_nonneg (by norm_num) n) (hbM n j)
  have hbn n j := stopped_dense_essential_bound P q hq N (hY.martingale.path P F)
    (τ n j) (τ n (j+1)) (fun ω => hτmono n ω (Nat.le_succ j)) (hτtop n (j+1))
    ((1/2:ℝ)^n) (pow_nonneg (by norm_num) n) (hbN n j)
  have hbb n j := stopped_dense_essential_bound P q hq B (hY.variation_continuous P F)
    (τ n j) (τ n (j+1)) (fun ω => hτmono n ω (Nat.le_succ j)) (hτtop n (j+1))
    ((1/2:ℝ)^n) (pow_nonneg (by norm_num) n) (hbB n j)
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  have hAB := variation_cross_sum_uniform_zero P F A B H hX.variation.toPathwise hHc
    τ hτmono hcofinal hbb (realTimeClamp d) hdt
  have hAN := variation_cross_sum_uniform_zero P F A N H hX.variation.toPathwise hHc
    τ hτmono hcofinal hbn (realTimeClamp d) hdt
  have hBM := variation_cross_sum_uniform_zero P F B M H hY.variation.toPathwise hHc
    τ hτmono hcofinal hbm (realTimeClamp d) hdt
  filter_upwards [hcore,hAB,hAN,hBM] with ω hcω hab han hbm
  obtain ⟨hCv,hCr,hlim⟩ := hcω
  refine ⟨hCv,hCr,?_⟩
  have h := uniform_limit_add _ _ _ _
    (uniform_limit_add _ _ _ _ (uniform_limit_add _ _ _ _ hab han) hbm) hlim
  simp only [zero_add] at h
  convert h using 1
  funext n t
  exact partition_cross_decomposition (fun t => X t ω) (fun t => Y t ω) (fun t => A t ω)
    (fun t => B t ω) (fun t => M t ω) (fun t => N t ω) (fun t => H t ω)
    (fun j => τ n j ω) (hτmono n ω) (hcofinal n ω) (realTimeClamp d) hdt
    (fun s hs => hX.decomposition s (hs.trans_lt hdt) ω)
    (fun s hs => hY.decomposition s (hs.trans_lt hdt) ω) t

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.semimartingale_covariation_approximation
