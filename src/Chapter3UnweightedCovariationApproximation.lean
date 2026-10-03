import Chapter3SignedCumulativeIdentity

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem unweighted_semimartingale_covariation_approximation
    {Ω ι : Type*} [Countable ι] {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y A B M N C : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hY : SemimartingaleDecomposition P F Y B N)
    (hC : LocalCovarianceWitness P F M N C)
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
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T) :
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun n t => partitionCross (fun s => X s ω) (fun s => Y s ω) (fun _ => 1)
        (fun j => τ n j ω) (min (realTimeClamp d) t))
      (fun t => C (min (realTimeClamp d) t) ω-C ⊥ ω) atTop := by
  have h := semimartingale_covariation_approximation P hT F hF hle hnull
    X Y A B M N C (fun _ _ => 1) hX hY hC (fun _ _ => measurable_const)
    (fun _ _ _ => continuousAt_const) τ hτ hτmono hτtop hτ0 hcofinal
    q hq hbM hbN hbA hbB (fun _ _ _ => by simp) d hd hdT
  filter_upwards [h] with ω hω
  obtain ⟨hv,hr,hlim⟩ := hω
  have hz : realTimeClamp (T := T) 0 = ⊥ := by
    apply Subtype.ext
    exact real_time_clamp_eq 0 le_rfl (by simpa using hT.le)
  have he (t : ClosedTime T) : signedIntegralRaw
      (bvSigned ((fun r => C (realTimeClamp r) ω) ∘ intervalClamp 0 d hd) hv hr 0)
      ((Iic (finitePrefixTime d hd t).val).indicator (fun _ => 1)) =
      C (min (realTimeClamp d) t) ω-C ⊥ ω := by
    rw [signed_cumulative_interval_identity _ _ (bvSigned_Ioc _ _ _ _) _ _
      (finitePrefixTime d hd t).property.1]
    · dsimp only [Function.comp_def]
      rw [intervalClamp_eq 0 d hd (finitePrefixTime d hd t).property,
        finite_prefix_time_clamp d hd hdT.le,intervalClamp_eq 0 d hd (show (0:ℝ) ∈ Icc 0 d from ⟨le_rfl,hd⟩),hz]
    · intro a ha
      dsimp only [Function.comp_def,intervalClamp]
      rw [projIcc_of_le_left hd ha,projIcc_left]
  simpa only [he,partitionCross] using hlim

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.unweighted_semimartingale_covariation_approximation
