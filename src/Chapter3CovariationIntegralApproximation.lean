import Chapter3SemimartingaleCovariationApproximation
import Chapter2VariationIntegralFormula

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Identify the covariation limit with the finite-variation integral
already defined in Chapter 2, rather than a newly postulated integral. -/
theorem semimartingale_covariation_integral_approximation
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
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (I : ClosedTime T → Ω → ℝ)
    (hI : VariationIntegralFormula P c hc C (fun z => H (realTimeClamp z.2) z.1) I)
    (k : ℕ) :
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun n t => partitionCross (fun s => X s ω) (fun s => Y s ω) (fun s => H s ω)
        (fun j => τ n j ω) (min (realTimeClamp (c k)) t))
      (fun t => I (min (realTimeClamp (c k)) t) ω) atTop := by
  have hcore := semimartingale_covariation_approximation P hT F hF hle hnull
    X Y A B M N C H hX hY hC hHm hHc τ hτ hτmono hτtop hτ0 hcofinal
    q hq hbM hbN hbA hbB hbH (c k) (hc k) (hcT k)
  obtain ⟨ξ,hs,hξ,hi,hform⟩ := hI k
  filter_upwards [hcore,hξ,hform] with ω hω hξω hfω
  obtain ⟨hCv,hCr,hlim⟩ := hω
  have he : bvSigned ((fun r => C (realTimeClamp r) ω) ∘ intervalClamp 0 (c k) (hc k)) hCv hCr 0 = ξ ω := by
    apply signed_measure_ext_Ioc
    intro a b hab
    rw [bvSigned_Ioc _ _ _ _ _ _ hab.le,hξω a b hab.le]
    rfl
  change ∀ t, I (min (realTimeClamp (c k)) t) ω =
    signedIntegralRaw (ξ ω) ((Iic (finitePrefixTime (c k) (hc k) t).val).indicator (fun r => H (realTimeClamp r) ω)) at hfω
  simpa only [he,← hfω,partitionCross] using hlim

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.semimartingale_covariation_integral_approximation
