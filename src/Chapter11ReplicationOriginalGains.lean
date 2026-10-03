import Chapter11ProgressiveMeasureInvariance
import Chapter11ReplicationStockIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The representation strategy gives the same discounted gains under the
 original measure. Together with the proved reverse discount identity this
 is the original stock-and-bank self-financing equation. -/
theorem replication_original_discounted_gains
    {Ω : Type*} {m : MeasurableSpace Ω} (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQP : Q ≪ P)
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnullP : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (hnullQ : ∀ t E,MeasurableSet[m] E → Q E=0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (Z : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness Q F Z)
    (hAQ : LocalCovarianceWitness Q F Z Z A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (H : Ω × ℝ → ℝ) (hHm : Measurable H)
    (hH : ∀ d : ℝ,@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val)))
    (hi : ∀ n,∀ᵐ w ∂P,Integrable (fun r => H (w,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) w) (hAm n w)
        (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure)
    (I K : ClosedTime T → Ω → ℝ) (hI : LocalMProcessWitness P F I) (hK : LocalMProcessWitness Q F K)
    (hII : ItoCovarianceFormula P F X H I) (hKI : ItoCovarianceFormula Q F Z H K)
    (j : ℕ) (B : Ω → ℝ → ℝ)
    (hB : ∀ w,MonotoneOn (B w) (Icc 0 (c j)))
    (hBc : ∀ w,ContinuousOn (B w) (Icc 0 (c j)))
    (hBm : ∀ t,Measurable (fun w => B w t))
    (hBa : ∀ t : Icc (0:ℝ) (c j),Measurable[F (realTimeClamp t.val)] (fun w => B w t.val))
    (ν : Ω → SignedMeasure ℝ) (hPQ : P ≪ Q)
    (W M : ClosedTime T → Ω → ℝ) (Sd φ : Ω × ℝ → ℝ) (σ : ℝ) (hσ : σ≠0)
    (hSd : ∀ z,Sd z≠0) (hSdm : ∀ w,Measurable (fun r => Sd (w,r)))
    (hφm : ∀ w,Measurable (fun r => φ (w,r)))
    (hW : LocalMProcessWitness Q F W) (hM : LocalMProcessWitness Q F M)
    (hZI : ItoCovarianceFormula Q F W (fun z => σ*Sd z) Z)
    (hMI : ItoCovarianceFormula Q F W φ M)
    (hhold : H=fun z => φ z/(σ*Sd z)) :
    let β := fun w => (intervalStieltjes 0 (c j) (hc j).le (B w) (hB w) (fun r hr => (hBc w r hr).mono inter_subset_left)).measure
    (∀ᵐ w ∂P,(ν w).totalVariation≤β w) →
    (∀ᵐ w ∂P,Integrable (fun r => |H (w,r)|) (β w)) →
    (∀ᵐ w ∂P,∀ a b,a∈Icc 0 (c j) → b∈Icc 0 (c j) → a≤b →
      ν w (Ioc a b)=(Z (realTimeClamp b) w-Z (realTimeClamp a) w)-
        (X (realTimeClamp b) w-X (realTimeClamp a) w)) →
    ∀ t,t∈Icc 0 (c j) →
      (fun w => I (realTimeClamp t) w+signedCumulative (ν w) (fun r => H (w,r)) t)=ᵐ[P] M (realTimeClamp t) := by
  intro β hν hiB hinc t ht
  have hKI' := hKI
  rw [hhold] at hKI'
  have hKM := replication_stock_integral Q hT F hF hle hnullQ W Z M K Sd φ σ hσ hSd hSdm hφm
    hW hZ hM hK hZI hMI hKI'
  have he := progressive_integral_measure_invariant_prefix P Q hQP hT F hF hle hnullP hnullQ
    X A hX hA Z hZ hAQ c hc hcm hcT hct hcut hcc hAm hAc H hHm hH hi I K hI hK hII hKI
    j B hB hBc hBm hBa ν hν hiB hinc t ht
  filter_upwards [hPQ.ae_le he,hPQ.ae_le hKM] with w he hkm
  exact he.trans (hkm _ (lt_of_le_of_lt (real_time_clamp_mono ht.2) (hcut j)))

end Asakura.Chapter11
