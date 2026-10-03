import Chapter11ProgressiveMeasureInvariance
import Chapter11ContinuousPrefixEquality
import Chapter11NoArbitrage

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- No arbitrage for the original-measure gains, obtained by constructing
 the common elementary approximation and then using the lower-bound argument. -/
theorem no_arbitrage_original_gains
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
    (V : ℝ → Ω → ℝ) (hVc : ∀ w,ContinuousOn (fun t => V t w) (Icc 0 (c j)))
    (a : ℝ) (hb : ∀ᵐ w ∂P,∀ t,t∈Icc 0 (c j) → -a≤V t w)
    (hn : 0≤ᵐ[P] V (c j)) :
    let β := fun w => (intervalStieltjes 0 (c j) (hc j).le (B w) (hB w) (fun r hr => (hBc w r hr).mono inter_subset_left)).measure
    (∀ᵐ w ∂P,(ν w).totalVariation≤β w) →
    (∀ᵐ w ∂P,Integrable (fun r => |H (w,r)|) (β w)) →
    (∀ᵐ w ∂P,∀ a b,a∈Icc 0 (c j) → b∈Icc 0 (c j) → a≤b →
      ν w (Ioc a b)=(Z (realTimeClamp b) w-Z (realTimeClamp a) w)-
        (X (realTimeClamp b) w-X (realTimeClamp a) w)) →
    (∀ t,t∈Icc 0 (c j) → V t=ᵐ[P] fun w => I (realTimeClamp t) w+signedCumulative (ν w) (fun r => H (w,r)) t) →
    V (c j)=ᵐ[P] 0 := by
  intro β hν hiB hinc hV
  have he t ht := progressive_integral_measure_invariant_prefix P Q hQP hT F hF hle hnullP hnullQ
    X A hX hA Z hZ hAQ c hc hcm hcT hct hcut hcc hAm hAc H hHm hH hi I K hI hK hII hKI
    j B hB hBc hBm hBa ν hν hiB hinc t ht
  have hKc w : ContinuousOn (fun t : ℝ => K (realTimeClamp t) w) (Icc 0 (c j)) := by
    intro t ht
    exact ((hK.path Q F w _ (lt_of_le_of_lt (real_time_clamp_mono ht.2) (hcut j))).comp real_time_clamp_continuous.continuousAt).continuousWithinAt
  have hall := continuous_prefix_equality Q (c j) (hc j).le V (fun t => K (realTimeClamp t)) hVc hKc
    (fun t ht => by
      filter_upwards [hQP.ae_le (hV t ht),he t ht] with w hw hk
      exact hw.trans hk)
  have hbound : ∀ᵐ w ∂Q,∀ t,t≤realTimeClamp (T:=T) (c j) → -a≤K t w := by
    filter_upwards [hall,hQP.ae_le hb] with w he hb
    intro t ht
    obtain ⟨r,hr,hrT,rfl⟩ := finite_closed_time_real t (ht.trans_lt (hcut j))
    have hrj : r≤c j := by
      have hh : (realTimeClamp (T:=T) r:EReal)≤(realTimeClamp (c j):EReal) := ht
      rw [real_time_clamp_eq r hr hrT.le,real_time_clamp_eq (c j) (hc j).le (hcT j).le] at hh
      exact EReal.coe_le_coe_iff.mp hh
    rw [←he r ⟨hr,hrj⟩]
    exact hb r ⟨hr,hrj⟩
  have hnQ : 0≤ᵐ[Q] K (realTimeClamp (c j)) := by
    filter_upwards [hall,hQP.ae_le hn] with w he hn
    rw [←he (c j) ⟨(hc j).le,le_rfl⟩]
    exact hn
  have hz := no_arbitrage_actual_local_wealth P Q hPQ F hF hle K hK (realTimeClamp (c j)) (hcut j) a hbound hnQ
  filter_upwards [hPQ.ae_le hall,hz] with w he hz
  exact (he (c j) ⟨(hc j).le,le_rfl⟩).trans hz

end Asakura.Chapter11
