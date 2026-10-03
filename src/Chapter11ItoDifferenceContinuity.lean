import Chapter11ItoSequenceContinuity
import Chapter2LenglartConvergence

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem ito_difference_probability_at_time
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (J : ℕ → Ω × ℝ → ℝ) (H : Ω × ℝ → ℝ)
    (hJ : ∀ k n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => (J k (z.1,z.2.val)-H (z.1,z.2.val))))
    (hi : ∀ k n, ∀ᵐ ω ∂P, Integrable (fun r => (J k (ω,r)-H (ω,r))^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure)
    (Y : ℕ → ClosedTime T → Ω → ℝ) (I : ClosedTime T → Ω → ℝ)
    (hY : ∀ k,LocalMProcessWitness P F (Y k)) (hI : LocalMProcessWitness P F I)
    (hYI : ∀ k,ItoCovarianceFormula P F X (J k) (Y k))
    (hII : ItoCovarianceFormula P F X H I)
    (j : ℕ) (d : ℝ) (hd : 0≤d) (hdj : d≤c j)
    (hAdm : ∀ w,MonotoneOn (fun r => A (realTimeClamp r) w) (Icc 0 d))
    (hAdc : ∀ w,ContinuousOn (fun r => A (realTimeClamp r) w) (Icc 0 d))
    (hp : ∀ ε>0,Tendsto (fun k => P {w | ε≤∫ r,(J k (w,r)-H (w,r))^2
      ∂(intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) w) (hAdm w) (fun r hr => (hAdc w r hr).mono inter_subset_left)).measure}) atTop (𝓝 0)) :
    ∀ t,t≤realTimeClamp d → ∀ ε>0,Tendsto (fun k => P {w | ε≤|Y k t w-I t w|}) atTop (𝓝 0) := by
  have hDI k : ItoCovarianceFormula P F X (fun z => J k z-H z) (fun t w => Y k t w-I t w) := by
    have hh := hII.add_smul P F hF hle X I (Y k) H (J k) (hYI k) (-1)
    convert hh using 1 <;> funext <;> ring
  exact ito_sequence_probability_at_time P hT F hF hle hnull X A hX hA
    c hc hcm hcT hct hcut hcc hAm hAc (fun k z => J k z-H z) hJ hi
    (fun k t w => Y k t w-I t w) (fun k => by
      have hh := (hY k).add P F hF hle (hI.smul P F (-1))
      simpa only [neg_one_mul,sub_eq_add_neg] using hh) hDI j d hd hdj hAdm hAdc hp

end Asakura.Chapter11
