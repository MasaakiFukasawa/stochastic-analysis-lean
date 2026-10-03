import Chapter11ItoAllTimeEnergy
import Chapter2LenglartConvergence

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem ito_sequence_probability_at_time
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
    (H : ℕ → Ω × ℝ → ℝ)
    (hH : ∀ k n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H k (z.1,z.2.val)))
    (hi : ∀ k n, ∀ᵐ ω ∂P, Integrable (fun r => H k (ω,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure)
    (Y : ℕ → ClosedTime T → Ω → ℝ) (hY : ∀ k,LocalMProcessWitness P F (Y k))
    (hYI : ∀ k,ItoCovarianceFormula P F X (H k) (Y k))
    (j : ℕ) (d : ℝ) (hd : 0≤d) (hdj : d≤c j)
    (hAdm : ∀ w,MonotoneOn (fun r => A (realTimeClamp r) w) (Icc 0 d))
    (hAdc : ∀ w,ContinuousOn (fun r => A (realTimeClamp r) w) (Icc 0 d))
    (hp : ∀ ε>0,Tendsto (fun k => P {w | ε≤∫ r,H k (w,r)^2
      ∂(intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) w) (hAdm w) (fun r hr => (hAdc w r hr).mono inter_subset_left)).measure}) atTop (𝓝 0)) :
    ∀ t,t≤realTimeClamp d → ∀ ε>0,Tendsto (fun k => P {w | ε≤|Y k t w|}) atTop (𝓝 0) := by
  choose C hC hCe using fun k => ito_covariance_formula_all_time_energy P hT F hF hle hnull X A hX hA
    c hc hcm hcT hct hcut hcc hAm hAc (H k) (hH k) (hi k) (Y k) (hY k) (hYI k)
  have hdT : (d:EReal)<T := (EReal.coe_le_coe hdj).trans_lt (hcT j)
  have hdt : realTimeClamp (T:=T) d<⊤ := by
    change (realTimeClamp d:EReal)<T
    rw [real_time_clamp_eq d hd hdT.le];exact hdT
  have hs t : MeasurableSet[F t] {w : Ω | realTimeClamp (T:=T) d≤t} := by
    by_cases h : realTimeClamp (T:=T) d≤t <;> simp [h]
  have hprob ε (hε : 0<ε) : Tendsto (fun k => P {w | ε≤C k (realTimeClamp d) w}) atTop (𝓝 0) := by
    have he k : P {w | ε≤C k (realTimeClamp d) w}=P {w | ε≤∫ r,H k (w,r)^2
        ∂(intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) w) (hAdm w) (fun r hr => (hAdc w r hr).mono inter_subset_left)).measure} := by
      obtain ⟨_,_,he⟩ := hCe k j d hd hdj
      exact measure_congr (he.mono fun w hw => by simp only [mem_setOf_eq,hw])
    simpa only [he] using hp ε hε
  intro t ht ε hε
  have hlim := local_martingale_probability_of_quadratic_variation P F hF hle hnull Y C hY hC
    (fun _ => realTimeClamp d) hs (fun _ => hdt) hprob ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro k
  apply measure_mono
  intro w hw
  have hh := (localStoppedPath P F hF hle (hY k) (fun _ => realTimeClamp d) hs (fun _ => hdt) w).norm_coe_le_norm t
  rw [ContinuousMap.norm_eq_iSup_norm] at hh
  have hh' : |Y k t w|≤⨆ t,|Y k (min (realTimeClamp d) t) w| := by
    simpa only [Real.norm_eq_abs,localStoppedPath,continuousPath,ContinuousMap.coe_mk,min_eq_right ht] using hh
  exact hw.trans hh'

end Asakura.Chapter11
