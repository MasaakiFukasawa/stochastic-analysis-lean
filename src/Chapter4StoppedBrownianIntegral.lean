import Chapter4ProgressiveItoBDG
import Chapter2ItoStoppingTimes
import Chapter2StoppingIntegrandMembership

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Construct the actual stopped integral for a progressive coefficient,
identify it with stopping the original integral, and retain its domain. -/
theorem stopped_brownian_integral_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A X : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A) (hX : LocalMProcessWitness P F X)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (G : Ω × ℝ → ℝ)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hXI : ItoCovarianceFormula P F W G X)
    (τ : Ω → ClosedTime T) (hτtop : ∀ w,τ w<⊤)
    (hτ : ∀ t,MeasurableSet[F t] {w | τ w≤t}) :
    let K := fun z : Ω × ℝ => (Ioc (⊥ : ClosedTime T) (τ z.1)).indicator (fun _ => G z) (realTimeClamp z.2)
    ∃ Z : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F W K Z ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → Z t w=X (min (τ w) t) w) ∧
      (∀ n,@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) (c n) => K (z.1,z.2.val))) ∧
      (∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => K (w,r)^2) volume 0 (c n)) := by
  classical
  dsimp only
  have hAm n w : MonotoneOn (fun r => A (realTimeClamp r) w) (Icc 0 (c n)) := by
    intro s hs t ht hst
    simpa only [hclock n w s hs,hclock n w t ht] using hst
  have hAc n w : ContinuousOn (fun r => A (realTimeClamp r) w) (Icc 0 (c n)) := by
    apply continuousOn_id.congr
    intro r hr; exact hclock n w r hr
  have hmeasure n w : (intervalStieltjes 0 (c n) (hc n).le
      (fun r => A (realTimeClamp r) w) (hAm n w)
      (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure=volume.restrict (Ioc 0 (c n)) := by
    rw [← clock_stieltjes_measure 0 (c n) (hc n).le]
    congr 1
    apply StieltjesFunction.ext
    intro r
    exact hclock n w _ (intervalClamp_mem _ _ _ _)
  have his n : ∀ᵐ w ∂P,Integrable (fun r => G (w,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) w) (hAm n w)
        (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure := by
    filter_upwards [hi n] with w hw
    rw [hmeasure]
    exact hw.1
  have hbot : ∀ t,MeasurableSet[F t] {w : Ω | (⊥ : ClosedTime T)≤t} := by simp
  obtain ⟨Y,Z,hY,hZ,hYI,hZI,he⟩ := ito_stochastic_interval_for_stopping_times P hT F hF hle hnull
    W A hW hA c hc hcm hcT hct hcut hcc hAm hAc G hG his
    (fun _ => ⊥) τ (fun _ => hT) hτtop (fun _ => bot_le) hbot hτ
  have hYX := ItoCovarianceFormula.unique P hT F hF hle hnull W Y X G hW hY hX hYI hXI
  refine ⟨Z,hZ,hZI,?_,?_,?_⟩
  · filter_upwards [he,hYX,hX.initial P F] with w hw hsame hzero
    intro t ht
    rw [hw t ht,hsame _ ((min_le_right _ _).trans_lt ht),min_eq_left bot_le,hsame _ hT]
    simpa only [Pi.zero_apply,hzero,sub_zero]
  · intro n
    exact stopping_interval_prefix_progressive F hF (fun _ => ⊥) τ hbot hτ (c n) G (hG n)
  · intro n
    filter_upwards [hi n] with w hw
    have hm : MeasurableSet {r : ℝ | realTimeClamp (T := T) r∈Ioc (⊥ : ClosedTime T) (τ w)} :=
      real_time_clamp_continuous.measurable measurableSet_Ioc
    have heq : (fun r => ((Ioc (⊥ : ClosedTime T) (τ w)).indicator (fun _ => G (w,r)) (realTimeClamp r))^2)=
        {r : ℝ | realTimeClamp (T := T) r∈Ioc (⊥ : ClosedTime T) (τ w)}.indicator (fun r => G (w,r)^2) := by
      funext r
      simp only [indicator_apply,mem_setOf_eq]
      split_ifs <;> simp
    rw [heq]
    exact ⟨hw.1.indicator hm,hw.2.indicator hm⟩

end Asakura.Chapter4
