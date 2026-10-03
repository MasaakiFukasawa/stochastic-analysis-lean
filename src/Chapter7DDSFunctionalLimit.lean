import Chapter7DDSRepresentatives
import Chapter7DDSRegularSystem
import Chapter7BrownianPathLaw
import Chapter7FunctionalClockLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

noncomputable def localContinuousPath
    {Ω : Type*} (X : HalfClosedTime → Ω → ℝ)
    (hc : ∀ w t,t < ⊤ → ContinuousAt (fun s => X s w) t) (w : Ω) : C(ℝ≥0,ℝ) :=
  ⟨fun t => X (realTimeClamp t) w,continuous_iff_continuousAt.mpr (fun (t : ℝ≥0) =>
    ((hc w _ (changed_time_finite t t.property)).comp
      real_time_clamp_continuous.continuousAt).comp NNReal.continuous_coe.continuousAt)⟩

/-- The divergent-bracket case of the functional martingale CLT, now from
actual local martingales and their quadratic variations. DDS, common
Brownian path laws, clock convergence and composition are all proved
inside the dependency chain. Independent Brownian-tail extension for
nondivergent brackets is handled separately. -/
theorem dds_functional_limit
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (M C : ℕ → HalfClosedTime → Ω → ℝ)
    (hM : ∀ n,LocalMProcessWitness P F (M n))
    (hC : ∀ n,LocalCovarianceWitness P F (M n) (M n) (C n))
    (hdiv : ∀ n,∀ᵐ w ∂P,∀ r : ℝ,∃ t,t < ⊤ ∧ r < C n t w)
    (hp : ∀ t : ℝ≥0,TendstoInMeasure P (fun n => C n (realTimeClamp t)) atTop (fun _ => (t:ℝ))) :
    ∃ B0 : BrownianSystem P 1,
      TendstoInDistribution (fun n => localContinuousPath (M n) ((hM n).path P F)) atTop
        (brownianContinuousPath B0) (fun _ => P) P := by
  have hT : (0:EReal) < ⊤ := by simp
  choose Y A hY hA he hAm hAc h0 hAu hflat using
    fun n => dds_regular_representatives P hT F hF hle hnull (M n) (C n) (hM n) (hC n) (hdiv n)
  choose B hB hrec hstop using fun n => dds_system_from_regular_paths P hT F hF hle hnull
    (Y n) (A n) (hY n) (hA n) (hAm n) (fun w => (h0 n w).2) (hAu n) (hflat n)
  have hAn n w t (ht : t < ⊤) : 0 ≤ A n t w := by
    simpa only [(h0 n w).2] using hAm n w hT ht bot_le
  let Q := fun n w => (⟨fun t : ℝ≥0 => ⟨A n (realTimeClamp t) w,hAn n w _ (changed_time_finite t t.property)⟩,
    Continuous.subtype_mk (continuous_iff_continuousAt.mpr (fun (t : ℝ≥0) =>
      ((hAc n w _ (changed_time_finite t t.property)).comp
        real_time_clamp_continuous.continuousAt).comp NNReal.continuous_coe.continuousAt)) _⟩ : C(ℝ≥0,ℝ≥0))
  have hQm n : Measurable[m] (Q n) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (((hA n).adapted P F (hY n) (hY n) _ (changed_time_finite t t.property)).mono
      (hle _) le_rfl).subtype_mk
  have hQmono n w : Monotone (Q n w) := by
    intro s t hst
    exact hAm n w (changed_time_finite s s.property) (changed_time_finite t t.property)
      (real_time_clamp_mono hst)
  have hQp (t : ℝ≥0) : TendstoInMeasure P (fun n w => Q n w t) atTop (fun _ => t) := by
    have hh : TendstoInMeasure P (fun n => A n (realTimeClamp t)) atTop (fun _ => (t:ℝ)) :=
      (hp t).congr (fun n => (he n).mono (fun w hw => (hw _).2.symm)) .rfl
    apply tendstoInMeasure_iff_dist.mpr
    intro ε hε
    change Tendsto (fun n => P {w | ε ≤ |A n (realTimeClamp t) w-(t:ℝ)|}) atTop (𝓝 0)
    exact tendstoInMeasure_iff_dist.mp hh ε hε
  have hlimit := functional_clock_limit P (fun n => brownianContinuousPath (B n))
    (brownianContinuousPath (B 0)) Q (fun n => brownian_continuous_path_measurable (B n))
    (brownian_continuous_path_measurable (B 0)) hQm
    (fun n => brownian_continuous_path_common_law P (B n) (B 0)) hQmono hQp
  refine ⟨B 0,?_⟩
  apply hlimit.congr _ .rfl
  intro n
  filter_upwards [he n] with w hw
  apply ContinuousMap.ext
  intro t
  change (B n).W 0 (realTimeClamp (A n (realTimeClamp t) w)) w = M n (realTimeClamp t) w
  rw [← hrec n _ (changed_time_finite t t.property) w,(hw _).1]

end Asakura.Chapter7
