import Chapter7ClosedCovarianceExtension
import Chapter7FiniteTimeCLT
import Chapter7BrownianExists

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

noncomputable def finiteClosedPath {Ω : Type*} (a : ℝ≥0) [Fact (0 ≤ ((a:ℝ):EReal))]
    (M : ClosedTime ((a:ℝ):EReal) → Ω → ℝ) (hc : ∀ w,Continuous (fun t => M t w))
    (w : Ω) : C(Icc (0:ℝ≥0) a,ℝ) :=
  ⟨fun t => M (realTimeClamp t.val) w,
    (hc w).comp (real_time_clamp_continuous.comp (NNReal.continuous_coe.comp continuous_subtype_val))⟩

/-- The closed finite-interval clause: extend at the terminal time using
continuity and localization, add an independent Brownian tail, then restrict
the proved half-line convergence. No moment assumption on terminal values. -/
theorem closed_finite_martingale_clt
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ≥0) [Fact (0 ≤ ((a:ℝ):EReal))] (ha0 : 0 < a)
    (F : ClosedTime ((a:ℝ):EReal) → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (M C : ℕ → ClosedTime ((a:ℝ):EReal) → Ω → ℝ)
    (hM : ∀ n,LocalMProcessWitness P F (M n))
    (hC : ∀ n,LocalCovarianceWitness P F (M n) (M n) (C n))
    (hMa : ∀ n t,Measurable[F t] (M n t)) (hMc : ∀ n w,Continuous (fun t => M n t w))
    (hCa : ∀ n t,Measurable[F t] (C n t)) (hCc : ∀ n w,Continuous (fun t => C n t w))
    (hp : ∀ t : ℝ≥0,t ≤ a → TendstoInMeasure P (fun n => C n (realTimeClamp t)) atTop (fun _ => (t:ℝ))) :
    ∃ (Γ : Type) (q : MeasurableSpace Γ) (Q : Measure Γ) (hQ : IsProbabilityMeasure Q),
    letI := q
    letI := hQ
    ∃ B0 : BrownianSystem (P.prod Q) 1,
      TendstoInDistribution (fun n => finiteClosedPath a (M n) (hMc n)) atTop
        (fun z => pathRestriction a (brownianContinuousPath B0 z)) (fun _ => P) (P.prod Q) := by
  let G := fun t => F (closedPrefixProjection a t)
  let X := fun n t w => M n (closedPrefixProjection a t) w
  have hG : Monotone G := hF.comp (closed_prefix_projection_mono a)
  have hGl t : G t ≤ m := hle _
  have hX n : LocalMProcessWitness P G (X n) :=
    closed_local_constant_extension P a F hF hle (M n) (hM n) (hMa n) (hMc n)
  have haE : 0 < ((a:ℝ):EReal) := by exact_mod_cast ha0
  choose D hD hDe using fun n => closed_covariance_constant_extension P a haE F hF hle hnull
    (M n) (C n) (hM n) (hC n) (hMa n) (hMc n) (hCa n) (hCc n)
  have hDp (t : ℝ≥0) (ht : t ≤ a) : TendstoInMeasure P (fun n => D n (realTimeClamp t)) atTop (fun _ => (t:ℝ)) := by
    apply TendstoInMeasure.congr _ Filter.EventuallyEq.rfl (hp t ht)
    intro n
    filter_upwards [hDe n] with w hw
    rw [hw,closed_prefix_projection_real (a:ℝ) (t:ℝ) t.property ht]
  obtain ⟨Γ,q,Q,hQ,⟨B⟩⟩ := brownian_system_exists
  letI := q
  letI := hQ
  obtain ⟨B0,hlim⟩ := finite_time_clt_of_half_line P Q G hG hGl X D hX hD a hDp B
  have he n w : pathRestriction a (localContinuousPath (X n) ((hX n).path P G) w) = finiteClosedPath a (M n) (hMc n) w := by
    ext t
    change M n (closedPrefixProjection a (realTimeClamp t.val)) w = M n (realTimeClamp t.val) w
    rw [closed_prefix_projection_real (a:ℝ) (t.val:ℝ) t.val.property t.property.2]
  simp_rw [he] at hlim
  exact ⟨Γ,q,Q,hQ,B0,hlim⟩

end Asakura.Chapter7
