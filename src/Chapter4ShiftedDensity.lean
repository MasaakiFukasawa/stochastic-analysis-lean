import Chapter4HalfLineCovarianceDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

lemma deterministic_shift_bot (s : ℝ) (hs : 0≤s) :
    deterministicTimeShift s hs ⊥=realTimeClamp (T:=⊤) s := by
  apply Subtype.ext
  change (s:EReal)+0=(realTimeClamp (T:=⊤) s).val
  rw [real_time_clamp_eq s hs le_top,add_zero]

lemma integral_primitive_shift (q : ℝ → ℝ) (hq : Continuous q) (s r : ℝ) :
    (∫ a in 0..(s+r),q a)-(∫ a in 0..s,q a)=∫ a in 0..r,q (s+a) := by
  rw [intervalIntegral.integral_comp_add_left,add_zero]
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hq.intervalIntegrable 0 s) (hq.intervalIntegrable s (s+r))
  linarith

theorem shifted_primitive_density
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : HalfClosedTime → Ω → ℝ) (Q : Ω → ℝ → ℝ) (hQ : ∀ w,Continuous (Q w))
    (he : ∀ᵐ w ∂P,∀ r : ℝ,0≤r → C (realTimeClamp r) w=∫ a in 0..r,Q w a)
    (s : ℝ) (hs : 0≤s) :
    ∀ᵐ w ∂P,∀ r : ℝ,0≤r →
      C (deterministicTimeShift s hs (realTimeClamp r)) w-C (deterministicTimeShift s hs ⊥) w=
        ∫ a in 0..r,Q w (s+a) := by
  filter_upwards [he] with w hw
  intro r hr
  rw [deterministic_shift_real s hs r hr,deterministic_shift_bot s hs,
    hw (s+r) (add_nonneg hs hr),hw s hs]
  exact integral_primitive_shift (Q w) (hQ w) s r

/-- The shifted Brownian covariance is the usual clock, including all
cross entries of its covariance matrix. -/
theorem shifted_brownian_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X Y C : HalfClosedTime → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (a : ℝ) (hc : ∀ w (r : ℝ),0≤r → C (realTimeClamp r) w=a*r)
    (s : ℝ) (hs : 0≤s) :
    let φ := deterministicTimeShift s hs
    LocalCovarianceWitness P (fun t => F (φ t))
      (fun t w => X (φ t) w-X (φ ⊥) w) (fun t w => Y (φ t) w-Y (φ ⊥) w)
      (fun t w => C (φ t) w-C (φ ⊥) w) ∧
    ∀ w (r : ℝ),0≤r → C (φ (realTimeClamp r)) w-C (φ ⊥) w=a*r := by
  refine ⟨covariance_shifted_future P F hF hle hnull X Y C hX hY hC s hs,?_⟩
  intro w r hr
  rw [deterministic_shift_real s hs r hr,deterministic_shift_bot s hs,
    hc w (s+r) (add_nonneg hs hr),hc w s hs]
  ring

end Asakura.Chapter4
