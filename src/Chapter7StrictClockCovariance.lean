import Chapter7RawClockTransfer
import Chapter7ClockInverseStopping
import Chapter3IncreasingAdaptedVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- A strictly increasing adapted clock transfers both a local martingale
and its actual quadratic variation to the stopped filtration. Neither
of the two time-changed local-martingale properties is an assumption. -/
theorem strict_clock_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (hCm : ∀ w,MonotoneOn (fun t => C t w) (Iio ⊤))
    (A : ClosedTime T → Ω → ℝ)
    (hAa : ∀ t,t < ⊤ → Measurable[F t] (A t))
    (hAm : ∀ w,StrictMonoOn (fun t => A t w) (Iio ⊤))
    (hAc : ∀ w t,t < ⊤ → ContinuousAt (fun s => A s w) t)
    (hA0 : ∀ w,A ⊥ w = 0) (hAu : ∀ w r,∃ t,t < ⊤ ∧ r < A t w) :
    let τ := fun r w => inverseRealClock (fun t => A t w) r
    let hτ := real_clock_inverse_stopping hT F A hAa (fun w => (hAm w).monotoneOn) hAc hA0 hAu
    let G := halfClosedFiltration m (fun s : ℝ≥0 => writtenStoppedSpace m F (τ s) (hτ s))
    LocalMProcessWitness P G (fun t w => X (τ (halfTimeReal t) w) w) ∧
      LocalCovarianceWitness P G
        (fun t w => X (τ (halfTimeReal t) w) w)
        (fun t w => X (τ (halfTimeReal t) w) w)
        (fun t w => C (τ (halfTimeReal t) w) w) := by
  let τ := fun r w => inverseRealClock (fun t => A t w) r
  have hτ := real_clock_inverse_stopping hT F A hAa (fun w => (hAm w).monotoneOn) hAc hA0 hAu
  let H := fun r => writtenStoppedSpace m F (τ r) (hτ r)
  let G := halfClosedFiltration m (fun s : ℝ≥0 => H s)
  let Y := fun (t : HalfClosedTime) w => X (τ (halfTimeReal t) w) w
  let D := fun (t : HalfClosedTime) w => C (τ (halfTimeReal t) w) w
  have hp w := real_clock_inverse_properties hT (fun t => A t w) (hAm w).monotoneOn (hAc w) (hA0 w) (hAu w)
  have hτm w : Monotone (fun r => τ r w) := (hp w).1
  have hτ0 w : τ 0 w = ⊥ := (hp w).2.1
  have hτt r w : τ r w < ⊤ := (hp w).2.2.1 r
  have hAn w a (ha : a < ⊤) : 0 ≤ A a w := by
    simpa only [hA0 w] using (hAm w).monotoneOn hT ha bot_le
  have hflat (Z : ClosedTime T → Ω → ℝ) w a b (ha : a < ⊤) (hb : b < ⊤)
      (he : A a w = A b w) : Z a w = Z b w := by
    rw [(hAm w).injOn ha hb he]
  have hcont (Z : ClosedTime T → Ω → ℝ)
      (hc : ∀ w t,t < ⊤ → ContinuousAt (fun s => Z s w) t) w :
      Continuous (fun r => Z (τ r w) w) :=
    real_clock_changed_path_continuous hT _ (hAm w).monotoneOn (hAc w) (hA0 w) (hAu w) _ (hc w) (hflat Z w)
  have hstop (Z : ClosedTime T → Ω → ℝ) w a (ha : a < ⊤) r :
      Z (min a (τ r w)) w = Z (τ (min (A a w) r) w) w :=
    (real_clock_stopping_identities hT _ (hAm w).monotoneOn (hAc w) (hA0 w) (hAu w) _ (hflat Z w) a ha r).2
  have hY : LocalMProcessWitness P G Y := local_martingale_raw_clock_transfer P F hF hle X hX τ hτ
    hτm hτ0 hτt (hcont X (hX.path P F)) A hAn (fun w => (hAm w).monotoneOn) hAu (hstop X)
  have hD : LocalMProcessWitness P G (fun t w => Y t w*Y t w-D t w) :=
    local_martingale_raw_clock_transfer P F hF hle _ hC.defect τ hτ hτm hτ0 hτt
      (hcont _ (hC.defect.path P F)) A hAn (fun w => (hAm w).monotoneOn) hAu (hstop (fun t w => X t w*X t w-C t w))
  have hHm : Monotone H := fun a b hab => written_stoppedSpace_mono m F
    (τ a) (τ b) (hτ a) (hτ b) (fun w => hτm w hab)
  have hGm : Monotone G := half_closed_filtration_mono m (fun s : ℝ≥0 => H s)
    (fun s t hst => hHm hst) (fun _ _ he => he.1)
  have hDa t (ht : t < ⊤) : Measurable[G t] (D t) := by
    have hh := ((hY.adapted P G t ht).mul (hY.adapted P G t ht)).sub (hD.adapted P G t ht)
    convert hh using 1
    funext w
    change D t w = Y t w*Y t w-(Y t w*Y t w-D t w)
    ring
  have hDc w t (ht : t < ⊤) : ContinuousAt (fun s => D s w) t :=
    (hcont C (local_covariance_path_continuous P F X X C hX hX hC) w).continuousAt.comp
      (changed_time_coordinate_continuousAt t ht)
  have hDv := continuous_increasing_adapted_variation (show (0:EReal) < ⊤ by simp) G hGm D hDa
    (fun w s hs t ht hst => hCm w (hτt _ w) (hτt _ w) (hτm w (half_time_real_mono hst ht))) hDc
  exact ⟨hY,⟨hD,hDv.toPathwise⟩⟩

end Asakura.Chapter7
