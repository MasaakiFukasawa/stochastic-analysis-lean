import Chapter9ReverseBrownianRegularity
import Chapter9ReverseLogScore

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The final integral SDE with the manuscript's literal log-density
 gradient; integrability of this displayed drift is proved as well. -/
theorem reverse_brownian_log_sde {Ω : Type*} {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → Fin d → ℝ) (hXc : ∀ w,Continuous (fun r => X r w))
    (T s : ℝ) (hs : 0≤s) (hsT : s<T) (w : Ω) (i : Fin d) :
    let a := fun r => X (T-r) w i+2*directional
      (fun y => Real.log (ouCoordinateDensity μ (T-r,y))) (Pi.single i 1) (X (T-r) w)
    IntervalIntegrable a volume 0 s ∧
      X (T-s) w i=X T w i+(∫ r in 0..s,a r)+Real.sqrt 2*reverseBrownian μ X T s w i := by
  let a := fun r => X (T-r) w i+2*directional
    (fun y => Real.log (ouCoordinateDensity μ (T-r,y))) (Pi.single i 1) (X (T-r) w)
  have he r (hr : r∈Icc 0 s) : ouReverseDrift μ (T-r,X (T-r) w) i=a r :=
    ou_reverse_drift_log_score μ (T-r) (sub_pos.mpr (hr.2.trans_lt hsT)) _ i
  have hc : ContinuousOn a (Icc 0 s) :=
    (reverse_drift_path_continuous μ X hXc T s hsT w i).congr (fun r hr => (he r hr).symm)
  refine ⟨hc.intervalIntegrable_of_Icc hs,?_⟩
  have hi : (∫ r in 0..s,ouReverseDrift μ (T-r,X (T-r) w) i)=∫ r in 0..s,a r := by
    apply intervalIntegral.integral_congr
    intro r hr
    exact he r (uIcc_of_le hs ▸ hr)
  simpa only [hi] using reverse_brownian_sde_identity μ X T s w i
end Asakura.Chapter9
