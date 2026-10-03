import Chapter4PowerCoefficientEnergy
import Chapter4DriftPowerBound

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The actual drift primitive has the required p moment and prefix bound. -/
theorem coefficient_drift_power_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0≤R) (p : ℝ) (hp : 1≤p)
    (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (hm : Measurable Y) (hi : MemLp Y (ENNReal.ofReal p) P)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H) (K : ℝ) (hK : 0≤K)
    (hb : ∀ w r,r∈Icc 0 R → |H (w,r)|^p≤K*(1+|Y w (projIcc 0 R hR r)|^p))
    (D : Ω → C(Icc (0:ℝ) R,ℝ)) (hDm : AEStronglyMeasurable D P)
    (hD : ∀ᵐ w ∂P,∀ t,D w t=∫ r in 0..t.val,H (w,r)) :
    MemLp D (ENNReal.ofReal p) P ∧
    (∫ w,‖D w‖^p ∂P)≤
      (R^(p-1)*K)*(R+∫ r in 0..R,(∫ w,‖prefixPath hR (Y w) r‖^p ∂P)) := by
  have hp0 : 0<p := by linarith only [hp]
  let ν := volume.restrict (Ioc (0:ℝ) R)
  obtain ⟨hI,hbI⟩ := coefficient_power_energy P R hR p hp0 Y hm hi H hHm K hK hb
  have hper : ∀ᵐ w ∂P,IntervalIntegrable (fun r => |H (w,r)|^p) volume 0 R := by
    filter_upwards [hI.prod_right_ae] with w hw
    refine ⟨hw,?_⟩
    change Integrable (fun r => |H (w,r)|^p) (volume.restrict (Ioc R 0))
    rw [Ioc_eq_empty_of_le hR,Measure.restrict_empty]
    exact integrable_zero_measure
  have hpoint : ∀ᵐ w ∂P,‖D w‖^p≤R^(p-1)*(∫ r in 0..R,|H (w,r)|^p) := by
    filter_upwards [hper,hD] with w hw hDw
    exact drift_path_power_bound R hR (fun r => H (w,r)) p hp hw (D w) hDw
  have hme : AEStronglyMeasurable (fun w => ‖D w‖^p) P :=
    (Real.continuous_rpow_const hp0.le).comp_aestronglyMeasurable hDm.norm
  have hdom : Integrable (fun w => R^(p-1)*(∫ r in 0..R,|H (w,r)|^p)) P := by
    simp_rw [intervalIntegral.integral_of_le hR]
    exact hI.integral_prod_left.const_mul _
  have hE : Integrable (fun w => ‖D w‖^p) P := by
    apply hdom.mono' hme
    filter_upwards [hpoint] with w hw
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hw
  have hDi : MemLp D (ENNReal.ofReal p) P := by
    apply (integrable_norm_rpow_iff hDm (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hp0.le] using hE
  refine ⟨hDi,?_⟩
  have hh := integral_mono_ae hE hdom hpoint
  rw [integral_const_mul] at hh
  have he : (∫ w,(∫ r in 0..R,|H (w,r)|^p) ∂P)=∫ z,|H z|^p ∂P.prod ν := by
    simp_rw [intervalIntegral.integral_of_le hR]
    exact (integral_prod _ hI).symm
  rw [he] at hh
  exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbI (Real.rpow_nonneg hR _))

end Asakura.Chapter4
