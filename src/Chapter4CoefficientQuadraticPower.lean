import Chapter4PowerCoefficientEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The quadratic-integral moment appearing on the right of BDG, bounded
by the stopped solution's prefix moments through Hölder and Fubini. -/
theorem coefficient_quadratic_power_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0≤R) (p : ℝ) (hp : 2≤p)
    (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (hm : Measurable Y) (hi : MemLp Y (ENNReal.ofReal p) P)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H) (K : ℝ) (hK : 0≤K)
    (hb : ∀ w r,r∈Icc 0 R → |H (w,r)|^p≤K*(1+|Y w (projIcc 0 R hR r)|^p)) :
    Integrable (fun w => (∫ r in 0..R,H (w,r)^2)^(p/2)) P ∧
    (∫ w,(∫ r in 0..R,H (w,r)^2)^(p/2) ∂P)≤
      (R^(p/2-1)*K)*(R+∫ r in 0..R,(∫ w,‖prefixPath hR (Y w) r‖^p ∂P)) := by
  have hp0 : 0<p := by linarith only [hp]
  let ν := volume.restrict (Ioc (0:ℝ) R)
  obtain ⟨hI,hbI⟩ := coefficient_power_energy P R hR p hp0 Y hm hi H hHm K hK hb
  have hper : ∀ᵐ w ∂P,IntervalIntegrable (fun r => (H (w,r)^2)^(p/2)) volume 0 R := by
    filter_upwards [hI.prod_right_ae] with w hw
    simp_rw [square_power_half]
    refine ⟨hw,?_⟩
    change Integrable (fun r => |H (w,r)|^p) (volume.restrict (Ioc R 0))
    rw [Ioc_eq_empty_of_le hR,Measure.restrict_empty]
    exact integrable_zero_measure
  have hpoint : ∀ᵐ w ∂P,(∫ r in 0..R,H (w,r)^2)^(p/2)≤R^(p/2-1)*(∫ r in 0..R,|H (w,r)|^p) := by
    filter_upwards [hper] with w hw
    have hh := (interval_integral_power_holder R hR (fun r => H (w,r)^2) (fun _ => sq_nonneg _)
      (p/2) (by linarith only [hp]) hw).2
    simpa only [square_power_half] using hh
  have hme : Measurable (fun w => (∫ r in 0..R,H (w,r)^2)^(p/2)) := by
    simp_rw [intervalIntegral.integral_of_le hR]
    exact (Real.continuous_rpow_const (by positivity : 0≤p/2)).measurable.comp
      ((hHm.pow_const 2).stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hdom : Integrable (fun w => R^(p/2-1)*(∫ r in 0..R,|H (w,r)|^p)) P := by
    simp_rw [intervalIntegral.integral_of_le hR]
    exact hI.integral_prod_left.const_mul _
  have hE : Integrable (fun w => (∫ r in 0..R,H (w,r)^2)^(p/2)) P := by
    apply hdom.mono' hme.aestronglyMeasurable
    filter_upwards [hpoint] with w hw
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg
      (intervalIntegral.integral_nonneg_of_forall hR (fun _ => sq_nonneg _)) _)]
    exact hw
  refine ⟨hE,?_⟩
  have hh := integral_mono_ae hE hdom hpoint
  rw [integral_const_mul] at hh
  have he : (∫ w,(∫ r in 0..R,|H (w,r)|^p) ∂P)=∫ z,|H z|^p ∂P.prod ν := by
    simp_rw [intervalIntegral.integral_of_le hR]
    exact (integral_prod _ hI).symm
  rw [he] at hh
  exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbI (Real.rpow_nonneg hR _))

end Asakura.Chapter4
