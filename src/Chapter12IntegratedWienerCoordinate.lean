import Chapter12IntegratedBrownianCovariance
import Chapter12LpBochnerPointwise
import Chapter12LinearCylinder

open MeasureTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- The time integral of the original continuous Brownian coordinates is
the Wiener integral of the integrated prefix direction, on the same space. -/
theorem integrated_wiener_coordinate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0≤T)
    (W : Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (B : Icc (0:ℝ) T × Ω → ℝ) (hm : Measurable B)
    (he : ∀ t,(W (finiteTimeIntervalVector T 0 t.val) : Ω → ℝ) =ᵐ[P] (fun w => B (t,w))) :
    (W (integratedBrownianDirection T hT) : Ω → ℝ) =ᵐ[P]
      (fun w => ∫ t : Icc (0:ℝ) T,B (t,w) ∂compactTimeMeasure T hT) := by
  have hi : Integrable (fun t : Icc (0:ℝ) T => finiteTimeIntervalVector T 0 t.val)
      (compactTimeMeasure T hT) := (finite_time_prefix_continuous T).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hb (t : Icc (0:ℝ) T) : MemLp (fun w => B (t,w)) 2 P := (Lp.memLp _).ae_eq (he t)
  have hbe (t : Icc (0:ℝ) T) : (hb t).toLp _=W (finiteTimeIntervalVector T 0 t.val) := by
    apply Lp.ext
    exact (hb t).coeFn_toLp.trans (he t).symm
  have hbi : Integrable (fun t : Icc (0:ℝ) T => (hb t).toLp _) (compactTimeMeasure T hT) := by
    simpa only [hbe,LinearIsometry.coe_toContinuousLinearMap] using W.toContinuousLinearMap.integrable_comp hi
  have hh := Lp_bochner_integral_pointwise (compactTimeMeasure T hT) P 2 le_rfl B hm hb hbi
  simp only [hbe] at hh
  have hc := W.toContinuousLinearMap.integral_comp_comm hi
  change (∫ t : Icc (0:ℝ) T,W (finiteTimeIntervalVector T 0 t.val) ∂compactTimeMeasure T hT)=
    W (integratedBrownianDirection T hT) at hc
  rw [hc] at hh
  exact hh

end Asakura.Chapter12
