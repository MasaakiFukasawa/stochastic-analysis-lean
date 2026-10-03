import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter8

/-- The three-dimensional Jacobian factor 4 pi r^2, with Euclidean speed. -/
theorem three_dimensional_radial_integral (f : ℝ → ℝ) :
    (∫ v : EuclideanSpace ℝ (Fin 3),f ‖v‖)=
      4*Real.pi*(∫ r in Ioi (0:ℝ),r^2*f r) := by
  have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3))) f
  have hv : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (Metric.ball 0 1)=Real.pi*4/3 := by
    rw [Measure.real,EuclideanSpace.volume_ball_fin_three]
    norm_num [ENNReal.toReal_ofReal,show 0≤Real.pi*4/3 by positivity]
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))=3 := by simp
  simp only [hd,hv,show 3-1=2 by decide,nsmul_eq_mul,smul_eq_mul] at h
  rw [h]
  norm_num
  <;> ring

end Asakura.Chapter8
