import EndToEndDensityL1
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction NNReal
namespace Asakura.EndToEnd
set_option backward.isDefEq.respectTransparency false

/-- L1 convergence of real densities controls every bounded continuous
 test, by the explicit integral error bound. -/
theorem density_L1_tests {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (p : ℕ → E → ℝ) (q : E → ℝ)
    (hp : ∀ n,Integrable (p n) μ) (hq : Integrable q μ)
    (hlim : Tendsto (fun n => ∫ x,|p n x-q x| ∂μ) atTop (𝓝 0))
    (φ : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ x,p n x*φ x ∂μ) atTop (𝓝 (∫ x,q x*φ x ∂μ)) := by
  have hpφ n := (hp n).mul_bdd φ.continuous.aestronglyMeasurable (.of_forall φ.norm_coe_le_norm)
  have hqφ := hq.mul_bdd φ.continuous.aestronglyMeasurable (.of_forall φ.norm_coe_le_norm)
  have hb n : ‖(∫ x,p n x*φ x ∂μ)-(∫ x,q x*φ x ∂μ)‖ ≤
      ‖φ‖*(∫ x,|p n x-q x| ∂μ) := by
    rw [← integral_sub (hpφ n) hqφ,← integral_const_mul]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono (hpφ n |>.sub hqφ |>.norm) (((hp n).sub hq).abs.const_mul ‖φ‖)
    intro x
    change ‖p n x*φ x-q x*φ x‖ ≤ ‖φ‖ * |p n x-q x|
    rw [← sub_mul,norm_mul,Real.norm_eq_abs (p n x-q x)]
    exact (mul_le_mul_of_nonneg_left (φ.norm_coe_le_norm x) (abs_nonneg _)).trans_eq (mul_comm _ _)
  have hz : Tendsto (fun n => (∫ x,p n x*φ x ∂μ)-(∫ x,q x*φ x ∂μ)) atTop (𝓝 0) :=
    squeeze_zero_norm hb (by simpa using hlim.const_mul ‖φ‖)
  have ht := hz.add (tendsto_const_nhds (x:=∫ x,q x*φ x ∂μ))
  simpa only [sub_add_cancel,zero_add] using ht

#print axioms density_L1_tests
end Asakura.EndToEnd
