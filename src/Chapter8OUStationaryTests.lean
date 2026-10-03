import Chapter8AdditiveFlowLaw

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The stationary Gaussian convolution gives invariance of the actual
OU transition expectations, in the form required by the time-average proof. -/
theorem ou_stationary_tests (θ σ : ℝ) (hθ : 0<θ) (t : ℝ≥0)
    (f : ℝ → ℝ) (hf : Continuous f) (C : ℝ) (hC : ∀ x,‖f x‖≤C) :
    (∫ x,(∫ y,f y ∂ouKernel θ σ hθ t x) ∂gaussianReal 0 (ouStationaryVariance θ σ hθ))=
      ∫ x,f x ∂gaussianReal 0 (ouStationaryVariance θ σ hθ) := by
  let π := gaussianReal 0 (ouStationaryVariance θ σ hθ)
  let ν := gaussianReal 0 (ouVariance θ σ hθ t)
  let a := Real.exp (-θ*(t:ℝ))
  have hm x : ν.map (fun z => a*x+z)=ouKernel θ σ hθ t x := by
    simpa only [ν,a,ouKernel,add_zero,zero_add] using gaussianReal_map_const_add (μ := 0) (v := ouVariance θ σ hθ t) (a*x)
  have hi : Integrable (fun z : ℝ × ℝ => f (a*z.1+z.2)) (π.prod ν) :=
    (integrable_const C).mono' (by fun_prop) (ae_of_all _ (fun z => hC _))
  have hflow : (π.prod ν).map (fun z => a*z.1+z.2)=π := by
    change flowLaw π ν (fun x z => a*x+z)=π
    have hh := additive_flow_law π ν (fun x => a*x) (by fun_prop) id measurable_id
    simp only [id_eq,Measure.map_id] at hh
    rw [hh]
    exact ou_stationary_gaussian θ σ hθ t
  have he x : (∫ y,f y ∂ouKernel θ σ hθ t x)=∫ z,f (a*x+z) ∂ν := by
    rw [←hm x,integral_map (by fun_prop) hf.aestronglyMeasurable]
  simp_rw [he]
  rw [←integral_prod _ hi]
  have hh := integral_map (μ := π.prod ν) (by fun_prop : AEMeasurable (fun z : ℝ × ℝ => a*z.1+z.2) (π.prod ν)) hf.aestronglyMeasurable
  rw [hflow] at hh
  exact hh.symm
end Asakura.Chapter8
