import Chapter11BarrierKernel
import Chapter11HeatGaussianRepresentation
import Mathlib.MeasureTheory.Group.Integral

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace Asakura.Chapter11
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem barrier_reflected_kernel_identity (a θ ν y z : ℝ) (v : ℝ≥0) (hv : v≠0)
    (hν : ν*(v:ℝ)=2*a*θ) :
    Real.exp (ν*z)*gaussianPDFReal (y+a*θ) v (-z)=
      Real.exp (-ν*y)*gaussianPDFReal (-y+a*θ) v z := by
  have hv0 : (v:ℝ)≠0 := by exact_mod_cast hv
  have he : ν*z+(-(-z-(y+a*θ))^2/(2*(v:ℝ)))=
      -ν*y+(-(z-(-y+a*θ))^2/(2*(v:ℝ))) := by
    rw [(eq_div_iff hv0).mpr hν]
    field_simp
    ring
  simp only [gaussianPDFReal]
  calc
    _ = (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹*Real.exp (ν*z+(-(-z-(y+a*θ))^2/(2*(v:ℝ)))) := by rw [Real.exp_add];ring
    _ = (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹*Real.exp (-ν*y+(-(z-(-y+a*θ))^2/(2*(v:ℝ)))) := by rw [he]
    _ = _ := by rw [Real.exp_add];ring

/-- Weighted reflection commutes with the drifted Gaussian average.
This identifies the reflected known solution with another actual heat
convolution, so its regularity is inherited from the same kernel proof. -/
theorem barrier_reflected_heat_integral (f : ℝ → ℝ) (a θ ν y : ℝ)
    (v : ℝ≥0) (hv : v≠0) (hν : ν*(v:ℝ)=2*a*θ) :
    (∫ z,(Real.exp (-ν*z)*f (-z))*gaussianPDFReal (y+a*θ) v z)=
      Real.exp (-ν*y)*(∫ z,f z*gaussianPDFReal (-y+a*θ) v z) := by
  rw [←integral_neg_eq_self (fun z => (Real.exp (-ν*z)*f (-z))*gaussianPDFReal (y+a*θ) v z) volume]
  rw [←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  simp only [neg_neg,mul_neg,neg_mul,neg_neg]
  have he := barrier_reflected_kernel_identity a θ ν y z v hv hν
  calc
    _ = f z*(Real.exp (ν*z)*gaussianPDFReal (y+a*θ) v (-z)) := by ring
    _ = f z*(Real.exp (-ν*y)*gaussianPDFReal (-y+a*θ) v z) := by rw [he]
    _ = _ := by ring


theorem reflected_payoff_exponential_bound (f : ℝ → ℝ) (hf : Measurable f)
    (K ν : ℝ) (hK : 0≤K) (hn : ∀ z,0≤f z) (hb : ∀ z,f z≤K) :
    Measurable (fun z => Real.exp (-ν*z)*f (-z)) ∧
      (∀ z,0≤Real.exp (-ν*z)*f (-z)) ∧
      ∀ z,Real.exp (-ν*z)*f (-z)≤K*(1+Real.exp ((-ν)*z)) := by
  refine ⟨(by fun_prop),fun z => mul_nonneg (Real.exp_pos _).le (hn _),?_⟩
  intro z
  have hh := mul_le_mul_of_nonneg_left (hb (-z)) (Real.exp_pos (-ν*z)).le
  nlinarith

end Asakura.Chapter11
