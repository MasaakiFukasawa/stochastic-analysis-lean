import Chapter11BarrierKernel

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter11
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Integrating the image-kernel estimate gives the bounds used to turn
the stopped local martingale into a true martingale. -/
theorem barrier_image_integral_bounds (a θ ν y : ℝ) (v : ℝ≥0) (hv : v≠0)
    (hν : ν*(v:ℝ)=2*a*θ) (hy : y≤0)
    (g : ℝ → ℝ) (hg : Measurable g) (K : ℝ) (hK : 0≤K)
    (hgn : ∀ z,0≤g z) (hgb : ∀ z,g z≤K) (hgz : ∀ z,0<z → g z=0) :
    let V := ∫ z,g z*gaussianPDFReal (y+a*θ) v z
    let U := V-Real.exp (-ν*y)*(∫ z,g z*gaussianPDFReal (-y+a*θ) v z)
    0≤U ∧ U≤V ∧ V≤K := by
  have hi (μ : ℝ) : Integrable (fun z => g z*gaussianPDFReal μ v z) := by
    apply ((integrable_gaussianPDFReal μ v).const_mul K).mono'
      (hg.mul (measurable_gaussianPDFReal _ _)).aestronglyMeasurable
    apply ae_of_all
    intro z
    rw [Real.norm_eq_abs,Pi.mul_apply,abs_of_nonneg (mul_nonneg (hgn z) (gaussianPDFReal_nonneg _ _ _))]
    exact mul_le_mul_of_nonneg_right (hgb z) (gaussianPDFReal_nonneg _ _ _)
  have hle z : Real.exp (-ν*y)*(g z*gaussianPDFReal (-y+a*θ) v z)≤
      g z*gaussianPDFReal (y+a*θ) v z := by
    by_cases hz : z≤0
    · have hh := (barrier_gaussian_kernel_bounds a θ ν y z v hv hν hy hz).1
      have hm := mul_le_mul_of_nonneg_left (sub_nonneg.mp hh) (hgn z)
      nlinarith
    · rw [hgz z (lt_of_not_ge hz)]
      simp
  have hlu := integral_mono ((hi (-y+a*θ)).const_mul _) (hi (y+a*θ)) hle
  rw [integral_const_mul] at hlu
  have hnon : 0≤Real.exp (-ν*y)*(∫ z,g z*gaussianPDFReal (-y+a*θ) v z) :=
    mul_nonneg (Real.exp_pos _).le (integral_nonneg fun z => mul_nonneg (hgn z) (gaussianPDFReal_nonneg _ _ _))
  have hupper := integral_mono (hi (y+a*θ)) ((integrable_gaussianPDFReal (y+a*θ) v).const_mul K)
    (fun z => mul_le_mul_of_nonneg_right (hgb z) (gaussianPDFReal_nonneg _ _ _))
  rw [integral_const_mul,integral_gaussianPDFReal_eq_one _ hv,mul_one] at hupper
  exact ⟨sub_nonneg.mpr hlu,sub_le_self _ hnon,hupper⟩

/-- The logarithmic payoff has the required sign, bound, and support. -/
theorem barrier_log_payoff_bounds (b K : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b) :
    let g := fun z : ℝ => if z<0 then max (b*Real.exp z-K) 0 else 0
    Measurable g ∧ (∀ z,0≤g z) ∧ (∀ z,g z≤b-K) ∧ (∀ z,0<z → g z=0) := by
  dsimp only
  refine ⟨Measurable.ite measurableSet_Iio ((measurable_const.mul Real.measurable_exp).sub measurable_const |>.max measurable_const) measurable_const,?_,?_,?_⟩
  · intro z
    split <;> positivity
  · intro z
    split
    · rename_i hz
      apply max_le
      · have he := Real.exp_le_one_iff.mpr hz.le
        nlinarith
      · exact sub_nonneg.mpr hKb.le
    · exact sub_nonneg.mpr hKb.le
  · intro z hz
    rw [if_neg (not_lt_of_ge hz.le)]

end Asakura.Chapter11
