import Chapter9ReverseKernelGaussian
import Chapter9TransitionDensity

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The reverse-kernel integral is exactly the Gaussian expectation in the
manuscript, including the inverse contraction Jacobian exp(d h). -/
theorem reverse_gaussian_change_variables {d : ℕ} (h : ℝ) (hh : 0<h)
    (x : Fin d → ℝ) (q : (Fin d → ℝ) → ℝ) (hq : Continuous q) :
    (∫ y,q y*gaussianKernel (Real.exp (-h)) (1-Real.exp (-2*h)) y x)=
      Real.exp ((d:ℝ)*h)*∫ ξ : EuclideanSpace ℝ (Fin d),
        q (fun i => Real.exp h*(x i-Real.sqrt (1-Real.exp (-2*h))*ξ i)) ∂stdGaussian _ := by
  let v := 1-Real.exp (-2*h)
  have hv : 0<v := ou_variance_positive h hh
  let w : ℝ≥0 := ⟨v/(Real.exp (-h))^2,by positivity⟩
  have hw : w≠0 := by apply ne_of_gt; exact_mod_cast (div_pos hv (sq_pos_of_pos (Real.exp_pos (-h))))
  let b := -Real.exp h*Real.sqrt v
  have hb : b^2=(w:ℝ) := by
    change (-Real.exp h*Real.sqrt v)^2=v/(Real.exp (-h))^2
    rw [mul_pow,neg_sq,Real.sq_sqrt hv.le,Real.exp_neg,inv_pow,div_inv_eq_mul]
    ring
  have hm := isotropic_gaussian_affine_density (Real.exp h) w hw x
  have hsc := standard_gaussian_scaled d b
  rw [hb] at hsc
  rw [←hsc,Measure.map_map (by fun_prop) (by fun_prop)] at hm
  let φ := fun ξ : EuclideanSpace ℝ (Fin d) => fun i => Real.exp h*(x i-Real.sqrt v*ξ i)
  have he : (fun ξ : EuclideanSpace ℝ (Fin d) => fun i => Real.exp h*x i+(b • ξ) i)=φ := by
    funext ξ i
    dsimp [b,φ]
    ring
  change (stdGaussian (EuclideanSpace ℝ (Fin d))).map
    (fun ξ => fun i => Real.exp h*x i+(b • ξ) i)=_ at hm
  rw [he] at hm
  have hk : Measurable (gaussianKernel (Real.exp h) w x) := by unfold gaussianKernel; fun_prop
  have hi := integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal
    (ae_of_all volume (fun _ => ENNReal.ofReal_lt_top)) q
  simp only [ENNReal.toReal_ofReal (gaussian_kernel_positive (Real.exp h) w x _).le,smul_eq_mul] at hi
  rw [←hm,integral_map (by dsimp [φ]; fun_prop) hq.aestronglyMeasurable] at hi
  calc
    _ = Real.exp ((d:ℝ)*h)*(∫ y,gaussianKernel (Real.exp h) w x y*q y) := by
      simp_rw [ou_reverse_kernel_gaussian_identity h hh x]
      rw [←integral_const_mul]
      apply integral_congr_ae
      apply ae_of_all
      intro y
      change q y*(Real.exp ((d:ℝ)*h)*gaussianKernel (Real.exp h) w x y)=_
      ring
    _ = _ := by rw [←hi]
end Asakura.Chapter9
