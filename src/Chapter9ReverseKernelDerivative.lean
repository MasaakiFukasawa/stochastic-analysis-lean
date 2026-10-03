import Chapter9ActualForwardPDE
import Chapter9ActualBackwardPDE
import Chapter9BackwardJointSmooth
import Chapter9CompactSupportDerivative
import Chapter9GaussianMixture

open Set Finset MeasureTheory
open scoped ContDiff NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

/-- Differentiate the actual reversed OU kernel, not an abstract semigroup
with the desired generator assumed. -/
theorem reverse_ou_kernel_derivative {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (T s r : ℝ) (hsr : s<r) (hrT : r<T) (x : Fin d → ℝ) :
    let p := fun t y => ∫ z,Real.exp (ouExponent z (t,y)) ∂μ
    let k := fun h y => gaussianKernel (Real.exp (-h)) (1-Real.exp (-2*h)) y x
    HasDerivAt (fun u => (∫ y,f y*p (T-u) y*k (u-s) y)/p (T-s) x)
      ((∫ y,p (T-r) y*reverseTest (p (T-r)) f y*k (r-s) y)/p (T-s) x) r := by
  dsimp only
  let p := fun t y => ∫ z,Real.exp (ouExponent z (t,y)) ∂μ
  let k := fun h y => gaussianKernel (Real.exp (-h)) (1-Real.exp (-2*h)) y x
  let F := fun u y => f y*p (T-u) y*k (u-s) y
  let D := fun u y => -f y*ouAdjoint (p (T-u)) y*k (u-s) y+
    f y*p (T-u) y*ouBackward (k (u-s)) y
  have hF : ContDiffOn ℝ ∞ F.uncurry (Ioo s T ×ˢ univ) := by
    intro q hq
    have hp : ContDiffAt ℝ ∞ (fun z : ℝ × (Fin d → ℝ) => p (T-z.1) z.2) q := by
      have hh : ContDiffAt ℝ ∞ (fun z => ∫ w,Real.exp (ouExponent w z) ∂μ) (T-q.1,q.2) := (ou_gaussian_mixture_smooth μ).contDiffAt
        ((isOpen_lt continuous_const continuous_fst).mem_nhds (sub_pos.mpr hq.1.2))
      exact hh.comp q (f := fun z : ℝ × (Fin d → ℝ) => (T-z.1,z.2)) (by fun_prop)
    have hk : ContDiffAt ℝ ∞ (fun z : ℝ × (Fin d → ℝ) => k (z.1-s) z.2) q := by
      have hh : ContDiffAt ℝ ∞ (fun z : ℝ × (Fin d → ℝ) => k z.1 z.2) (q.1-s,q.2) := (ou_backward_joint_smooth x).contDiffAt
        ((isOpen_lt continuous_const continuous_fst).mem_nhds (sub_pos.mpr hq.1.1))
      exact hh.comp q (f := fun z : ℝ × (Fin d → ℝ) => (z.1-s,z.2)) (by fun_prop)
    exact (((hf.contDiffAt.comp q contDiffAt_snd).mul hp).mul hk).contDiffWithinAt
  have hD (u : ℝ) (hu : u∈Ioo s T) (y : Fin d → ℝ) :
      HasDerivAt (fun w => F w y) (D u y) u := by
    have hp := (ou_mixture_actual_time_derivative μ (T-u) (sub_pos.mpr hu.2) y).comp u
      ((hasDerivAt_id u).const_sub T)
    have hk := (ou_kernel_actual_backward_derivative (u-s) (sub_pos.mpr hu.1) y x).comp u
      ((hasDerivAt_id u).sub_const s)
    have hh := (hp.const_mul (f y)).mul hk
    convert hh using 1
    · funext w; rfl
    · dsimp [F,D,p,k,Function.comp_def]
      ring
  have hF0 (u : ℝ) (y : Fin d → ℝ) (hy : y∉tsupport f) : F u y=0 := by
    dsimp [F]
    rw [image_eq_zero_of_notMem_tsupport hy,zero_mul,zero_mul]
  have hD0 (u : ℝ) (y : Fin d → ℝ) (hy : y∉tsupport f) : D u y=0 := by
    simp [D,image_eq_zero_of_notMem_tsupport hy]
  have hd := compact_smooth_integral_derivative (tsupport f) hfc.isCompact F D (Ioo s T)
    isOpen_Ioo hF hD hF0 hD0 r ⟨hsr,hrT⟩
  have hp0 (y : Fin d → ℝ) : p (T-r) y≠0 := by
    have hv := ou_variance_positive (T-r) (sub_pos.mpr hrT)
    exact (gaussian_mixture_positive μ (Real.exp (-(T-r))) ⟨1-Real.exp (-2*(T-r)),hv.le⟩
      (by intro hz; exact hv.ne' (congrArg (fun z : ℝ≥0 => (z:ℝ)) hz)) y).2.ne'
  have he := reverse_integral_generator f (p (T-r)) (k (r-s)) hf
    (ou_mixture_slice_smooth μ (T-r) (sub_pos.mpr hrT))
    (gaussian_initial_smooth _ _ x) hfc hp0
  change (∫ y,D r y)=(∫ y,p (T-r) y*reverseTest (p (T-r)) f y*k (r-s) y) at he
  rw [he] at hd
  exact hd.div_const (p (T-s) x)
end Asakura.Chapter9
