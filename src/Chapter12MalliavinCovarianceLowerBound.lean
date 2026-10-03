import Chapter12AdjointInverseBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The manuscript's lower bound is obtained by integrating the ellipticity
bound and the inverse variational-flow estimate. -/
theorem malliavin_covariance_integral_lower_bound {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : F →L[ℝ] E) (J : ℝ → E ≃L[ℝ] E) (K T ell : ℝ) (hT : 0≤T) (hell : 0≤ell)
    (hA : ∀ v : E,ell*‖v‖^2≤‖ContinuousLinearMap.adjoint A v‖^2)
    (hJ : ∀ s∈Ioc (0:ℝ) T,‖(J s).symm.toContinuousLinearMap‖≤Real.exp (K*T))
    (v : E)
    (hi : IntegrableOn (fun s => ‖ContinuousLinearMap.adjoint A
      (ContinuousLinearMap.adjoint (J s).toContinuousLinearMap v)‖^2) (Ioc (0:ℝ) T)) :
    ell*T*Real.exp (-2*K*T)*‖v‖^2≤
      ∫ s in Ioc (0:ℝ) T,‖ContinuousLinearMap.adjoint A
        (ContinuousLinearMap.adjoint (J s).toContinuousLinearMap v)‖^2 := by
  let c := ell*Real.exp (-2*K*T)*‖v‖^2
  have hp : ∀ s∈Ioc (0:ℝ) T,c≤‖ContinuousLinearMap.adjoint A
      (ContinuousLinearMap.adjoint (J s).toContinuousLinearMap v)‖^2 := by
    intro s hs
    have hh := adjoint_square_lower_of_exponential_inverse_bound (J s) K T (hJ s hs) v
    have hs : c≤ell*‖ContinuousLinearMap.adjoint (J s).toContinuousLinearMap v‖^2 := by
      simpa only [c,mul_assoc] using mul_le_mul_of_nonneg_left hh hell
    exact hs.trans (hA _)
  have hh : (∫ _ : ℝ in Ioc (0:ℝ) T,c)≤∫ s in Ioc (0:ℝ) T,
      ‖ContinuousLinearMap.adjoint A (ContinuousLinearMap.adjoint (J s).toContinuousLinearMap v)‖^2 := by
    apply integral_mono_ae (integrable_const c) hi
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hp s hs
  rw [integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
    sub_zero,ENNReal.toReal_ofReal hT] at hh
  convert hh using 1 <;> dsimp only [c] <;> ring

end Asakura.Chapter12
