import Chapter12FiniteWienerKernelPairing
import Chapter12AdjointInverseBound

open MeasureTheory Set
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem kernel_covariance_lower_bound {E:Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (d:ℕ) (T K ell:ℝ) (hT:0≤T) (hK:0≤K) (hell:0≤ell)
    (v:Fin (d+1) → E) (hv:∀z:E,ell*‖z‖^2≤∑j,(inner ℝ z (v j))^2)
    (J Q:ℝ → E →L[ℝ] E) (hcQ:Continuous Q)
    (he:∀s∈Icc 0 T,∃e:E ≃L[ℝ] E,e.toContinuousLinearMap=J T*Q s ∧
      ‖e.symm.toContinuousLinearMap‖≤Real.exp (K*(T-s)))
    (z:E) (U:FiniteWienerHilbert d T)
    (hU:∀j,(brownianCoordinateProjection T j U:ℝ → ℝ)=ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
      (fun s => inner ℝ z (J T (Q s (v j))))) :
    ell*T*Real.exp (-2*K*T)*‖z‖^2≤‖U‖^2 := by
  let f := fun s => ∑j,(inner ℝ z (J T (Q s (v j))))^2
  have hfc:Continuous f := continuous_finsetSum _ (fun j _ =>
    (continuous_const.inner ((J T).continuous.comp (hcQ.clm_apply continuous_const))).pow 2)
  have hp s (hs:s∈Ioc 0 T):ell*Real.exp (-2*K*T)*‖z‖^2≤f s := by
    obtain ⟨e,heq,heb⟩ := he s ⟨hs.1.le,hs.2⟩
    have hb:‖e.symm.toContinuousLinearMap‖≤Real.exp (K*T) := heb.trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_self T hs.1.le) hK))
    have hn := adjoint_square_lower_of_exponential_inverse_bound e K T hb z
    have hl := (mul_le_mul_of_nonneg_left hn hell).trans (hv (ContinuousLinearMap.adjoint e.toContinuousLinearMap z))
    have hid j:inner ℝ (ContinuousLinearMap.adjoint e.toContinuousLinearMap z) (v j)=
        inner ℝ z (J T (Q s (v j))) := by
      rw [ContinuousLinearMap.adjoint_inner_left,heq]
      rfl
    simpa only [hid,mul_assoc] using hl
  have hn := finite_wiener_kernel_pairing T hT U U _ _ hU hU
  rw [real_inner_self_eq_norm_sq] at hn
  have hn':‖U‖^2=∫s in Ioc (0:ℝ) T,f s := by
    simpa only [pow_two,intervalIntegral.integral_of_le hT,f] using hn
  rw [hn']
  have hi:IntegrableOn f (Ioc (0:ℝ) T) :=
    (hfc.intervalIntegrable 0 T).1
  have h := integral_mono_ae (integrable_const (μ:=volume.restrict (Ioc (0:ℝ) T))
    (ell*Real.exp (-2*K*T)*‖z‖^2)) hi
    ((ae_restrict_mem measurableSet_Ioc).mono (fun s hs => hp s hs))
  rw [integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
    sub_zero,ENNReal.toReal_ofReal hT] at h
  convert h using 1 <;> ring
end Asakura.Chapter12
#print axioms Asakura.Chapter12.kernel_covariance_lower_bound
