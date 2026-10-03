import Chapter6BridgeSquareCoarse
import Chapter6ConditionalLinearGrowth

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_bridge_linear_growth_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (U V : Ω → Fin d → ℝ) (hUm : Measurable U) (hVm : Measurable V)
    (hUV : HasGaussianLaw (fun w => (U w,V w)) P)
    (s t : ℝ) (hs : 0≤s) (hst : s<t)
    (hU0 : ∀ i,(∫ w,U w i ∂P)=0) (hV0 : ∀ i,(∫ w,V w i ∂P)=0)
    (hUU : ∀ i j,cov[(fun w => U w i),(fun w => U w j);P]=if i=j then s else 0)
    (hVV : ∀ i j,cov[(fun w => V w i),(fun w => V w j);P]=if i=j then t else 0)
    (hUVc : ∀ i j,cov[(fun w => U w i),(fun w => V w j);P]=if i=j then s else 0)
    (b : (Fin d → ℝ) → Fin d → ℝ) (hb : Measurable b) (K : ℝ) (hK : 0≤K)
    (hbb : ∀ y,‖WithLp.toLp 2 (b y)‖≤K*(1+‖WithLp.toLp 2 y‖)) :
    (∀ᵐ w ∂P,P[(fun w => ‖WithLp.toLp 2 (b (U w))‖^2)|MeasurableSpace.comap V inferInstance] w
      ≤2*K^2*(3+2*(d:ℝ)*t)*(1+‖WithLp.toLp 2 (V w)‖^2)) ∧
    (∀ᵐ w ∂P,P[(fun w => ‖WithLp.toLp 2 (V w-U w)‖^2)|MeasurableSpace.comap V inferInstance] w
      ≤(2/t+2*(d:ℝ))*(1+‖WithLp.toLp 2 (V w)‖^2)*(t-s)) := by
  obtain ⟨hu,hv⟩ := gaussian_bridge_conditional_square_bounds P U V hUm hVm hUV s t hs hst hU0 hV0 hUU hVV hUVc
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hue : HasGaussianLaw (fun w => e (U w)) P := hUV.fst.map_equiv e
  let b' := fun y => e (b (e.symm y))
  have hbm : Measurable b' := e.continuous.measurable.comp (hb.comp e.symm.continuous.measurable)
  have hbb' y : ‖b' y‖≤K*(1+‖y‖) := by
    have hh := hbb (e.symm y)
    change ‖e (b (e.symm y))‖≤K*(1+‖e (e.symm y)‖) at hh
    rw [e.apply_symm_apply] at hh
    exact hh
  have hc := conditional_linear_growth_square P (fun w => e (U w)) b' hue.memLp_two
    (hbm.comp (e.continuous.measurable.comp hUm)).aestronglyMeasurable K hK hbb'
    (MeasurableSpace.comap V inferInstance) hVm.comap_le
  have hbe w : b' (e (U w))=WithLp.toLp 2 (b (U w)) := by
    dsimp only [b']
    rw [e.symm_apply_apply]
    rfl
  simp only [hbe] at hc
  simp only [e,PiLp.continuousLinearEquiv_symm_apply] at hc
  constructor
  · filter_upwards [hu,hc] with w hu hc
    have hz := sq_nonneg ‖WithLp.toLp 2 (V w)‖
    have hco := (bridge_square_coarse_bounds s t (‖WithLp.toLp 2 (V w)‖^2) d hs hst hz (Nat.cast_nonneg d)).1
    have hm := mul_le_mul_of_nonneg_left (hu.trans hco) (show 0≤2*K^2 by positivity)
    have hh : 1+(2+2*(d:ℝ)*t)*(1+‖WithLp.toLp 2 (V w)‖^2)≤(3+2*(d:ℝ)*t)*(1+‖WithLp.toLp 2 (V w)‖^2) := by nlinarith
    have hh' := mul_le_mul_of_nonneg_left hh (show 0≤2*K^2 by positivity)
    nlinarith
  · filter_upwards [hv] with w hv
    exact hv.trans (bridge_square_coarse_bounds s t (‖WithLp.toLp 2 (V w)‖^2) d hs hst (sq_nonneg _) (Nat.cast_nonneg d)).2

end Asakura.Chapter6
