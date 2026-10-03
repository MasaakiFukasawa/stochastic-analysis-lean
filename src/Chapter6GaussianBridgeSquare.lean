import Chapter6IndependentResidualSquare
import Chapter6GaussianBridgeNorm

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_bridge_conditional_square_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (U V : Ω → Fin d → ℝ) (hUm : Measurable U) (hVm : Measurable V)
    (hUV : HasGaussianLaw (fun w => (U w,V w)) P)
    (s t : ℝ) (hs : 0≤s) (hst : s<t)
    (hU0 : ∀ i,(∫ w,U w i ∂P)=0) (hV0 : ∀ i,(∫ w,V w i ∂P)=0)
    (hUU : ∀ i j,cov[(fun w => U w i),(fun w => U w j);P]=if i=j then s else 0)
    (hVV : ∀ i j,cov[(fun w => V w i),(fun w => V w j);P]=if i=j then t else 0)
    (hUVc : ∀ i j,cov[(fun w => U w i),(fun w => V w j);P]=if i=j then s else 0) :
    (∀ᵐ w ∂P,P[(fun w => ‖WithLp.toLp 2 (U w)‖^2)|MeasurableSpace.comap V inferInstance] w
      ≤2*(s/t)^2*‖WithLp.toLp 2 (V w)‖^2+2*(d:ℝ)*(s*(t-s)/t)) ∧
    (∀ᵐ w ∂P,P[(fun w => ‖WithLp.toLp 2 (V w-U w)‖^2)|MeasurableSpace.comap V inferInstance] w
      ≤2*((t-s)/t)^2*‖WithLp.toLp 2 (V w)‖^2+2*(d:ℝ)*(s*(t-s)/t)) := by
  have ht : 0<t := lt_of_le_of_lt hs hst
  let R := fun w i => U w i-(s/t)*V w i
  obtain ⟨hR,hind,_,hR2⟩ := gaussian_bridge_residual P U V hUV s t ht hU0 hV0 hUU hVV hUVc
  have hn := gaussian_vector_square_moment P R hR (s*(t-s)/t) hR2
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hRe : HasGaussianLaw (fun w => e (R w)) P := hR.map_equiv e
  have hVe : HasGaussianLaw (fun w => e (V w)) P := hUV.snd.map_equiv e
  have hrm : Measurable R := hUm.sub (hVm.const_smul (s/t))
  have herm : Measurable (fun w => e (R w)) := e.continuous.measurable.comp hrm
  have hevm : Measurable (fun w => e (V w)) := e.continuous.measurable.comp hVm
  have heind : IndepFun (fun w => e (R w)) (fun w => e (V w)) P := hind.comp e.continuous.measurable e.continuous.measurable
  have heindneg : IndepFun (fun w => -e (R w)) (fun w => e (V w)) P := heind.comp measurable_neg measurable_id
  have hU := independent_residual_conditional_square P (fun w => -e (R w)) (fun w => e (V w))
    herm.neg hevm hRe.memLp_two.neg hVe.memLp_two heindneg (s/t)
  have hD := independent_residual_conditional_square P (fun w => e (R w)) (fun w => e (V w))
    herm hevm hRe.memLp_two hVe.memLp_two heind ((t-s)/t)
  have hcomap : MeasurableSpace.comap (fun w => e (V w)) inferInstance=MeasurableSpace.comap V inferInstance := by
    rw [show (fun w => e (V w))=e ∘ V from rfl,←MeasurableSpace.comap_comp]
    have hc : MeasurableSpace.comap e inferInstance=(inferInstance : MeasurableSpace (Fin d → ℝ)) :=
      e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comap_eq
    rw [hc]
  have heU w : (s/t) • e (V w)-(-e (R w))=WithLp.toLp 2 (U w) := by
    apply WithLp.ofLp_injective
    funext i
    change s/t*V w i-(-(U w i-s/t*V w i))=U w i
    ring
  have heD w : ((t-s)/t) • e (V w)-e (R w)=WithLp.toLp 2 (V w-U w) := by
    apply WithLp.ofLp_injective
    funext i
    change (t-s)/t*V w i-(U w i-s/t*V w i)=V w i-U w i
    field_simp [ht.ne']
    ring
  change ∀ᵐ w ∂P, P[(fun w => ‖(s/t) • e (V w)-(-e (R w))‖^2)|MeasurableSpace.comap (fun w => e (V w)) inferInstance] w ≤ 2*(s/t)^2*‖e (V w)‖^2+2*∫ w, ‖-e (R w)‖^2 ∂P at hU
  simp only [heU,hcomap,norm_neg] at hU
  simp only [e,PiLp.continuousLinearEquiv_symm_apply,hn] at hU
  change ∀ᵐ w ∂P, P[(fun w => ‖((t-s)/t) • e (V w)-e (R w)‖^2)|MeasurableSpace.comap (fun w => e (V w)) inferInstance] w ≤ 2*((t-s)/t)^2*‖e (V w)‖^2+2*∫ w, ‖e (R w)‖^2 ∂P at hD
  simp only [heD,hcomap] at hD
  simp only [e,PiLp.continuousLinearEquiv_symm_apply,hn] at hD
  constructor
  · simpa only [mul_assoc] using hU
  · simpa only [mul_assoc] using hD

end Asakura.Chapter6
