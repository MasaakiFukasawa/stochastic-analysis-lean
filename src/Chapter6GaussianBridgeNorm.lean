import Chapter6IndependentResidualNorm

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_bridge_conditional_norm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (U V : Ω → Fin d → ℝ) (hUm : Measurable U) (hVm : Measurable V)
    (hUV : HasGaussianLaw (fun w => (U w,V w)) P)
    (s t : ℝ) (hs : 0≤s) (hst : s<t)
    (hU0 : ∀ i,(∫ w,U w i ∂P)=0) (hV0 : ∀ i,(∫ w,V w i ∂P)=0)
    (hUU : ∀ i j,cov[(fun w => U w i),(fun w => U w j);P]=if i=j then s else 0)
    (hVV : ∀ i j,cov[(fun w => V w i),(fun w => V w j);P]=if i=j then t else 0)
    (hUVc : ∀ i j,cov[(fun w => U w i),(fun w => V w j);P]=if i=j then s else 0) :
    ∀ᵐ w ∂P,P[(fun w => ‖WithLp.toLp 2 (V w-U w)‖)|MeasurableSpace.comap V inferInstance] w
      ≤(t-s)/t*‖WithLp.toLp 2 (V w)‖+Real.sqrt ((d:ℝ)*(t-s)) := by
  have ht : 0<t := lt_of_le_of_lt hs hst
  let R := fun w i => U w i-(s/t)*V w i
  obtain ⟨hR,hind,_,hR2⟩ := gaussian_bridge_residual P U V hUV s t ht hU0 hV0 hUU hVV hUVc
  have hn := (gaussian_vector_norm_bound P R hR (s*(t-s)/t) hR2).2
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hRe : HasGaussianLaw (fun w => e (R w)) P := hR.map_equiv e
  have hVe : HasGaussianLaw (fun w => e (V w)) P := hUV.snd.map_equiv e
  have hrm : Measurable R := hUm.sub (hVm.const_smul (s/t))
  have heind : IndepFun (fun w => e (R w)) (fun w => e (V w)) P := hind.comp e.continuous.measurable e.continuous.measurable
  have hbound : (∫ w,‖e (R w)‖ ∂P)≤Real.sqrt ((d:ℝ)*(t-s)) := by
    apply hn.trans (Real.sqrt_le_sqrt _)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    apply (div_le_iff₀ ht).2
    nlinarith
  have hh := independent_residual_conditional_norm P (fun w => e (R w)) (fun w => e (V w))
    (e.continuous.measurable.comp hrm) (e.continuous.measurable.comp hVm)
    hRe.memLp_two hVe.memLp_two heind ((t-s)/t) (Real.sqrt ((d:ℝ)*(t-s)))
    (div_nonneg (sub_nonneg.mpr hst.le) ht.le) hbound
  have hcomap : MeasurableSpace.comap (fun w => e (V w)) inferInstance=MeasurableSpace.comap V inferInstance := by
    rw [show (fun w => e (V w))=e ∘ V from rfl,←MeasurableSpace.comap_comp]
    have hc : MeasurableSpace.comap e inferInstance=(inferInstance : MeasurableSpace (Fin d → ℝ)) :=
      e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comap_eq
    rw [hc]
  have heq : (fun w => ((t-s)/t) • e (V w)-e (R w))=(fun w => WithLp.toLp 2 (V w-U w)) := by
    funext w
    apply WithLp.ofLp_injective
    funext i
    change (t-s)/t*V w i-(U w i-s/t*V w i)=V w i-U w i
    field_simp [ht.ne']
    ring
  rw [hcomap] at hh
  have heqn : (fun w => ‖((t-s)/t) • e (V w)-e (R w)‖)=(fun w => ‖WithLp.toLp 2 (V w-U w)‖) := congrArg (fun f => fun w => ‖f w‖) heq
  rw [heqn] at hh
  simpa only [e,PiLp.continuousLinearEquiv_symm_apply] using hh

end Asakura.Chapter6
