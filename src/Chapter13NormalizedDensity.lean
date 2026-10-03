import Chapter13Numeraire

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem positive_density_mean {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] (Z:Ω → ℝ) (hi:Integrable Z P)
    (hp:∀ᵐw∂P,0<Z w) : 0<∫w,Z w∂P := by
  have hn := integral_nonneg_of_ae (hp.mono (fun _ h => h.le))
  by_contra h
  have he:(∫w,Z w∂P)=0 := le_antisymm (not_lt.mp h) hn
  have hz := (integral_eq_zero_iff_of_nonneg_ae (hp.mono (fun _ h => h.le)) hi).mp he
  have hf:∀ᵐw∂P,False := by filter_upwards [hp,hz] with w hp hz;simp only [Pi.zero_apply] at hz;linarith
  have hh:P univ=0 := by simpa using ae_iff.mp hf
  simpa using hh

theorem normalized_density_probability {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] (Z:Ω → ℝ) (hm:Measurable Z) (hi:Integrable Z P)
    (hp:∀ᵐw∂P,0<Z w) :
    let c:=∫w,Z w∂P
    let D:=fun w => Z w/c
    0<c ∧ Measurable D ∧ Integrable D P ∧ (∀ᵐw∂P,0<D w) ∧
      (∫w,D w∂P)=1 ∧ IsProbabilityMeasure (P.withDensity (fun w => ENNReal.ofReal (D w))) := by
  intro c D
  have hc:0<c := positive_density_mean P Z hi hp
  have hD:Integrable D P := hi.div_const c
  have hDp:∀ᵐw∂P,0<D w := hp.mono (fun w hw => div_pos hw hc)
  have he:(∫w,D w∂P)=1 := by
    simp only [D,div_eq_mul_inv,integral_mul_const]
    exact mul_inv_cancel₀ (ne_of_gt hc)
  exact ⟨hc,hm.div_const c,hD,hDp,he,Asakura.Chapter6.mean_one_density_probability P D hD (hDp.mono (fun _ h => h.le)) he⟩
end Asakura.Chapter13
#print axioms Asakura.Chapter13.normalized_density_probability
