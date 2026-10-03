import Chapter13ConditionalDensityRestriction
import Chapter6DensityProbability

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter6
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem numeraire_martingale {Ω ι:Type*} {m:MeasurableSpace Ω} [Preorder ι]
    (P:Measure Ω) [IsProbabilityMeasure P]
    (F:ι → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (D:Ω → ℝ) (hDm:Measurable D) (hDi:Integrable D P)
    (hDp:∀ᵐw∂P,0<D w) (hDone:(∫w,D w∂P)=1)
    (Y:ι → Ω → ℝ) (hYm:∀t,StronglyMeasurable[F t] (Y t)) (hYi:∀t,Integrable (Y t) P)
    (hY:∀s t,s≤t → P[Y t|F s]=ᵐ[P] Y s) :
    let Q:=P.withDensity (fun w => ENNReal.ofReal (D w))
    IsProbabilityMeasure Q ∧
    (∀t,Integrable (fun w => Y t w/P[D|F t] w) Q) ∧
    (∀s t,s≤t → Q[(fun w => Y t w/P[D|F t] w)|F s]=ᵐ[Q]
      (fun w => Y s w/P[D|F s] w)) := by
  letI:MeasurableSpace Ω := m
  let Q:=P.withDensity (fun w => ENNReal.ofReal (D w))
  have hQ:IsProbabilityMeasure Q := mean_one_density_probability P D hDi (hDp.mono (fun _ h => h.le)) hDone
  letI := hQ
  have hi t := density_div_conditional_integrable P (hle t) D hDi hDp (Y t) (hYm t) (hYi t)
  refine ⟨hQ,hi,?_⟩
  intro s t hst
  have hDX:Integrable (fun w => D w*(Y t w/P[D|F t] w)) P := by
    have hh := hi t
    apply (integrable_withDensity_iff_integrable_smul' (ENNReal.measurable_ofReal.comp hDm)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp at hh
    apply hh.congr
    filter_upwards [hDp] with w hw
    simp only [Function.comp_def,ENNReal.toReal_ofReal hw.le,smul_eq_mul]
  have hCE := unbounded_pullout_right P (hle t) D (fun w => Y t w/P[D|F t] w)
    ((hYm t).div stronglyMeasurable_condExp) hDX hDi
  have hz := exercise_ce_strictly_positive P (hle t) hDi hDp
  have he:P[(fun w => D w*(Y t w/P[D|F t] w))|F t]=ᵐ[P] Y t := by
    filter_upwards [hCE,hz] with w hw hp
    change P[(fun w => D w*(Y t w/P[D|F t] w))|F t] w= P[D|F t] w*(Y t w/P[D|F t] w) at hw
    rw [hw]
    field_simp
  have hc := condExp_congr_ae (m:=F s) he
  have ht := condExp_condExp_of_le (hF hst) (hle t) (f:=fun w => D w*(Y t w/P[D|F t] w)) (μ:=P)
  have hb := bayes_real_density P Q (hle s) D hDm hDi hDp rfl _ (hi t)
  have hae:Q[(fun w => Y t w/P[D|F t] w)|F s]=ᵐ[P] (fun w => Y s w/P[D|F s] w) := by
    filter_upwards [hb,hc,ht,hY s t hst] with w hb hc ht hy
    rw [hb,←ht,hc,hy]
  exact (show Q≪P from withDensity_absolutelyContinuous P _).ae_eq hae
end Asakura.Chapter13
#print axioms Asakura.Chapter13.numeraire_martingale
