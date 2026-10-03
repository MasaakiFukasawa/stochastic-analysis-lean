import Chapter13NormalizedDensity

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem closed_numeraire_martingale {Ω ι:Type*} {m:MeasurableSpace Ω} [Preorder ι]
    (P:Measure Ω) [IsProbabilityMeasure P]
    (F:ι → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (Z:Ω → ℝ) (hZm:Measurable Z) (hZi:Integrable Z P) (hZp:∀ᵐw∂P,0<Z w)
    (N:ι → Ω → ℝ) (hNm:∀t,StronglyMeasurable[F t] (N t))
    (hN:∀t,P[Z|F t]=ᵐ[P] N t)
    (Y:ι → Ω → ℝ) (hYm:∀t,StronglyMeasurable[F t] (Y t)) (hYi:∀t,Integrable (Y t) P)
    (hY:∀s t,s≤t → P[Y t|F s]=ᵐ[P] Y s) :
    let c:=∫w,Z w∂P
    let Q:=P.withDensity (fun w => ENNReal.ofReal (Z w/c))
    IsProbabilityMeasure Q ∧ (∀t,Integrable (fun w => Y t w/N t w) Q) ∧
    (∀s t,s≤t → Q[(fun w => Y t w/N t w)|F s]=ᵐ[Q] (fun w => Y s w/N s w)) := by
  letI:MeasurableSpace Ω := m
  intro c Q
  obtain ⟨hc,hDm,hDi,hDp,hDone,hQ⟩ := normalized_density_probability P Z hZm hZi hZp
  let D:=fun w => Z w/c
  let V:=fun t w => c⁻¹*Y t w
  have hVi t:Integrable (V t) P := (hYi t).const_mul c⁻¹
  have hV:∀s t,s≤t → P[V t|F s]=ᵐ[P] V s := by
    intro s t hst
    have h:=condExp_smul (μ:=P) c⁻¹ (Y t) (F s)
    filter_upwards [h,hY s t hst] with w hw hy
    change P[V t|F s] w=c⁻¹*P[Y t|F s] w at hw
    rw [hw,hy]
  obtain ⟨_,hi,hm⟩ := numeraire_martingale P F hF hle D hDm hDi hDp hDone V
    (fun t => stronglyMeasurable_const.mul (hYm t)) hVi hV
  have he t:(fun w => V t w/P[D|F t] w)=ᵐ[P] (fun w => Y t w/N t w) := by
    have h:=condExp_smul (μ:=P) c⁻¹ Z (F t)
    have hDe:D=(fun w => c⁻¹*Z w) := by funext w;dsimp [D];ring
    rw [hDe]
    filter_upwards [h,hN t] with w hw hn
    change P[(fun w => c⁻¹*Z w)|F t] w=c⁻¹*P[Z|F t] w at hw
    rw [hw,hn]
    dsimp [V]
    have hc0:c≠0 := ne_of_gt hc
    field_simp [hc0]
  have heQ t:(fun w => V t w/P[D|F t] w)=ᵐ[Q] (fun w => Y t w/N t w) :=
    (show Q≪P from withDensity_absolutelyContinuous P _).ae_eq (he t)
  refine ⟨hQ,fun t => (hi t).congr (heQ t),?_⟩
  intro s t hst
  exact (condExp_congr_ae (m:=F s) (heQ t)).symm.trans ((hm s t hst).trans (heQ s))
end Asakura.Chapter13
#print axioms Asakura.Chapter13.closed_numeraire_martingale
