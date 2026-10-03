import Chapter13ClosedNumeraire

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem frozen_terminal_conditional {Ω ι:Type*} {m:MeasurableSpace Ω} [LinearOrder ι]
    (P:Measure Ω) [IsProbabilityMeasure P] (F:ι → MeasurableSpace Ω)
    (hF:Monotone F) (hle:∀t,F t≤m) (N:ι → Ω → ℝ)
    (hm:∀t,StronglyMeasurable[F t] (N t)) (hi:∀t,Integrable (N t) P)
    (hN:∀s t,s≤t → P[N t|F s]=ᵐ[P] N s) (τ:ι)
    (hf:∀t,τ≤t → N t=ᵐ[P] N τ) : ∀t,P[N τ|F t]=ᵐ[P] N t := by
  intro t
  rcases le_total t τ with h|h
  · exact hN t τ h
  · exact (Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (hle t)
      ((hm τ).mono (hF h)) (hi τ))).trans (hf t h).symm

theorem affine_martingale_identity {Ω ι:Type*} {m:MeasurableSpace Ω} [Preorder ι]
    (P:Measure Ω) [IsProbabilityMeasure P] (F:ι → MeasurableSpace Ω) (hle:∀t,F t≤m)
    (X:ι → Ω → ℝ) (hi:∀t,Integrable (X t) P)
    (hX:∀s t,s≤t → P[X t|F s]=ᵐ[P] X s) (a b:ℝ) :
    (∀t,Integrable (fun w => a*X t w+b) P) ∧
    (∀s t,s≤t → P[(fun w => a*X t w+b)|F s]=ᵐ[P] (fun w => a*X s w+b)) := by
  refine ⟨fun t => ((hi t).const_mul a).add (integrable_const b),?_⟩
  intro s t hst
  have h1:=condExp_add ((hi t).const_mul a) (integrable_const b) (F s)
  have h2:=condExp_smul (μ:=P) a (X t) (F s)
  have h3:=condExp_const (μ:=P) (hle s) b
  filter_upwards [h1,h2,hX s t hst] with w h1 h2 hx
  change P[(fun w => a*X t w+b)|F s] w=P[(fun w => a*X t w)|F s] w+P[(fun _ => b)|F s] w at h1
  change P[(fun w => a*X t w)|F s] w=a*P[X t|F s] w at h2
  rw [h1,h2,h3,hx]

theorem finite_annuity_conditional {Ω J:Type*} {G m:MeasurableSpace Ω} [Fintype J]
    (P:Measure Ω) [IsProbabilityMeasure P] (a:J → ℝ) (Z N:J → Ω → ℝ)
    (hi:∀j,Integrable (Z j) P) (he:∀j,P[Z j|G]=ᵐ[P] N j) :
    P[(fun w => ∑j,a j*Z j w)|G]=ᵐ[P] (fun w => ∑j,a j*N j w) := by
  have hs:=condExp_finsetSum (s:=Finset.univ) (fun j _ => (hi j).const_mul (a j)) G
  have hc j:=condExp_smul (μ:=P) (a j) (Z j) G
  filter_upwards [hs,ae_all_iff.mpr he,ae_all_iff.mpr hc] with w hs he hc
  simp only [Finset.sum_fn,Finset.sum_apply] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro j _
  have hj:=hc j
  change P[(fun w => a j*Z j w)|G] w=a j*P[Z j|G] w at hj
  rw [hj,he]
end Asakura.Chapter13
#print axioms Asakura.Chapter13.frozen_terminal_conditional
#print axioms Asakura.Chapter13.finite_annuity_conditional
