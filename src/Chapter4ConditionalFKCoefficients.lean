import Chapter4ConditionalFeynmanKac

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's conditional Feynman--Kac formula, with continuous
coefficients evaluated on the actual vector SDE and the printed generator. -/
theorem conditional_feynman_kac_coefficients
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W : Fin noise → ClosedTime T → Ω → ℝ)
    (B : Fin noise → Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hB : ∀ j k,LocalCovarianceWitness P F (W j) (W k) (B j k))
    (hclock : ∀ j k w (r : ℝ),0≤r → (r:EReal)<T → B j k (realTimeClamp r) w=if j=k then r else 0)
    (X : ClosedTime T → Ω → Fin dim → ℝ) (ξ : Ω → Fin dim → ℝ)
    (hξ : Measurable[F ⊥] ξ)
    (hXa : ∀ r,r<⊤ → Measurable[F r] (X r))
    (hXc : ∀ w r,r<⊤ → ContinuousAt (fun u => X u w) r)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ)
    (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j))
    (N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => σ i j (X (realTimeClamp z.2) z.1)) (N i j))
    (t : ℝ) (ht : 0≤t) (htT : (t:EReal)<T)
    (he : ∀ᵐ w ∂P,∀ r∈Icc 0 t,∀ i,X (realTimeClamp r) w i=
      ξ w i+(∫ s in 0..r,μ i (X (realTimeClamp s) w))+∑ j,N i j (realTimeClamp r) w)
    (v : ℝ → (Fin dim → ℝ) → ℝ) (vt : ℝ × (Fin dim → ℝ) → ℝ)
    (hv : ∀ a,0<a → ContDiff ℝ 2 (v a))
    (hvt : ∀ a,0<a → ∀ x,HasDerivAt (fun s => v s x) (vt (a,x)) a)
    (hvc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => v z.1 z.2) {z | 0≤z.1})
    (hvtc : ContinuousOn vt {z | 0<z.1})
    (hdxc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (v z.1) z.2) {z | 0<z.1})
    (hhc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (v z.1)) z.2) {z | 0<z.1})
    (hpde : ∀ a,0<a → ∀ x,vt (a,x)=
      (∑ i,fderiv ℝ (v a) x (Pi.single i 1)*μ i x)+
      (∑ i,∑ l,fderiv ℝ (fderiv ℝ (v a)) x (Pi.single i 1) (Pi.single l 1)*(∑ j,σ i j x*σ l j x))/2)
    (K : ℝ) (hb : ∀ a∈Icc 0 t,∀ x,|v a x|≤K)
    (s : ℝ) (hs : s∈Icc 0 t) :
    P[(fun w => v 0 (X (realTimeClamp t) w)) | F (realTimeClamp s)]=ᵐ[P]
      fun w => v (t-s) (X (realTimeClamp s) w) := by
  exact conditional_feynman_kac_constructed P hT F hF hle hnull W B hW hB hclock X ξ hξ hXa hXc
    (fun i r w => μ i (X r w)) (fun i j r w => σ i j (X r w)) N
    (fun i r hr => (hμ i).measurable.comp (hXa r hr))
    (fun i w r hr => (hμ i).continuousAt.comp (hXc w r hr)) hN
    (fun i j r hr => (hσ i j).measurable.comp (hXa r hr))
    (fun i j w r hr => (hσ i j).continuousAt.comp (hXc w r hr)) hNI
    t ht htT he v vt hv hvt hvc hvtc hdxc hhc
    (ae_of_all _ fun w r hr => hpde (t-r) (sub_pos.mpr hr.2) _) K hb s hs

/-- Taking expectations at a deterministic initial state identifies the
PDE solution with the transition expectation; no triviality assumption
on the initial sigma algebra is needed. -/
theorem transition_value_of_conditional_formula
    {Ω E : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G≤m) (Y : Ω → ℝ) (X₀ : Ω → E)
    (x : E) (v : E → ℝ) (hx : X₀=ᵐ[P] fun _ => x)
    (he : P[Y | G]=ᵐ[P] fun w => v (X₀ w)) : v x=∫ w,Y w ∂P := by
  have hh : P[Y | G]=ᵐ[P] fun _ => v x := he.trans (hx.mono fun w hw => congrArg v hw)
  have hi := integral_congr_ae hh
  rw [integral_condExp hG] at hi
  simpa only [integral_const,probReal_univ,one_smul] using hi.symm

end Asakura.Chapter4
