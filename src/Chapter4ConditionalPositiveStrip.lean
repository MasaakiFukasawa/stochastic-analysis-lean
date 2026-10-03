import Chapter4SDEHarmonicConditional
import Chapter4C12PositiveExtension

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Apply the actual vector SDE formula before the terminal time. Only
positive-time C1,2 regularity is required. -/
theorem sde_conditional_positive_strip
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
    (G : Fin dim → ClosedTime T → Ω → ℝ)
    (H N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hGa : ∀ i t,t<⊤ → Measurable[F t] (G i t))
    (hGc : ∀ i w t,t<⊤ → ContinuousAt (fun s => G i s w) t)
    (hN : ∀ i j,LocalMProcessWitness P F (N i j))
    (hHa : ∀ i j t,t<⊤ → Measurable[F t] (H i j t))
    (hHc : ∀ i j w t,t<⊤ → ContinuousAt (fun s => H i j s w) t)
    (hNI : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => H i j (realTimeClamp z.2) z.1) (N i j))
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (he : ∀ᵐ w ∂P,∀ r∈Icc 0 R,∀ i,X (realTimeClamp r) w i=
      ξ w i+(∫ s in 0..r,G i (realTimeClamp s) w)+∑ j,N i j (realTimeClamp r) w)
    (t : ℝ) (hRt : R<t)
    (v : ℝ → (Fin dim → ℝ) → ℝ) (vt : ℝ × (Fin dim → ℝ) → ℝ)
    (hv : ∀ a,0<a → ContDiff ℝ 2 (v a))
    (hvt : ∀ a,0<a → ∀ x,HasDerivAt (fun s => v s x) (vt (a,x)) a)
    (hvc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => v z.1 z.2) {z | 0<z.1})
    (hvtc : ContinuousOn vt {z | 0<z.1})
    (hdxc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (v z.1) z.2) {z | 0<z.1})
    (hhc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (v z.1)) z.2) {z | 0<z.1})
    (hpde : ∀ᵐ w ∂P,∀ r∈Icc 0 R,vt (t-r,X (realTimeClamp r) w)=
      (∑ i,fderiv ℝ (v (t-r)) (X (realTimeClamp r) w) (Pi.single i 1)*G i (realTimeClamp r) w)+
      (∑ i,∑ l,fderiv ℝ (fderiv ℝ (v (t-r))) (X (realTimeClamp r) w) (Pi.single i 1) (Pi.single l 1)*
        (∑ j,H i j (realTimeClamp r) w*H l j (realTimeClamp r) w))/2)
    (K : ℝ) (hb : ∀ a∈Icc 0 t,∀ x,|v a x|≤K)
    (s : ℝ) (hs : s∈Icc 0 R) :
    P[(fun w => v (t-R) (X (realTimeClamp R) w)) | F (realTimeClamp s)]=ᵐ[P]
      fun w => v (t-s) (X (realTimeClamp s) w) := by
  obtain ⟨u,ut,hu,hut,huc,hutc,hdu,hhu,heu⟩ := c12_positive_time_extension v vt hv hvt hvc hvtc hdxc hhc
    (t-R) (sub_pos.mpr hRt)
  let f := fun r x => u (t-r) x
  let ft := fun z : ℝ × (Fin dim → ℝ) => -ut (t-z.1,z.2)
  have hmap : Continuous (fun z : ℝ × (Fin dim → ℝ) => (t-z.1,z.2)) :=
    (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hfd r x : HasDerivAt (fun a => f a x) (ft (r,x)) r := by
    have hh := (hut (t-r) x).comp r ((hasDerivAt_const r t).sub (hasDerivAt_id r))
    simpa only [zero_sub,mul_neg,mul_one,f,ft,Function.comp_def] using hh
  have hpe : ∀ᵐ w ∂P,∀ r∈Icc 0 R,ft (r,X (realTimeClamp r) w)+
      (∑ i,fderiv ℝ (f r) (X (realTimeClamp r) w) (Pi.single i 1)*G i (realTimeClamp r) w)+
      (∑ i,∑ l,fderiv ℝ (fderiv ℝ (f r)) (X (realTimeClamp r) w) (Pi.single i 1) (Pi.single l 1)*
        (∑ j,H i j (realTimeClamp r) w*H l j (realTimeClamp r) w))/2=0 := by
    filter_upwards [hpde] with w hw
    intro r hr
    have hx := heu (t-r) (by linarith [hr.2]) (X (realTimeClamp r) w)
    dsimp only [ft,f]
    rw [hx.2.1,hx.2.2.1,hx.2.2.2]
    linarith [hw r hr]
  have hfb r (hr : r∈Icc 0 R) x : |f r x|≤K := by
    rw [show f r x=v (t-r) x from (heu (t-r) (by linarith [hr.2]) x).1]
    exact hb (t-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩ x
  have hh := sde_harmonic_conditional_constructed P hT F hF hle hnull W B hW hB hclock X ξ hξ G H N
    hGa hGc hN hHa hHc hNI R hR hRT he f ft (fun r => hu (t-r)) hfd
    (huc.comp hmap) ((hutc.comp hmap).neg) (hdu.comp hmap) (hhu.comp hmap) hpe K hfb s hs
  have hRval : (fun w => f R (X (realTimeClamp R) w))=(fun w => v (t-R) (X (realTimeClamp R) w)) :=
    funext (fun w => (heu (t-R) le_rfl _).1)
  have hsval : (fun w => f s (X (realTimeClamp s) w))=(fun w => v (t-s) (X (realTimeClamp s) w)) :=
    funext (fun w => (heu (t-s) (by linarith [hs.2]) _).1)
  rwa [hRval,hsval] at hh

end Asakura.Chapter4
