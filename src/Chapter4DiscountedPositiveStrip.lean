import Chapter4SDEDiscountedConditional
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
theorem sde_discounted_positive_strip
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
    (hXa : ∀ t,t<⊤ → Measurable[F t] (X t))
    (hXc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
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
    (k g : ℝ × (Fin dim → ℝ) → ℝ) (hk : Continuous k) (hg : Continuous g)
    (hkpos : ∀ r∈Icc 0 R,∀ x,0≤k (t-r,x))
    (hpde : ∀ᵐ w ∂P,∀ r∈Icc 0 R,vt (t-r,X (realTimeClamp r) w)=
      (∑ i,fderiv ℝ (v (t-r)) (X (realTimeClamp r) w) (Pi.single i 1)*G i (realTimeClamp r) w)+
      (∑ i,∑ l,fderiv ℝ (fderiv ℝ (v (t-r))) (X (realTimeClamp r) w) (Pi.single i 1) (Pi.single l 1)*
        (∑ j,H i j (realTimeClamp r) w*H l j (realTimeClamp r) w))/2+
      g (t-r,X (realTimeClamp r) w)-k (t-r,X (realTimeClamp r) w)*v (t-r) (X (realTimeClamp r) w))
    (L : Ω → ℝ) (hL : MemLp L 2 P)
    (hb : ∀ᵐ w ∂P,∀ r∈Icc 0 R,|v (t-r) (X (realTimeClamp r) w)|≤L w ∧ |g (t-r,X (realTimeClamp r) w)|≤L w)
    (s : ℝ) (hs : s∈Icc 0 R) :
    let V := fun r w => v (t-r) (X (realTimeClamp r) w)*discountFactor (fun a => k (t-a,X (realTimeClamp a) w)) r+
      ∫ a in 0..r,g (t-a,X (realTimeClamp a) w)*discountFactor (fun b => k (t-b,X (realTimeClamp b) w)) a
    P[V R | F (realTimeClamp s)]=ᵐ[P] V s := by
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
        (∑ j,H i j (realTimeClamp r) w*H l j (realTimeClamp r) w))/2=
        k (t-r,X (realTimeClamp r) w)*f r (X (realTimeClamp r) w)-g (t-r,X (realTimeClamp r) w) := by
    filter_upwards [hpde] with w hw
    intro r hr
    have hx := heu (t-r) (by linarith [hr.2]) (X (realTimeClamp r) w)
    dsimp only [ft,f]
    rw [hx.2.1,hx.2.2.1,hx.2.2.2,hx.1]
    linarith [hw r hr]
  have hfb : ∀ᵐ w ∂P,∀ r∈Icc 0 R,|f r (X (realTimeClamp r) w)|≤L w ∧ |g (t-r,X (realTimeClamp r) w)|≤L w := by
    filter_upwards [hb] with w hw
    intro r hr
    rw [show f r (X (realTimeClamp r) w)=v (t-r) (X (realTimeClamp r) w) from
      (heu (t-r) (by linarith [hr.2]) _).1]
    exact hw r hr
  have hh := sde_discounted_conditional_constructed P hT F hF hle hnull W B hW hB hclock X ξ hξ hXa hXc G H N
    hGa hGc hN hHa hHc hNI R hR hRT he f ft (fun r => hu (t-r)) hfd
    (huc.comp hmap) ((hutc.comp hmap).neg) (hdu.comp hmap) (hhu.comp hmap)
    (fun z => k (t-z.1,z.2)) (fun z => g (t-z.1,z.2)) (hk.comp hmap) (hg.comp hmap) hkpos hpe L hL hfb s hs
  have hRval x : f R x=v (t-R) x := (heu (t-R) le_rfl x).1
  have hsval x : f s x=v (t-s) x := (heu (t-s) (by linarith [hs.2]) x).1
  dsimp only at hh ⊢
  simpa only [hRval,hsval] using hh

end Asakura.Chapter4
