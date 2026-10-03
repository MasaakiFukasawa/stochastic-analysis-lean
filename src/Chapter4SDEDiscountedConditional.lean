import Chapter4SDEDriftRepresentation
import Chapter4DiscountedFunctionConditional

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- The actual vector SDE gives the generator drift and local martingale
representation of a C1,2 function on a closed time strip. -/
theorem sde_discounted_conditional_constructed
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
    (f : ℝ → (Fin dim → ℝ) → ℝ) (ft : ℝ × (Fin dim → ℝ) → ℝ)
    (hf : ∀ a,ContDiff ℝ 2 (f a))
    (hft : ∀ a x,HasDerivAt (fun s => f s x) (ft (a,x)) a)
    (hfc : Continuous (fun z : ℝ × (Fin dim → ℝ) => f z.1 z.2)) (hftc : Continuous ft)
    (hdxc : Continuous (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (f z.1) z.2))
    (hhc : Continuous (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (f z.1)) z.2))
    (k g : ℝ × (Fin dim → ℝ) → ℝ) (hk : Continuous k) (hg : Continuous g)
    (hkpos : ∀ r∈Icc 0 R,∀ x,0≤k (r,x))
    (hpde : ∀ᵐ w ∂P,∀ r∈Icc 0 R,ft (r,X (realTimeClamp r) w)+
      (∑ i,fderiv ℝ (f r) (X (realTimeClamp r) w) (Pi.single i 1)*G i (realTimeClamp r) w)+
      (∑ i,∑ l,fderiv ℝ (fderiv ℝ (f r)) (X (realTimeClamp r) w) (Pi.single i 1) (Pi.single l 1)*
        (∑ j,H i j (realTimeClamp r) w*H l j (realTimeClamp r) w))/2=k (r,X (realTimeClamp r) w)*f r (X (realTimeClamp r) w)-g (r,X (realTimeClamp r) w))
    (L : Ω → ℝ) (hL : MemLp L 2 P)
    (hb : ∀ᵐ w ∂P,∀ r∈Icc 0 R,|f r (X (realTimeClamp r) w)|≤L w ∧ |g (r,X (realTimeClamp r) w)|≤L w)
    (s : ℝ) (hs : s∈Icc 0 R) :
    let V := fun r w => f r (X (realTimeClamp r) w)*discountFactor (fun a => k (a,X (realTimeClamp a) w)) r+
      ∫ a in 0..r,g (a,X (realTimeClamp a) w)*discountFactor (fun b => k (b,X (realTimeClamp b) w)) a
    P[V R | F (realTimeClamp s)]=ᵐ[P] V s := by
  obtain ⟨Z,hZ,hZe⟩ := sde_drift_representation_constructed P hT F hF hle hnull W B hW hB hclock X ξ hξ
    G H N hGa hGc hN hHa hHc hNI R hR hRT he f ft hf hft hfc hftc hdxc hhc
    (fun z => k (z.2,X (realTimeClamp z.2) z.1)*f z.2 (X (realTimeClamp z.2) z.1)-g (z.2,X (realTimeClamp z.2) z.1)) hpde
  exact discounted_function_conditional P hT F hF hle hnull X hXa hXc
    (fun z => f z.1 z.2) k g hfc hk hg R hR hRT hkpos L hL hb Z hZ hZe s hs

end Asakura.Chapter4
