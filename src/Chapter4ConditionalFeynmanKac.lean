import Chapter4ConditionalPositiveStrip
import Chapter4ConditionalTerminalLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- Conditional Feynman--Kac from the actual vector SDE, with precisely
positive-time C1,2 regularity and continuity at time zero. -/
theorem conditional_feynman_kac_constructed
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
    (G : Fin dim → ClosedTime T → Ω → ℝ)
    (H N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hGa : ∀ i t,t<⊤ → Measurable[F t] (G i t))
    (hGc : ∀ i w t,t<⊤ → ContinuousAt (fun s => G i s w) t)
    (hN : ∀ i j,LocalMProcessWitness P F (N i j))
    (hHa : ∀ i j t,t<⊤ → Measurable[F t] (H i j t))
    (hHc : ∀ i j w t,t<⊤ → ContinuousAt (fun s => H i j s w) t)
    (hNI : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => H i j (realTimeClamp z.2) z.1) (N i j))
    (t : ℝ) (ht : 0≤t) (htT : (t:EReal)<T)
    (he : ∀ᵐ w ∂P,∀ r∈Icc 0 t,∀ i,X (realTimeClamp r) w i=
      ξ w i+(∫ s in 0..r,G i (realTimeClamp s) w)+∑ j,N i j (realTimeClamp r) w)
    (v : ℝ → (Fin dim → ℝ) → ℝ) (vt : ℝ × (Fin dim → ℝ) → ℝ)
    (hv : ∀ a,0<a → ContDiff ℝ 2 (v a))
    (hvt : ∀ a,0<a → ∀ x,HasDerivAt (fun s => v s x) (vt (a,x)) a)
    (hvc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => v z.1 z.2) {z | 0≤z.1})
    (hvtc : ContinuousOn vt {z | 0<z.1})
    (hdxc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (v z.1) z.2) {z | 0<z.1})
    (hhc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (v z.1)) z.2) {z | 0<z.1})
    (hpde : ∀ᵐ w ∂P,∀ r∈Ico 0 t,vt (t-r,X (realTimeClamp r) w)=
      (∑ i,fderiv ℝ (v (t-r)) (X (realTimeClamp r) w) (Pi.single i 1)*G i (realTimeClamp r) w)+
      (∑ i,∑ l,fderiv ℝ (fderiv ℝ (v (t-r))) (X (realTimeClamp r) w) (Pi.single i 1) (Pi.single l 1)*
        (∑ j,H i j (realTimeClamp r) w*H l j (realTimeClamp r) w))/2)
    (K : ℝ) (hb : ∀ a∈Icc 0 t,∀ x,|v a x|≤K)
    (s : ℝ) (hs : s∈Icc 0 t) :
    P[(fun w => v 0 (X (realTimeClamp t) w)) | F (realTimeClamp s)]=ᵐ[P]
      fun w => v (t-s) (X (realTimeClamp s) w) := by
  have hvcont a (ha : 0≤a) : Continuous (v a) :=
    hvc.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ha)
  have hsm : Measurable[F (realTimeClamp s)] (fun w => v (t-s) (X (realTimeClamp s) w)) :=
    (hvcont (t-s) (sub_nonneg.mpr hs.2)).measurable.comp (hXa _ (real_time_below s hs.1 ((EReal.coe_le_coe hs.2).trans_lt htT)))
  have hVi : Integrable (fun w => v (t-s) (X (realTimeClamp s) w)) P :=
    Integrable.of_bound (hsm.mono (hle _) le_rfl).aestronglyMeasurable K
      (ae_of_all _ fun w => hb (t-s) ⟨sub_nonneg.mpr hs.2,by linarith [hs.1]⟩ _)
  rcases hs.2.eq_or_lt with hst | hst
  · subst s
    simpa only [sub_self] using Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable (hle _) (by simpa only [sub_self] using hsm.stronglyMeasurable)
        (by simpa only [sub_self] using hVi))
  let Z := fun r w => v (t-r) (X (realTimeClamp r) w)
  have hZm r (hr : r∈Icc s t) : AEStronglyMeasurable[m] (Z r) P :=
    ((hvcont (t-r) (sub_nonneg.mpr hr.2)).measurable.comp
      ((hXa _ (real_time_below r (hs.1.trans hr.1) ((EReal.coe_le_coe hr.2).trans_lt htT))).mono (hle _) le_rfl)).aestronglyMeasurable
  have hZc w : ContinuousOn (fun r => Z r w) (Icc s t) := by
    change ContinuousOn ((fun z : ℝ × (Fin dim → ℝ) => v z.1 z.2) ∘
      (fun r => (t-r,X (realTimeClamp r) w))) (Icc s t)
    apply hvc.comp
    · apply (continuous_const.sub continuous_id).continuousOn.prodMk
      intro r hr
      exact ((hXc w _ (real_time_below r (hs.1.trans hr.1) ((EReal.coe_le_coe hr.2).trans_lt htT))).comp
        real_time_clamp_continuous.continuousAt).continuousWithinAt
    · intro r hr
      exact sub_nonneg.mpr hr.2
  have hZb r (hr : r∈Icc s t) w : |Z r w|≤K :=
    hb (t-r) ⟨sub_nonneg.mpr hr.2,by linarith [hs.1,hr.1]⟩ _
  have hpre r (hr : r∈Ico s t) : P[Z r | F (realTimeClamp s)]=ᵐ[P]
      fun w => v (t-s) (X (realTimeClamp s) w) := by
    apply sde_conditional_positive_strip P hT F hF hle hnull W B hW hB hclock X ξ hξ G H N
      hGa hGc hN hHa hHc hNI r (hs.1.trans hr.1) ((EReal.coe_lt_coe hr.2).trans htT)
      (he.mono fun w hw a ha => hw a ⟨ha.1,ha.2.trans hr.2.le⟩) t hr.2 v vt hv hvt
      (hvc.mono fun z hz => show 0≤z.1 from le_of_lt hz) hvtc hdxc hhc
      (hpde.mono fun w hw a ha => hw a ⟨ha.1,ha.2.trans_lt hr.2⟩) K hb s ⟨hs.1,hr.1⟩
  have hh := bounded_conditional_terminal_limit P (F (realTimeClamp s)) (hle _) Z
    (fun w => v (t-s) (X (realTimeClamp s) w)) s t K hst hZm hZc hZb hsm.stronglyMeasurable hVi hpre
  simpa only [Z,sub_self] using hh

end Asakura.Chapter4
