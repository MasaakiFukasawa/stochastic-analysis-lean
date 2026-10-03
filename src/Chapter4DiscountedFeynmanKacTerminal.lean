import Chapter4DiscountedPositiveStrip
import Chapter4DominatedTerminalLimit
import Chapter4DiscountedProcessConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- Conditional Feynman--Kac from the actual vector SDE, with precisely
positive-time C1,2 regularity and continuity at time zero. -/
theorem discounted_feynman_kac_terminal_constructed
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
    (k g : ℝ × (Fin dim → ℝ) → ℝ) (hk : Continuous k) (hg : Continuous g)
    (hkpos : ∀ r∈Icc 0 t,∀ x,0≤k (t-r,x))
    (hpde : ∀ᵐ w ∂P,∀ r∈Ico 0 t,vt (t-r,X (realTimeClamp r) w)=
      (∑ i,fderiv ℝ (v (t-r)) (X (realTimeClamp r) w) (Pi.single i 1)*G i (realTimeClamp r) w)+
      (∑ i,∑ l,fderiv ℝ (fderiv ℝ (v (t-r))) (X (realTimeClamp r) w) (Pi.single i 1) (Pi.single l 1)*
        (∑ j,H i j (realTimeClamp r) w*H l j (realTimeClamp r) w))/2+
      g (t-r,X (realTimeClamp r) w)-k (t-r,X (realTimeClamp r) w)*v (t-r) (X (realTimeClamp r) w))
    (L : Ω → ℝ) (hL : MemLp L 2 P)
    (hb : ∀ᵐ w ∂P,∀ r∈Icc 0 t,|v (t-r) (X (realTimeClamp r) w)|≤L w ∧ |g (t-r,X (realTimeClamp r) w)|≤L w)
    (s : ℝ) (hs : s∈Icc 0 t) :
    let V := fun r w => v (t-r) (X (realTimeClamp r) w)*discountFactor (fun a => k (t-a,X (realTimeClamp a) w)) r+
      ∫ a in 0..r,g (t-a,X (realTimeClamp a) w)*discountFactor (fun b => k (t-b,X (realTimeClamp b) w)) a
    P[V t | F (realTimeClamp s)]=ᵐ[P] V s := by
  dsimp only
  let c := fun r : ClosedTime T => (finitePrefixTime t ht r).val
  let Y := fun r w => (t-c r,X r w)
  let fv := fun z : ℝ × (Fin dim → ℝ) => v (max 0 z.1) z.2
  have hfv : Continuous fv := hvc.comp_continuous
    ((continuous_const.max continuous_fst).prodMk continuous_snd) (fun z => show 0≤max 0 z.1 from le_max_left _ _)
  let U := fun r w => fv (Y r w)
  let K := fun r w => k (Y r w)
  let Gs := fun r w => g (Y r w)
  have hYa r hr : Measurable[F r] (Y r) := measurable_const.prodMk (hXa r hr)
  have hYc w r hr : ContinuousAt (fun a => Y a w) r :=
    (continuousAt_const.sub ((continuous_subtype_val.comp (finite_prefix_time_continuous t ht)).continuousAt)).prodMk (hXc w r hr)
  have hcr r (hr : r∈Icc 0 t) : c (realTimeClamp r)=r := finite_prefix_time_of_real t r ht hr htT.le
  have hUr w r (hr : r∈Icc 0 t) : U (realTimeClamp r) w=v (t-r) (X (realTimeClamp r) w) := by
    dsimp only [U,fv,Y]
    rw [hcr r hr,max_eq_right (sub_nonneg.mpr hr.2)]
  have hKr w r (hr : r∈Icc 0 t) : K (realTimeClamp r) w=k (t-r,X (realTimeClamp r) w) := by
    dsimp only [K,Y]
    rw [hcr r hr]
  have hGr w r (hr : r∈Icc 0 t) : Gs (realTimeClamp r) w=g (t-r,X (realTimeClamp r) w) := by
    dsimp only [Gs,Y]
    rw [hcr r hr]
  have hUb : ∀ᵐ w ∂P,∀ r∈Icc 0 t,|U (realTimeClamp r) w|≤L w ∧ |Gs (realTimeClamp r) w|≤L w := by
    filter_upwards [hb] with w hw
    intro r hr
    rw [hUr w r hr,hGr w r hr]
    exact hw r hr
  obtain ⟨V,hVa,hVc,hVr,hVb⟩ := discounted_process_construction P hT F hF hle hnull U K Gs
    (fun r hr => hfv.measurable.comp (hYa r hr)) (fun w r hr => hfv.continuousAt.comp (hYc w r hr))
    (fun r hr => hk.measurable.comp (hYa r hr)) (fun w r hr => hk.continuousAt.comp (hYc w r hr))
    (fun r hr => hg.measurable.comp (hYa r hr)) (fun w r hr => hg.continuousAt.comp (hYc w r hr))
    t ht htT (fun w r hr => by rw [hKr w r hr];exact hkpos r hr _) L hL hUb
  have hDr w r (hr : r∈Icc 0 t) : discountFactor (fun a => K (realTimeClamp a) w) r=
      discountFactor (fun a => k (t-a,X (realTimeClamp a) w)) r := by
    dsimp only [discountFactor]
    congr 2
    apply intervalIntegral.integral_congr
    intro a ha
    exact hKr w a (Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using ha))
  have hrep r (hr : r∈Icc 0 t) : V (realTimeClamp r)=fun w =>
      v (t-r) (X (realTimeClamp r) w)*discountFactor (fun a => k (t-a,X (realTimeClamp a) w)) r+
        ∫ a in 0..r,g (t-a,X (realTimeClamp a) w)*discountFactor (fun b => k (t-b,X (realTimeClamp b) w)) a := by
    funext w
    rw [hVr w r hr,hUr w r hr,hDr w r hr]
    congr 1
    apply intervalIntegral.integral_congr
    intro a ha
    have ha' : a∈Icc 0 t := Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using ha)
    dsimp only
    rw [hGr w a ha',hDr w a ha']
  have hLB : Integrable (fun w => (1+t)*L w) P := (hL.const_mul (1+t)).integrable (by norm_num)
  have hsm := hVa (realTimeClamp s) (real_time_below s hs.1 ((EReal.coe_le_coe hs.2).trans_lt htT))
  have hsb : ∀ᵐ w ∂P,|V (realTimeClamp s) w|≤(1+t)*L w :=
    hVb.mono fun w hw => hw _ (real_time_clamp_mono hs.2)
  have hsi : Integrable (V (realTimeClamp s)) P :=
    hLB.mono' ((hsm.mono (hle _) le_rfl).aestronglyMeasurable) hsb
  have hcnd : P[V (realTimeClamp t) | F (realTimeClamp s)]=ᵐ[P] V (realTimeClamp s) := by
    rcases hs.2.eq_or_lt with hst | hst
    · subst s
      exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable (hle _) hsm.stronglyMeasurable hsi)
    apply dominated_conditional_terminal_limit P (F (realTimeClamp s)) (hle _)
      (fun r => V (realTimeClamp r)) (V (realTimeClamp s)) s t (fun w => (1+t)*L w) hLB hst
    · intro r hr
      exact ((hVa _ (real_time_below r (hs.1.trans hr.1) ((EReal.coe_le_coe hr.2).trans_lt htT))).mono (hle _) le_rfl).aestronglyMeasurable
    · intro w
      exact ((hVc w).comp real_time_clamp_continuous).continuousOn
    · intro r hr
      exact hVb.mono fun w hw => hw _ (real_time_clamp_mono hr.2)
    · exact hsm.stronglyMeasurable
    · exact hsi
    intro r hr
    rw [hrep r ⟨hs.1.trans hr.1,hr.2.le⟩,hrep s hs]
    apply sde_discounted_positive_strip P hT F hF hle hnull W B hW hB hclock X ξ hξ hXa hXc G H N
      hGa hGc hN hHa hHc hNI r (hs.1.trans hr.1) ((EReal.coe_lt_coe hr.2).trans htT)
      (he.mono fun w hw a ha => hw a ⟨ha.1,ha.2.trans hr.2.le⟩) t hr.2 v vt hv hvt
      (hvc.mono fun z hz => show 0≤z.1 from le_of_lt hz) hvtc hdxc hhc k g hk hg
      (fun a ha => hkpos a ⟨ha.1,ha.2.trans hr.2.le⟩)
      (hpde.mono fun w hw a ha => hw a ⟨ha.1,ha.2.trans_lt hr.2⟩) L hL
      (hb.mono fun w hw a ha => hw a ⟨ha.1,ha.2.trans hr.2.le⟩) s ⟨hs.1,hr.1⟩
  rwa [hrep t ⟨ht,le_rfl⟩,hrep s hs] at hcnd

end Asakura.Chapter4
