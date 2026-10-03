import Chapter4DiscountedDrift
import Chapter4DominatedLocalPointwise

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 5200000
set_option backward.isDefEq.respectTransparency false

/-- Conditional expectation after discounting a drift kU-g. Polynomial
bounds will supply the square-integrable random bound in the PDE application. -/
theorem discounted_drift_conditional
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (U N K G : ClosedTime T → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (hUa : ∀ t,t<⊤ → Measurable[F t] (U t))
    (hUc : ∀ w t,t<⊤ → ContinuousAt (fun s => U s w) t)
    (hKa : ∀ t,t<⊤ → Measurable[F t] (K t))
    (hKc : ∀ w t,t<⊤ → ContinuousAt (fun s => K s w) t)
    (hGa : ∀ t,t<⊤ → Measurable[F t] (G t))
    (hGc : ∀ w t,t<⊤ → ContinuousAt (fun s => G s w) t)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hKpos : ∀ w r,r∈Icc 0 R → 0≤K (realTimeClamp r) w)
    (B : Ω → ℝ) (hB : MemLp B 2 P)
    (hb : ∀ᵐ w ∂P,∀ r∈Icc 0 R,|U (realTimeClamp r) w|≤B w ∧ |G (realTimeClamp r) w|≤B w)
    (he : ∀ r∈Icc 0 R,U (realTimeClamp r)=ᵐ[P] fun w => U ⊥ w+N (realTimeClamp r) w+
      ∫ s in 0..r,K (realTimeClamp s) w*U (realTimeClamp s) w-G (realTimeClamp s) w)
    (s : ℝ) (hs : s∈Icc 0 R) :
    let V := fun r w => U (realTimeClamp r) w*discountFactor (fun a => K (realTimeClamp a) w) r+
      ∫ a in 0..r,G (realTimeClamp a) w*discountFactor (fun b => K (realTimeClamp b) w) a
    P[V R | F (realTimeClamp s)]=ᵐ[P] V s := by
  dsimp only
  obtain ⟨A,hA,hAc,hAe,_,hD,hDb⟩ := nonnegative_discount_process hT F hF K hKa hKc R hR hRT hKpos
  let D := fun t w => Real.exp (-A t w)
  have hDc w : Continuous (fun t => D t w) := Real.continuous_exp.comp ((hAc w).neg)
  have hDa t ht : Measurable[F t] (D t) := ((hA.adapted t ht).neg).exp
  have hd w r (hr : r∈Icc 0 R) : D (realTimeClamp r) w=discountFactor (fun a => K (realTimeClamp a) w) r := by
    dsimp only [D,discountFactor]
    rw [hAe,finite_prefix_time_of_real R r hR hr hRT.le]
  let H := fun z : Ω × ℝ => G (realTimeClamp z.2) z.1*D (realTimeClamp z.2) z.1
  have hHc w : ContinuousOn (fun r => H (w,r)) (Icc 0 R) := by
    intro r hr
    exact (((hGc w _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hRT))).mul (hDc w).continuousAt).comp
      real_time_clamp_continuous.continuousAt).continuousWithinAt
  have hHp := continuous_adapted_real_progressive F hF H R hR
    (fun r hr => (hGa _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hRT))).mul
      (hDa _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hRT)))) hHc
  obtain ⟨J,hJ,hJc,hJe⟩ := progressive_integrable_drift_variation hT F hF R hR hRT.le H hHp
    (fun w => ((hHc w).intervalIntegrable_of_Icc hR).1)
  let V := fun t w => U (min (realTimeClamp R) t) w*D t w+J t w
  have hVc w : Continuous (fun t => V t w) :=
    ((open_path_stopped_continuous U hUc R hR hRT w).mul (hDc w)).add (hJc w)
  have hVa t ht : Measurable[F t] (V t) :=
    (((hUa _ ((min_le_left _ _).trans_lt (real_time_below R hR hRT))).mono (hF (min_le_right _ _)) le_rfl).mul
      (hDa t ht)).add (hJ.adapted t ht)
  have hVr w r (hr : r∈Icc 0 R) : V (realTimeClamp r) w=
      U (realTimeClamp r) w*discountFactor (fun a => K (realTimeClamp a) w) r+
        ∫ a in 0..r,G (realTimeClamp a) w*discountFactor (fun b => K (realTimeClamp b) w) a := by
    dsimp only [V]
    rw [min_eq_right (real_time_clamp_mono hr.2),hd w r hr,hJe,finite_prefix_time_of_real R r hR hr hRT.le]
    congr 1
    apply intervalIntegral.integral_congr
    intro a ha
    dsimp only [H]
    rw [hd w a (Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using ha))]
  have hz : realTimeClamp (T:=T) 0=⊥ := by
    apply Subtype.ext
    exact real_time_clamp_eq 0 le_rfl (le_of_lt hT)
  have hV0 w : V ⊥ w=U ⊥ w := by
    have hh := hVr w 0 ⟨le_rfl,hR⟩
    simpa only [hz,discount_factor_zero,mul_one,intervalIntegral.integral_same,add_zero] using hh
  obtain ⟨Z,hZ,hZe⟩ := discounted_drift_local_representation P hT F hF hle hnull U N K G hN hUc hKa hKc hGc R hR hRT hKpos he
  have hrep t (ht : t≤realTimeClamp (T:=T) R) : V t=ᵐ[P] fun w => V ⊥ w+Z t w := by
    let r := (finitePrefixTime (T:=T) R hR t).val
    have hr : r∈Icc 0 R := (finitePrefixTime R hR t).property
    have hrt : realTimeClamp (T:=T) r=t := by rw [finite_prefix_time_clamp R hR hRT.le,min_eq_right ht]
    filter_upwards [hZe r hr] with w hw
    rw [hV0]
    rw [← hrt,hVr w r hr]
    exact hw
  have hbound : ∀ᵐ w ∂P,∀ t,t≤realTimeClamp (T:=T) R → |V t w|≤(1+R)*B w := by
    filter_upwards [hb] with w hw
    have hBpos : 0≤B w := (abs_nonneg _).trans (hw 0 ⟨le_rfl,hR⟩).1
    intro t ht
    let r := (finitePrefixTime (T:=T) R hR t).val
    have hr : r∈Icc 0 R := (finitePrefixTime R hR t).property
    have hrt : realTimeClamp (T:=T) r=t := by rw [finite_prefix_time_clamp R hR hRT.le,min_eq_right ht]
    rw [← hrt,hVr w r hr]
    have hDb' a (ha : a∈Icc 0 R) := discount_factor_bounds (fun b => K (realTimeClamp b) w) a ha.1
      (fun b hb => hKpos w b (Icc_subset_Icc_right ha.2 hb))
    have hUbound : |U (realTimeClamp r) w*discountFactor (fun a => K (realTimeClamp a) w) r|≤B w := by
      rw [abs_mul,abs_of_pos (hDb' r hr).1]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hDb' r hr).2).trans (hw r hr).1
    have hIbound := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=r) (C:=B w)
      (f:=fun a => G (realTimeClamp a) w*discountFactor (fun b => K (realTimeClamp b) w) a) (fun a ha => by
        have ha' : a∈Icc 0 R := Icc_subset_Icc_right hr.2 ⟨(uIoc_of_le hr.1 ▸ ha).1.le,(uIoc_of_le hr.1 ▸ ha).2⟩
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos (hDb' a ha').1]
        exact (mul_le_of_le_one_right (abs_nonneg _) (hDb' a ha').2).trans (hw a ha').2)
    simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg hr.1] at hIbound
    have hsum := (abs_add_le _ _).trans (add_le_add hUbound hIbound)
    nlinarith [mul_le_mul_of_nonneg_right hr.2 hBpos]
  have hh := square_dominated_local_increment_conditional_of_pointwise P hT F hF hle V Z hZ hVa
    (fun w t _ => (hVc w).continuousAt) (realTimeClamp R) (real_time_below R hR hRT)
    (fun w => (1+R)*B w) (hB.const_mul (1+R)) hbound hrep (realTimeClamp s) (real_time_clamp_mono hs.2)
  rw [funext (fun w => hVr w R ⟨hR,le_rfl⟩),funext (fun w => hVr w s hs)] at hh
  exact hh

end Asakura.Chapter4
