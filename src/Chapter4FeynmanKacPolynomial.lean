import Chapter4DiscountedFKCoefficients
import Chapter4PolynomialPathDomination
import Chapter4VectorCoefficientBridge
import Chapter4VectorLipschitzGrowth
import Chapter4VectorGlobalPowerMoment
import Chapter4VectorPowerGrowth
import Chapter4ConditionalFKCoefficients
import Chapter4NonnegativeTimeExtension
import Chapter4DiscountedFunctionComponents
import Chapter4PolynomialNormComparison

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5 Asakura.Chapter4.Vector
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's conditional Feynman--Kac formula, with continuous
coefficients evaluated on the actual vector SDE and the printed generator. -/
theorem feynman_kac_polynomial_sde
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) (hTinf : T=⊤) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W : Fin noise → ClosedTime T → Ω → ℝ)
    (B : Fin noise → Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hB : ∀ j k,LocalCovarianceWitness P F (W j) (W k) (B j k))
    (hclock : ∀ j k w (r : ℝ),0≤r → (r:EReal)<T → B j k (realTimeClamp r) w=if j=k then r else 0)
    (X : ClosedTime T → Ω → Fin dim → ℝ) (x : Fin dim → ℝ)
    (hXa : ∀ r,r<⊤ → Measurable[F r] (X r))
    (hXc : ∀ w r,r<⊤ → ContinuousAt (fun u => X u w) r)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ)
    (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (Lip : ℝ) (hLip : 0≤Lip)
    (hcoeff : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤Lip*∑ i,(x i-y i)^2)
    (N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => σ i j (X (realTimeClamp z.2) z.1)) (N i j))
    (t : ℝ) (ht : 0≤t) (htT : (t:EReal)<T)
    (he : ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T → ∀ i,X (realTimeClamp r) w i=
      x i+(∫ s in 0..r,μ i (X (realTimeClamp s) w))+∑ j,N i j (realTimeClamp r) w)
    (v : ℝ → (Fin dim → ℝ) → ℝ) (vt : ℝ × (Fin dim → ℝ) → ℝ)
    (hv : ∀ a,0<a → ContDiff ℝ 2 (v a))
    (hvt : ∀ a,0<a → ∀ x,HasDerivAt (fun s => v s x) (vt (a,x)) a)
    (hvc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => v z.1 z.2) {z | 0≤z.1})
    (hvtc : ContinuousOn vt {z | 0<z.1})
    (hdxc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (v z.1) z.2) {z | 0<z.1})
    (hhc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (v z.1)) z.2) {z | 0<z.1})
    (k g : ℝ × (Fin dim → ℝ) → ℝ) (hk : ContinuousOn k {z | 0≤z.1}) (hg : ContinuousOn g {z | 0≤z.1})
    (hkpos : ∀ a,0≤a → ∀ x,0≤k (a,x))
    (hpde : ∀ a,0<a → ∀ x,vt (a,x)=
      (∑ i,fderiv ℝ (v a) x (Pi.single i 1)*μ i x)+
      (∑ i,∑ l,fderiv ℝ (fderiv ℝ (v a)) x (Pi.single i 1) (Pi.single l 1)*(∑ j,σ i j x*σ l j x))/2+g (a,x)-k (a,x)*v a x)
    (deg : ℕ) (C : ℝ) (hC : 0≤C)
    (hvbound : ∀ a∈Icc 0 t,∀ y,|v a y|≤C*(1+(Real.sqrt (∑ i,y i^2))^deg))
    (hgbound : ∀ a∈Icc 0 t,∀ y,|g (a,y)|≤C*(1+(Real.sqrt (∑ i,y i^2))^deg)) :
    v t x=(∫ w,v 0 (X (realTimeClamp t) w)*discountFactor (fun a => k (t-a,X (realTimeClamp a) w)) t ∂P)+
      ∫ w,(∫ a in 0..t,g (t-a,X (realTimeClamp a) w)*discountFactor (fun b => k (t-b,X (realTimeClamp b) w)) a) ∂P := by
  obtain ⟨hμ,hσ,hμLip,hσLip⟩ := manuscript_lipschitz_coordinates μ σ Lip hLip hcoeff
  obtain ⟨K,hK,hμg,hσg⟩ := vector_lipschitz_growth μ σ (Lip*(dim:ℝ)) (by positivity) hμLip hσLip
  have hmom := global_sde_power_moment P hT hTinf F hF hle hnull W (fun j => B j j) hW
    (fun j => hB j j) (fun j w r hr hrT => by simpa only [ite_true] using hclock j j w r hr hrT)
    μ σ (fun i => (hμ i).measurable) (fun i j => (hσ i j).measurable)
    (K*(dim+1)) (by positivity)
    (fun i y => vector_square_growth_norm y _ K hK (hμg i y))
    (fun i j y => vector_square_growth_norm y _ K hK (hσg i j y))
    (2*((deg:ℝ)+1)) (by have := Nat.cast_nonneg (α:=ℝ) deg;linarith)
    (fun _ => x) measurable_const (memLp_const x) X hXa hXc N hN hNI he t ht htT
  have hlow : 2*(deg:ℝ≥0∞)≤ENNReal.ofReal (2*((deg:ℝ)+1)) := by
    rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_add (by positivity) (by norm_num)]
    simp only [ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast,ENNReal.ofReal_one]
    gcongr
    exact le_add_of_nonneg_right (by norm_num)
  let Cp := C*(1+((dim:ℝ)+1)^deg)
  have hvbound' a (ha : a∈Icc 0 t) y : |v a y|≤Cp*(1+‖y‖^deg) :=
    euclidean_polynomial_growth_to_pi y deg C (v a y) hC (hvbound a ha y)
  have hgbound' a (ha : a∈Icc 0 t) y : |g (a,y)|≤Cp*(1+‖y‖^deg) :=
    euclidean_polynomial_growth_to_pi y deg C (g (a,y)) hC (hgbound a ha y)
  obtain ⟨L,hL,hbound⟩ := polynomial_path_uniform_bound P X hXc t ht htT
    (fun z => v (t-z.1) z.2) (fun z => g (t-z.1,z.2)) deg Cp (by dsimp only [Cp];positivity)
    (fun r hr y => hvbound' (t-r) ⟨sub_nonneg.mpr hr.2,by linarith [hr.1]⟩ y)
    (fun r hr y => hgbound' (t-r) ⟨sub_nonneg.mpr hr.2,by linarith [hr.1]⟩ y)
    (hmom.mono_exponent hlow)
  let ke := fun z : ℝ × (Fin dim → ℝ) => k (max 0 z.1,z.2)
  let ge := fun z : ℝ × (Fin dim → ℝ) => g (max 0 z.1,z.2)
  have hke a (ha : 0≤a) y : ke (a,y)=k (a,y) := by simp only [ke,max_eq_right ha]
  have hge a (ha : 0≤a) y : ge (a,y)=g (a,y) := by simp only [ge,max_eq_right ha]
  have hdisc w r (hr : r∈Icc 0 t) :
      discountFactor (fun a => ke (t-a,X (realTimeClamp a) w)) r=
      discountFactor (fun a => k (t-a,X (realTimeClamp a) w)) r := by
    apply discount_factor_congr_on_interval _ _ r hr.1
    intro a ha
    exact hke (t-a) (sub_nonneg.mpr (ha.2.trans hr.2)) _
  have hcnd := discounted_feynman_kac_coefficients P hT F hF hle hnull W B hW hB hclock X (fun _ => x)
    measurable_const hXa hXc μ σ hμ hσ N hN hNI t ht htT
    (he.mono fun w hw r hr => hw r hr.1 ((EReal.coe_le_coe hr.2).trans_lt htT))
    v vt hv hvt hvc hvtc hdxc hhc ke ge (continuous_nonnegative_time_extension k hk)
    (continuous_nonnegative_time_extension g hg)
    (fun a ha y => by rw [hke a ha];exact hkpos a ha y)
    (fun a ha y => by rw [hge a ha.le,hke a ha.le];exact hpde a ha y)
    L hL (ae_of_all _ fun w r hr => by
      rw [hge (t-r) (sub_nonneg.mpr hr.2)]
      exact hbound w r hr) 0 ⟨le_rfl,ht⟩
  have hz : realTimeClamp (T:=T) 0=⊥ := by
    apply Subtype.ext
    exact real_time_clamp_eq 0 le_rfl (le_of_lt hT)
  have hi : X ⊥=ᵐ[P] fun _ => x := by
    have hinit : ∀ᵐ w ∂P,∀ i j,N i j ⊥ w=0 :=
      ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (hN i j).initial P F
    filter_upwards [he,hinit] with w hw hw0
    ext i
    have hh := hw 0 le_rfl hT i
    simpa only [hz,intervalIntegral.integral_same,add_zero,hw0,Finset.sum_const_zero] using hh
  dsimp only at hcnd
  simp only [sub_self,sub_zero,hz,discount_factor_zero,mul_one,intervalIntegral.integral_same,add_zero] at hcnd
  have hres := transition_value_of_conditional_formula P (F ⊥) (hle ⊥) _ (X ⊥) x (v t) hi hcnd
  obtain ⟨hterm,hsource⟩ := discounted_function_components_integrable P hT F hF hle hnull X hXa hXc
    t ht htT v hvc ke ge (continuous_nonnegative_time_extension k hk)
    (continuous_nonnegative_time_extension g hg)
    (fun r hr y => by rw [hke (t-r) (sub_nonneg.mpr hr.2)];exact hkpos _ (sub_nonneg.mpr hr.2) y)
    L hL (ae_of_all _ fun w r hr => by
      rw [hge (t-r) (sub_nonneg.mpr hr.2)]
      exact hbound w r hr)
  have hterm' : Integrable (fun w => v 0 (X (realTimeClamp t) w)*discountFactor (fun a => k (t-a,X (realTimeClamp a) w)) t) P :=
    hterm.congr (ae_of_all _ fun w => by dsimp only;rw [hdisc w t ⟨ht,le_rfl⟩])
  have hsource' : Integrable (fun w => ∫ a in 0..t,g (t-a,X (realTimeClamp a) w)*discountFactor (fun b => k (t-b,X (realTimeClamp b) w)) a) P :=
    hsource.congr (ae_of_all _ fun w => by
      apply intervalIntegral.integral_congr
      intro a ha
      have ha' : a∈Icc 0 t := by simpa only [uIcc_of_le ht] using ha
      dsimp only
      rw [hge (t-a) (sub_nonneg.mpr ha'.2),hdisc w a ha'])
  rw [← integral_add hterm' hsource',hres]
  apply integral_congr_ae
  exact ae_of_all _ fun w => by
    dsimp only
    rw [hdisc w t ⟨ht,le_rfl⟩]
    congr 1
    apply intervalIntegral.integral_congr
    intro a ha
    have ha' : a∈Icc 0 t := by simpa only [uIcc_of_le ht] using ha
    dsimp only
    rw [hge (t-a) (sub_nonneg.mpr ha'.2),hdisc w a ha']

end Asakura.Chapter4
