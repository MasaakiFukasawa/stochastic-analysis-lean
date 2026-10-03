import Chapter8DynkinIntegratedGenerator
import Chapter8SDEExpectationContinuity
import Chapter8DynkinTimeDerivative
import Chapter8DynkinFubini

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5 Asakura.Chapter4 Asakura.Chapter4.Vector
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- The right generator at zero is derived from the actual SDE. -/
theorem sde_right_generator
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
    (he : ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T → ∀ i,X (realTimeClamp r) w i=
      x i+(∫ s in 0..r,μ i (X (realTimeClamp s) w))+∑ j,N i j (realTimeClamp r) w)
    (f G : (Fin dim → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (hG : Continuous G)
    (hgen : ∀ y,G y=(∑ i,fderiv ℝ f y (Pi.single i 1)*μ i y)+
      (∑ i,∑ l,fderiv ℝ (fderiv ℝ f) y (Pi.single i 1) (Pi.single l 1)*(∑ j,σ i j y*σ l j y))/2)
    (deg : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ y,|f y| ≤ C*(1+(Real.sqrt (∑ i,y i^2))^deg))
    (hGb : ∀ y,|G y| ≤ C*(1+(Real.sqrt (∑ i,y i^2))^deg)) :
    HasDerivWithinAt (fun r => ∫ w,f (X (realTimeClamp r) w) ∂P) (G x) (Ici 0) 0 := by
  have hc := sde_polynomial_expectation_continuous P hT hTinf F hF hle hnull W B hW hB hclock
    X x hXa hXc μ σ Lip hLip hcoeff N hN hNI 1 (by norm_num) (by rw [hTinf]; exact EReal.coe_lt_top _) he G hG deg C hC hGb
  have heq (r : ℝ) (hr : 0≤r) (hrT : (r:EReal)<T) :=
    dynkin_integrated_generator P hT hTinf F hF hle hnull W B hW hB hclock
      X x hXa hXc μ σ Lip hLip hcoeff N hN hNI r hr hrT he f G hf hG hgen deg C hC hfb hGb
  have hz := heq 0 le_rfl (by simpa using hT)
  simp only [intervalIntegral.integral_same,add_zero] at hz
  have hzero : realTimeClamp (T:=T) 0=⊥ := by
    apply Subtype.ext
    exact real_time_clamp_eq 0 le_rfl (le_of_lt hT)
  have hi : X (realTimeClamp 0)=ᵐ[P] fun _ => x := by
    have hinit : ∀ᵐ w ∂P,∀ i j,N i j ⊥ w=0 :=
      ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (hN i j).initial P F
    filter_upwards [he,hinit] with w hw hw0
    ext i
    have hh := hw 0 le_rfl hT i
    simpa only [hzero,intervalIntegral.integral_same,add_zero,hw0,Finset.sum_const_zero] using hh
  have hg0 : (∫ w,G (X (realTimeClamp 0) w) ∂P)=G x := by
    calc
      _ = ∫ _ : Ω,G x ∂P := integral_congr_ae (hi.mono (fun w hw => congrArg G hw))
      _ = G x := by simp
  rw [← hg0]
  apply dynkin_right_derivative _ _ 1 (by norm_num) hc
  intro r hr
  rw [hz]
  exact heq r hr.1 (by rw [hTinf]; exact EReal.coe_lt_top _)

end Asakura.Chapter8
