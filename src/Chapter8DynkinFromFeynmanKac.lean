import Chapter4FeynmanKacPolynomial

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5 Asakura.Chapter4 Asakura.Chapter4.Vector
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Dynkin's formula for the actual SDE, obtained by applying the already
verified Feynman--Kac formula to the time-independent function f and
source -Lf. This avoids assuming a martingale expectation identity. -/
theorem dynkin_from_feynman_kac
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
    (f G : (Fin dim → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (hG : Continuous G)
    (hgen : ∀ y,G y=(∑ i,fderiv ℝ f y (Pi.single i 1)*μ i y)+
      (∑ i,∑ l,fderiv ℝ (fderiv ℝ f) y (Pi.single i 1) (Pi.single l 1)*(∑ j,σ i j y*σ l j y))/2)
    (deg : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ y,|f y| ≤ C*(1+(Real.sqrt (∑ i,y i^2))^deg))
    (hGb : ∀ y,|G y| ≤ C*(1+(Real.sqrt (∑ i,y i^2))^deg)) :
    (∫ w,f (X (realTimeClamp t) w) ∂P)=f x+∫ w,(∫ s in 0..t,G (X (realTimeClamp s) w)) ∂P := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv (n := 1)).mp hf |>.2.2
  have hh := feynman_kac_polynomial_sde P hT hTinf F hF hle hnull W B hW hB hclock X x hXa hXc
    μ σ Lip hLip hcoeff N hN hNI t ht htT he
    (fun _ y => f y) (fun _ => 0) (fun _ _ => hf)
    (fun a _ y => hasDerivAt_const a (f y))
    (hf.continuous.comp continuous_snd).continuousOn continuous_const.continuousOn
    ((hf.continuous_fderiv (by norm_num)).comp continuous_snd).continuousOn
    ((hf1.continuous_fderiv (by norm_num)).comp continuous_snd).continuousOn
    (fun _ => 0) (fun z => -G z.2) continuous_const.continuousOn
    (hG.neg.comp continuous_snd).continuousOn (fun _ _ _ => le_rfl)
    (fun a _ y => by rw [← hgen y]; ring) deg C hC
    (fun _ _ y => hfb y) (fun _ _ y => by simpa only [abs_neg] using hGb y)
  have hdisc r : discountFactor (fun _ : ℝ => (0:ℝ)) r=1 := by simp [discountFactor]
  simp only [hdisc,mul_one,intervalIntegral.integral_neg,integral_neg] at hh
  linarith

end Asakura.Chapter8
