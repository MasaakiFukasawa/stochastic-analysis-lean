import Chapter8DynkinFromFeynmanKac
import Chapter8DynkinFubini

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5 Asakura.Chapter4 Asakura.Chapter4.Vector
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Dynkin identity with expectation inside the time integral, derived
from the actual SDE and its already proved finite-time moments. -/
theorem dynkin_integrated_generator
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
    (∫ w,f (X (realTimeClamp t) w) ∂P)=f x+∫ s in 0..t, ∫ w,G (X (realTimeClamp s) w) ∂P := by
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
  have hb y : |G y|≤Cp*(1+‖y‖^deg) :=
    euclidean_polynomial_growth_to_pi y deg C (G y) hC (hGb y)
  obtain ⟨L,hL,hbound⟩ := polynomial_path_uniform_bound P X hXc t ht htT
    (fun z => G z.2) (fun z => G z.2) deg Cp (by dsimp only [Cp];positivity)
    (fun _ _ y => hb y) (fun _ _ y => hb y) (hmom.mono_exponent hlow)
  have hbelow r : realTimeClamp (T := T) r<⊤ := by
    apply (real_time_clamp_mono (le_max_left r 0)).trans_lt
    apply real_time_below (max r 0) (le_max_right r 0)
    simp [hTinf]
  have hXm r : Measurable (X (realTimeClamp r)) := (hXa _ (hbelow r)).mono (hle _) le_rfl
  have hXcont w : Continuous (fun r => X (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hXc w _ (hbelow r)).comp real_time_clamp_continuous.continuousAt
  have hXmjoint : Measurable (fun z : ℝ × Ω => X (realTimeClamp z.1) z.2) :=
    measurable_uncurry_of_continuous_of_measurable hXcont hXm
  have hh := dynkin_fubini P t ht (fun w s => G (X (realTimeClamp s) w))
    (hG.measurable.comp (hXmjoint.comp measurable_swap)) L
    (hL.integrable (by norm_num))
    (ae_of_all _ fun w s hs => by simpa only [Real.norm_eq_abs] using (hbound w s hs).1)
  rw [← hh.2]
  exact dynkin_from_feynman_kac P hT hTinf F hF hle hnull W B hW hB hclock X x hXa hXc
    μ σ Lip hLip hcoeff N hN hNI t ht htT he f G hf hG hgen deg C hC hfb hGb

end Asakura.Chapter8
