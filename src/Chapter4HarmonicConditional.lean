import Chapter5NonlinearFeynmanKacUnit
import Chapter5TimeSpaceIntegrand
import Chapter5BoundedBrownianIntegralM2

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- A bounded space-time harmonic test with bounded spatial derivative
has the conditional martingale identity, derived from the constructed Ito
integral and its finite-horizon M² property. No increment law is assumed. -/
theorem harmonic_conditional_from_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (f : (Fin 2 → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (hpde : ∀ r∈Icc 0 R,∀ x,fderiv ℝ f ![r,x] (Pi.single 0 1)+
      fderiv ℝ (fderiv ℝ f) ![r,x] (Pi.single 1 1) (Pi.single 1 1)/2=0)
    (K C : ℝ) (hC : 0≤C)
    (hbound : ∀ r∈Icc 0 R,∀ x,|f ![r,x]|≤K)
    (hgrad : ∀ r∈Icc 0 R,∀ x,|fderiv ℝ f ![r,x] (Pi.single 1 1)|≤C)
    (s : ℝ) (hs : s∈Icc 0 R) :
    P[(fun w => f ![R,W (realTimeClamp R) w]) | F (realTimeClamp s)] =ᵐ[P]
      fun w => f ![s,W (realTimeClamp s) w] := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨N,hN,hNI,hrep⟩ := nonlinear_feynman_kac_unit P hT F hF hle hnull W A hW hA
    R hR hRT f hf (fun _ _ _ => 0) (fun x => f ![R,x]) (fun _ => rfl)
    (fun r hr x => by simpa only [add_zero] using hpde r hr x)
    c (fun n => (hc n).le) hcm.monotone hcT hcc
    (fun n w r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))
  let G := fun z : Ω × ℝ => fderiv ℝ f
    ![(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val,W (realTimeClamp z.2) z.1] (Pi.single 1 1)
  have hreg := time_space_integrand_regularity P F W (fun _ _ => 0) W
    (local_martingale_semimartingale_decomposition P hT F hF W hW) R hR
    (fun x => fderiv ℝ f x (Pi.single 1 1))
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hM := bounded_brownian_integral_stopped_M2 P hT F hF hle hnull W A N hW hA hN hclock
    G hreg.2.1 hreg.2.2 hNI R C hR hRT hC (by
      intro w r hr
      dsimp only [G]
      rw [finite_prefix_time_of_real R r hR hr hRT.le]
      exact hgrad r hr (W (realTimeClamp r) w))
  have hst : realTimeClamp (T := T) s≤realTimeClamp R := real_time_clamp_mono hs.2
  have hmart := hM.martingale (realTimeClamp s) (realTimeClamp R) hst
  simp only [min_self,min_eq_right hst] at hmart
  have hiR : Integrable (N (realTimeClamp R)) P := by
    simpa only [min_self] using (hM.moment (realTimeClamp R)).integrable (by norm_num)
  have his : Integrable (N (realTimeClamp s)) P := by
    simpa only [min_eq_right hst] using (hM.moment (realTimeClamp s)).integrable (by norm_num)
  have hsT : realTimeClamp (T := T) s<⊤ := by
    change (realTimeClamp s:EReal)<T
    rw [real_time_clamp_eq s hs.1 ((EReal.coe_le_coe hs.2).trans hRT.le)]
    exact (EReal.coe_le_coe hs.2).trans_lt hRT
  have hsm : Measurable[F (realTimeClamp s)] (fun w => f ![s,W (realTimeClamp s) w]) := by
    letI : MeasurableSpace Ω := F (realTimeClamp s)
    apply hf.continuous.measurable.comp
    apply measurable_pi_iff.mpr
    intro i
    fin_cases i
    · exact measurable_const
    · exact hW.adapted P F _ hsT
  have hsi : Integrable (fun w => f ![s,W (realTimeClamp s) w]) P :=
    Integrable.of_bound (hsm.mono (hle _) le_rfl).aestronglyMeasurable K
      (ae_of_all _ fun w => hbound s hs _)
  have he := hrep s hs
  simp only [intervalIntegral.integral_zero,sub_zero] at he
  have hadd := condExp_add hsi (hiR.sub his) (F (realTimeClamp s))
  have hsub := condExp_sub hiR his (F (realTimeClamp s))
  have hfix := condExp_of_stronglyMeasurable (hle _) hsm.stronglyMeasurable hsi
  have hNs := condExp_of_stronglyMeasurable (hle _) (hN.adapted P F _ hsT).stronglyMeasurable his
  simp only [Pi.add_def,Pi.sub_def] at hadd hsub
  apply (condExp_congr_ae he).trans
  filter_upwards [hadd,hsub,hmart] with w ha hb hm
  rw [ha,hb]
  simp only [hfix,hNs,hm,sub_self,add_zero]

end Asakura.Chapter4
