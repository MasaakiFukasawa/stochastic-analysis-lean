import Chapter4ExponentialWeight
import Chapter4ClockVariationIntegral
import Chapter2ItoAssociativityConstruction
import Chapter3IdentityItoIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The explicit OU process, with its actual Ito integral constructed,
satisfies the manuscript's integral equation at all finite times. -/
theorem ou_sde_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (y a σ : ℝ) :
    ∃ N : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W (fun z => σ*Real.exp (-a*z.2)) N ∧
      ∀ᵐ w ∂P,∀ d : ℝ,0≤d → (d:EReal)<T →
        Real.exp (a*d)*(y+N (realTimeClamp d) w)=y+
          a*(∫ r in 0..d,Real.exp (a*r)*(y+N (realTimeClamp r) w))+σ*W (realTimeClamp d) w := by
  let G := fun z : Ω × ℝ => σ*Real.exp (-a*A (realTimeClamp z.2) z.1)
  let H := fun z : Ω × ℝ => Real.exp (a*A (realTimeClamp z.2) z.1)
  obtain ⟨hAm,hAc⟩ := clock_regular_from_identity A hclock
  have hAa := hA.adapted P F hW hW
  have hregG := open_process_real_regularity F (fun t w => σ*Real.exp (-a*A t w))
    (fun t ht => measurable_const.mul ((measurable_const.mul (hAa t ht)).exp))
    (fun w t ht => continuousAt_const.mul ((Real.continuous_exp.continuousAt.comp (continuousAt_const.mul (hAc w t ht)))))
  have hregH := open_process_real_regularity F (fun t w => Real.exp (a*A t w))
    (fun t ht => (measurable_const.mul (hAa t ht)).exp)
    (fun w t ht => (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul (hAc w t ht))))
  obtain ⟨N,Z,V,hN,hZ,hV,hNI,hZI,hVI,hZV⟩ := continuous_adapted_ito_associativity_constructed
    P hT F hF hle hnull W hW G H hregG.1 hregH.1 hregG.2 hregH.2
  have hprod : (fun z => H z*G z)=(fun _ : Ω × ℝ => σ) := by
    funext z
    dsimp only [H,G]
    rw [mul_left_comm,← Real.exp_add]
    simp only [neg_mul,add_neg_cancel,Real.exp_zero,mul_one]
  rw [hprod] at hVI
  have hid := identity_ito_integral P hT F hF hle hnull W hW
  have hσI : ItoCovarianceFormula P F W (fun _ => σ) (fun t w => σ*W t w) := by
    convert hid.add_smul P F hF hle W W W (fun _ => 1) (fun _ => 1) hid (σ-1) using 1 <;>
      ext z w <;> ring
  have hVσ := ItoCovarianceFormula.unique P hT F hF hle hnull W V (fun t w => σ*W t w)
    (fun _ => σ) hW hV (hW.smul P F σ) hVI hσI
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hv : ContDiff ℝ 1 (fun x : ℝ => Real.exp (a*x)) := by fun_prop
  have hder x : HasDerivAt (fun s => Real.exp (a*s)) (a*Real.exp (a*x)) x := by
    convert ((hasDerivAt_id x).const_mul a).exp using 1 <;> simp only [id_eq] <;> ring
  obtain ⟨J,L,hJ,hJI,hL,hLc,hLI,hprodNL⟩ := C1_weighted_product_constructed P hT F hF hle hnull
    N A hN (continuous_increasing_adapted_variation hT F hF A hAa hAm hAc) hAc (fun x => Real.exp (a*x)) hv
    (exponential_adapted_variation hT F hF A hAa hAm hAc a)
    c (fun n => (hc n).le) hcm.monotone hcT hcc
  have hJZ := ItoCovarianceFormula.unique P hT F hF hle hnull N J Z H hN hJ hZ hJI hZI
  simp only [(hder _).deriv] at hLI
  have htime := clock_variation_integral_all_times P A L _ c (fun n => (hc n).le) hcT
    (fun n w r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) hLI
  refine ⟨N,hN,hNI.congr_on_time_domain P F W N G _ (fun w r hr hrT => by dsimp only [G]; rw [hclock w r hr hrT]),?_⟩
  filter_upwards [hprodNL,hJZ,hZV,hVσ,htime] with w hw hj hz hvw ht
  intro d hd hdT
  have hdt := real_time_below d hd hdT
  obtain ⟨n,hn⟩ := hcc _ hdt
  have hdn : d≤c n := by
    change (realTimeClamp d:EReal)<(realTimeClamp (c n):EReal) at hn
    rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c n) (hc n).le (hcT n).le] at hn
    exact (EReal.coe_lt_coe_iff.mp hn).le
  have hp := hw _ hdt
  rw [hclock w d hd hdT,hj _ hdt,hz _ hdt,hvw _ hdt,ht n d ⟨hd,hdn⟩] at hp
  have hLIr : (∫ r in 0..d,N (realTimeClamp r) w*(a*Real.exp (a*A (realTimeClamp r) w)))=
      a*(∫ r in 0..d,N (realTimeClamp r) w*Real.exp (a*r)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc 0 d := by simpa only [uIcc_of_le hd] using hr
    dsimp only
    rw [hclock w r hr'.1 ((EReal.coe_le_coe hr'.2).trans_lt hdT)]
    ring
  rw [hLIr] at hp
  have hcN := (open_process_real_regularity F N (hN.adapted P F) (hN.path P F)).2 d hd hdT w
  have hNe : IntervalIntegrable (fun r => N (realTimeClamp r) w*Real.exp (a*r)) volume 0 d :=
    (hcN.mul (by fun_prop : Continuous (fun r : ℝ => Real.exp (a*r))).continuousOn).intervalIntegrable_of_Icc hd
  have hee : IntervalIntegrable (fun r : ℝ => Real.exp (a*r)) volume 0 d :=
    (by fun_prop : Continuous (fun r : ℝ => Real.exp (a*r))).intervalIntegrable _ _
  have hint : (∫ r in 0..d,Real.exp (a*r)*(y+N (realTimeClamp r) w))=
      y*(∫ r in 0..d,Real.exp (a*r))+(∫ r in 0..d,N (realTimeClamp r) w*Real.exp (a*r)) := by
    have heq : (fun r => Real.exp (a*r)*(y+N (realTimeClamp r) w))=
        (fun r => y*Real.exp (a*r)+N (realTimeClamp r) w*Real.exp (a*r)) := by funext r; ring
    rw [heq,intervalIntegral.integral_add (hee.const_mul y) hNe,intervalIntegral.integral_const_mul]
  rw [hint]
  have hdet := exponential_weight_integral a d
  nlinarith only [hp,congrArg (fun x : ℝ => y*x) hdet]

end Asakura.Chapter4
