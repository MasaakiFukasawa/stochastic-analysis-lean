import Chapter5NonlinearFeynmanKacUnit
import Chapter5SmoothExtension
import Chapter4BrownianSystem

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Actual Ito representation with a constant multiple of the spatial
gradient as drift, as needed under the original market measure. -/
theorem open_gradient_drift_ito_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (R T : ℝ) (hR : 0≤R) (hRT : R<T)
    (θ : ℝ) (v : (Fin 2 → ℝ) → ℝ)
    (hv : ContDiffOn ℝ 2 v {q | q 0<T})
    (hpde : ∀ t∈Icc 0 R,∀ x,fderiv ℝ v ![t,x] (Pi.single 0 1)+
      fderiv ℝ (fderiv ℝ v) ![t,x] (Pi.single 1 1) (Pi.single 1 1)/2=θ*fderiv ℝ v ![t,x] (Pi.single 1 1)) :
    ∃ N : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => fderiv ℝ v ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,
          B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) N ∧
      ∀ t∈Icc 0 R,(fun w => v ![t,B.W 0 (realTimeClamp t) w])=ᵐ[P]
        fun w => v ![0,B.W 0 ⊥ w]+N (realTimeClamp t) w+
          (∫ u in 0..t,θ*fderiv ℝ v ![u,B.W 0 (realTimeClamp u) w] (Pi.single 1 1)) := by
  obtain ⟨g,hg,he⟩ := time_strip_C2_extension R {q : Fin 2 → ℝ | q 0<T}
    (isOpen_lt (continuous_apply 0) continuous_const)
    (fun q hq => lt_of_le_of_lt hq.2 hRT) v hv
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion (T:=(⊤:EReal)) (by simp)
  obtain ⟨N,hN,hNI,hrep⟩ := nonlinear_feynman_kac_unit P (T:=(⊤:EReal)) (by simp)
    B.F B.mono B.le B.null (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0)
    R hR (EReal.coe_lt_top R) g hg (fun _ _ z => -θ*z) (fun x => g ![R,x]) (fun _ => rfl)
    (fun t ht x => by
      have hh := he ![t,x] (by simpa using ht)
      rw [hh.2.1,hh.2.2]
      have h := hpde t ht x
      linarith)
    c (fun n => (hc n).le) hcm.monotone hcT hcc
    (fun n w t ht => B.diagonal_clock 0 w t ht.1)
  have hi : (fun z : Ω × ℝ => fderiv ℝ g ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,
      B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1))=
    (fun z => fderiv ℝ v ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,
      B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) := by
    funext z
    have hh := he ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,B.W 0 (realTimeClamp z.2) z.1]
      (by simpa using (finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).property)
    exact congrArg (fun L => L (Pi.single 1 1)) hh.2.1
  rw [hi] at hNI
  refine ⟨N,hN,hNI,?_⟩
  have hz : realTimeClamp (T:=(⊤:EReal)) 0=⊥ := by
    apply Subtype.ext
    change (realTimeClamp (T:=(⊤:EReal)) 0:EReal)=0
    simpa only [EReal.coe_zero] using real_time_clamp_eq (T:=(⊤:EReal)) 0 le_rfl le_top
  intro t ht
  filter_upwards [hrep t ht,hrep 0 ⟨le_rfl,hR⟩,hN.initial P B.F] with w htw h0w hn0
  simp only [hz,hn0,Pi.zero_apply,sub_zero] at h0w
  let D := fun u : ℝ => -θ*fderiv ℝ g ![u,B.W 0 (realTimeClamp u) w] (Pi.single 1 1)
  have hUc : ContinuousOn (fun u : ℝ => ![u,B.W 0 (realTimeClamp u) w]) (Icc 0 R) := by
    intro u hu
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact continuousAt_id
    · exact ((B.martingale 0).path P B.F w _ (real_time_below u hu.1 (EReal.coe_lt_top u))).comp real_time_clamp_continuous.continuousAt
  have hDc : ContinuousOn D (Icc 0 R) :=
    continuousOn_const.mul (((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp_continuousOn hUc)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    ((hDc.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
    ((hDc.mono (Icc_subset_Icc_left ht.1)).intervalIntegrable_of_Icc ht.2)
  have hneg : (∫ u in 0..t,D u)= -(∫ u in 0..t,θ*fderiv ℝ v ![u,B.W 0 (realTimeClamp u) w] (Pi.single 1 1)) := by
    rw [←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u∈Icc 0 R := Icc_subset_Icc_right ht.2 (by simpa only [uIcc_of_le ht.1] using hu)
    dsimp only [D]
    rw [(he ![u,B.W 0 (realTimeClamp u) w] (by simpa using hu')).2.1]
    ring
  rw [(he ![t,B.W 0 (realTimeClamp t) w] (by simpa using ht)).1] at htw
  rw [(he ![0,B.W 0 ⊥ w] (by simpa using (show (0:ℝ)∈Icc 0 R from ⟨le_rfl,hR⟩))).1] at h0w
  change g ![R,B.W 0 (realTimeClamp R) w]=v ![t,B.W 0 (realTimeClamp t) w]-(∫ u in t..R,D u)+(N (realTimeClamp R) w-N (realTimeClamp t) w) at htw
  change g ![R,B.W 0 (realTimeClamp R) w]=v ![0,B.W 0 ⊥ w]-(∫ u in 0..R,D u)+N (realTimeClamp R) w at h0w
  linarith

end Asakura.Chapter11
