import Chapter5NonlinearFeynmanKacUnit
import Chapter5SmoothExtension
import Chapter4BrownianSystem

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Actual Ito representation of a harmonic pricing function on every
preterminal strip. No global extension of the original payoff is assumed. -/
theorem open_harmonic_ito_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (R T : ℝ) (hR : 0≤R) (hRT : R<T)
    (v : (Fin 2 → ℝ) → ℝ)
    (hv : ContDiffOn ℝ 2 v {q | q 0<T})
    (hpde : ∀ t∈Icc 0 R,∀ x,fderiv ℝ v ![t,x] (Pi.single 0 1)+
      fderiv ℝ (fderiv ℝ v) ![t,x] (Pi.single 1 1) (Pi.single 1 1)/2=0) :
    ∃ N : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => fderiv ℝ v ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,
          B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) N ∧
      ∀ t∈Icc 0 R,(fun w => v ![t,B.W 0 (realTimeClamp t) w])=ᵐ[P]
        fun w => v ![0,B.W 0 ⊥ w]+N (realTimeClamp t) w := by
  obtain ⟨g,hg,he⟩ := time_strip_C2_extension R {q : Fin 2 → ℝ | q 0<T}
    (isOpen_lt (continuous_apply 0) continuous_const)
    (fun q hq => lt_of_le_of_lt hq.2 hRT) v hv
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion (T:=(⊤:EReal)) (by simp)
  obtain ⟨N,hN,hNI,hrep⟩ := nonlinear_feynman_kac_unit P (T:=(⊤:EReal)) (by simp)
    B.F B.mono B.le B.null (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0)
    R hR (EReal.coe_lt_top R) g hg (fun _ _ _ => 0) (fun x => g ![R,x]) (fun _ => rfl)
    (fun t ht x => by
      have hh := he ![t,x] (by simpa using ht)
      rw [hh.2.1,hh.2.2]
      simpa only [add_zero] using hpde t ht x)
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
  simp only [intervalIntegral.integral_zero,sub_zero,hz,hn0,Pi.zero_apply] at htw h0w
  rw [(he ![t,B.W 0 (realTimeClamp t) w] (by simpa using ht)).1] at htw
  rw [(he ![0,B.W 0 ⊥ w] (by simpa using (show (0:ℝ)∈Icc 0 R from ⟨le_rfl,hR⟩))).1] at h0w
  linarith

end Asakura.Chapter11
