import Chapter4ProgressiveFiniteMoment
import Chapter4ClockRegularity
import Chapter8BrownianForcingPath

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Finite path moments of the deterministic noise integrals used in the
Kalman linear state equation, obtained from the proved Ito maximal estimate. -/
theorem deterministic_noise_path {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (B : BrownianSystem P n)
    (j : Fin n) (g : ℝ → ℝ) (hg : Continuous g)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W j) (fun z => g z.2) N)
    (T : ℝ) (hT : 0≤T) :
    ∃ Z : Ω → C(Icc (0:ℝ) T,ℝ),Measurable Z ∧ MemLp Z 2 P ∧
      (∀ w t,Z w t=N (realTimeClamp t.val) w) ∧
      (∫ w,‖Z w‖^2 ∂P)≤4*(∫ s in 0..T,(g s)^2) := by
  have hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<⊤ → B.C j j (realTimeClamp r) w=r :=
    fun w r hr _ => B.diagonal_clock j w r hr
  obtain ⟨hCm,hCc⟩ := clock_regular_from_identity (B.C j j) hclock
  have hp (R : ℝ) hR (_ : (R:EReal)<⊤) := continuous_adapted_real_progressive B.F B.mono
    (fun z : Ω × ℝ => g z.2) R hR
    (fun r _ => (show Measurable[B.F (realTimeClamp r)] (fun _ : Ω => g r) from measurable_const))
    (fun _ => hg.continuousOn)
  have hi (R : ℝ) (hR : 0≤R) (_ : (R:EReal)<⊤) :
      ∀ᵐ w ∂P,Integrable (fun r => (g r)^2) (volume.restrict (Ioc 0 R)) :=
    Filter.Eventually.of_forall (fun _ => ((hg.pow 2).intervalIntegrable 0 R).1)
  obtain ⟨hc,hZ,hbound⟩ := brownian_progressive_ito_finite_path_moment P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null (B.W j) (B.C j j) N (fun z => g z.2)
    (B.martingale j) (B.cov j j) hCm hCc hclock hp hi hN hNI T hT
    (EReal.coe_lt_top _) (show Integrable (fun _ : Ω => ∫ s in 0..T,(g s)^2) P from integrable_const _)
  refine ⟨finiteRealPath N T hc,
    finite_real_path_measurable B.F B.le N T (EReal.coe_lt_top _) hc (hN.adapted P B.F),
    hZ,fun _ _ => rfl,?_⟩
  simpa only [integral_const,probReal_univ,one_smul] using hbound

end Asakura.Chapter10
