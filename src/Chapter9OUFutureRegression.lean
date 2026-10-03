import Chapter9OUTwoTimeDensity
import Chapter9OUTransitionBounded
import Chapter9GaussianRegressionPullback
import Chapter9ReverseInformation
import Chapter9ObservationReindex

open MeasureTheory Matrix Set
open scoped NNReal ENNReal
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false

/-- Reverse conditioning for the actual OU solution given its entire future.
The forward transitions, Bayes regression, finite-cylinder induction, and
monotone-class extension are all connected to the same stochastic integrals. -/
theorem standard_ou_future_regression {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ)
    (s t : ℝ) (hs : 0≤s) (hst : s<t)

    (f : (Fin d → ℝ) → ℝ) (hf : IsBoundedBorel f) :
    let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
    P[(fun w => f (X s w))|MeasurableSpace.comap (fun w (r : Ici t) => X r w) MeasurableSpace.pi]=ᵐ[P]
      (fun w => gaussianPosteriorTest (P.map (X s)) (Real.exp (-(t-s))) (1-Real.exp (-2*(t-s))) f (X t w)) := by
  let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
  have hXa r := standard_ou_adapted P B N hN ξ hξ r
  have hXm r : Measurable (X r) := (hXa r).mono (B.le _) le_rfl
  let μ := P.map (X s)
  haveI : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff (hXm s).aemeasurable).mpr inferInstance
  let v : ℝ≥0 := ⟨1-Real.exp (-2*(t-s)),(ou_variance_positive (t-s) (sub_pos.mpr hst)).le⟩
  have hv : v≠0 := by
    intro he
    exact (ou_variance_positive (t-s) (sub_pos.mpr hst)).ne' (congrArg (fun z : ℝ≥0 => (z:ℝ)) he)
  let R := gaussianPosteriorTest μ (Real.exp (-(t-s))) v f
  have hR : IsBoundedBorel R := gaussian_posterior_bounded_borel μ _ v hv f hf
  have hreg := gaussian_transition_regression P μ (X s) (X t) (hXm s) (hXm t)
    (Real.exp (-(t-s))) v hv (standard_ou_two_time_density P B N hN hNI ξ hξ s t hs hst) f hf
  let tt : Ici (0:ℝ) := ⟨t,hs.trans hst.le⟩
  have he := reverse_information_regression P
    (fun r : Ici (0:ℝ) => B.F (realTimeClamp r))
    (fun r u hru => B.mono (real_time_clamp_mono hru)) (fun r => B.le _)
    (fun r : Ici (0:ℝ) => X r) (fun r => hXa r)
    (fun r u hru g hg => standard_ou_bounded_transition P B N hN hNI ξ hξ r u r.property hru g hg)
    tt (fun w => f (X s w)) (hf.comp (X s) (hXm s))
    (hf.1.comp ((hXa s).mono (B.mono (real_time_clamp_mono hst.le)) le_rfl)) R hR hreg
  have hinfo := observation_information_congr
    (fun r : {r : Ici (0:ℝ) // tt≤r} => X r.val)
    (fun r : Ici t => X r)
    (fun r => ⟨⟨r.val.val,r.property⟩,rfl⟩)
    (fun r => ⟨⟨⟨r.val,(hs.trans hst.le).trans r.property⟩,r.property⟩,rfl⟩)
  rw [hinfo] at he
  exact he
end Asakura.Chapter9
