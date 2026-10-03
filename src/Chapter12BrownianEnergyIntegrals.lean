import Chapter12CanonicalClock
import Chapter12WienerItoConstruction
open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5

theorem brownian_energy_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d) (i : Fin d)
    (H : progressiveEnergyIntegrands B.F canonicalClock (P.prod (volume.restrict (Ioi (0:ℝ))))) :
    ∃ N : HalfClosedTime → Ω → ℝ,ContinuousM2Witness P B.F N ∧ ItoCovarianceFormula P B.F (B.W i) H.val N := by
  obtain ⟨hc,hcm,hct,hcut,hcc,hco⟩ := canonical_clock_properties
  obtain ⟨I,hI⟩ := brownian_L2_isometry_constructed P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null (B.W i) (B.C i i) (B.martingale i) (B.cov i i)
    canonicalClock hc hcm (fun _ => EReal.coe_lt_top _) hct hcut hcc
    (fun _ w t ht => B.diagonal_clock i w t ht.1) hco
  obtain ⟨N,hN,hNI,_⟩ := hI H
  exact ⟨N,hN,hNI⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_energy_integral
