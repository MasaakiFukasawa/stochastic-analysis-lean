import Chapter12BrownianUnitDirection
import Chapter12BrownianEnergyIntegrals
import Chapter12ItoIntegratorLinear
import Chapter5LeftItoFiniteSum
import Chapter12GaussianMartingaleTerminal

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem brownian_direction_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (u : Fin (d+1) → ℝ) (hu : ∑ i,u i^2=1)
    (φ : progressiveEnergyIntegrands B.F canonicalClock (P.prod (volume.restrict (Ioi (0:ℝ))))) :
    ∃ Q : Fin (d+1) → HalfClosedTime → Ω → ℝ,
      (∀ j,ContinuousM2Witness P B.F (Q j)) ∧
      (∀ j,ItoCovarianceFormula P B.F (B.W j) (fun z => u j*φ.val z) (Q j)) ∧
      ContinuousM2Witness P B.F (fun t w => ∑ j,Q j t w) ∧
      ItoCovarianceFormula P B.F ((brownianUnitDirection P B u hu).W 0) φ.val (fun t w => ∑ j,Q j t w) := by
  choose Z hZ hZI using fun j => brownian_energy_integral P B j φ
  let Q := fun j t w => u j*Z j t w
  have hQ j : ContinuousM2Witness P B.F (Q j) := (hZ j).smul P B.F (u j)
  have hQI j : ItoCovarianceFormula P B.F (B.W j) (fun z => u j*φ.val z) (Q j) := by
    convert (hZI j).add_smul P B.F B.mono B.le (B.W j) (Z j) (Z j) φ.val φ.val (hZI j) (u j-1) using 1
    · funext z;ring
    · funext t w;dsimp only [Q];ring
  have hsum : ContinuousM2Witness P B.F (fun t w => ∑ j,Q j t w) := by
    exact finite_sum_continuous_m2 P B.F B.mono B.le Q hQ
  have hscaled j : ItoCovarianceFormula P B.F (fun t w => u j*B.W j t w) φ.val (Q j) := by
    obtain ⟨hc,hcm,hct,hcut,hcc,hco⟩ := canonical_clock_properties
    have hZl := continuous_m2_is_local P B.F B.mono B.le
      (fun n => realTimeClamp (T:=⊤) (canonicalClock n)) hct.monotone hcut hcc (Z j) (hZ j)
    exact ito_integrator_smul P (by simp) B.F B.mono B.le B.null (B.W j) (Z j) φ.val (u j)
      (B.martingale j) hZl (fun w => φ.property.1.comp measurable_prodMk_left) (hZI j)
  refine ⟨Q,hQ,hQI,hsum,?_⟩
  exact ito_integrator_nonempty_sum P (by simp) B.F B.mono B.le B.null d
    (fun j t w => u j*B.W j t w) Q φ.val (fun j => (B.martingale j).smul P B.F (u j)) hscaled

end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_direction_integral
