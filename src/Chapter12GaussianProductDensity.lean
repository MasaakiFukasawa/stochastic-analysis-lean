import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem finite_product_absolutelyContinuous_volume (d : ℕ)
    (μ : Fin d → Measure ℝ) [∀ i,SigmaFinite (μ i)]
    (hμ : ∀ i,μ i ≪ volume) : Measure.pi μ ≪ volume := by
  induction d with
  | zero =>
    rw [Measure.pi_of_empty,Measure.volume_pi_eq_dirac]
  | succ d ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0
    have heμ := measurePreserving_piFinSuccAbove μ 0
    have hev := volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0
    have hp := (hμ 0).prod (ih (fun i => μ (Fin.succAbove 0 i)) (fun i => hμ _))
    have hh := hp.map e.symm.measurable
    rw [heμ.symm.map_eq] at hh
    change Measure.pi μ ≪ (volume : Measure (ℝ × (Fin d → ℝ))).map e.symm at hh
    rw [hev.symm.map_eq] at hh
    exact hh

theorem gaussian_product_absolutelyContinuous_volume (d : ℕ) (T : ℝ≥0) (hT : T≠0) :
    (Measure.pi (fun _ : Fin d => gaussianReal 0 T)) ≪ volume :=
  finite_product_absolutelyContinuous_volume d _ (fun _ => gaussianReal_absolutelyContinuous 0 hT)

end Asakura.Chapter12
