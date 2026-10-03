import Chapter6BrownianGridGaussian

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem brownian_grid_linear_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (h : ℝ) (hh : 0≤h) (n : ℕ) (L : (Fin n → Fin d → ℝ) →L[ℝ] ℝ) :
    let Z := finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h n
    (∫ w,L (Z w) ∂P)=0 ∧ Var[(fun w => L (Z w));P]=h*(∑ k : Fin n,∑ j : Fin d,L (Pi.single k (Pi.single j 1))^2) := by
  let Z := finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h n
  have hm := (B.grid_law h hh n).1
  have he := brownian_grid_linear_map_law P B h hh n L
  rw [Measure.map_map L.continuous.measurable hm] at he
  have hl : HasLaw (fun w => L (Z w)) (gaussianReal 0 ⟨h*(∑ k : Fin n,∑ j : Fin d,L (Pi.single k (Pi.single j 1))^2),
      mul_nonneg hh (sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _)))⟩) P :=
    ⟨(L.continuous.measurable.comp hm).aemeasurable,he⟩
  refine ⟨?_,?_⟩
  · simpa only [integral_id_gaussianReal] using hl.integral_eq
  · rw [← variance_id_map hl.aemeasurable,hl.map_eq,variance_id_gaussianReal]
    rfl

/-- Covariance of two linear functionals of the actual grid. -/
theorem brownian_grid_linear_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (h : ℝ) (hh : 0≤h) (n : ℕ) (L K : (Fin n → Fin d → ℝ) →L[ℝ] ℝ) :
    let Z := finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h n
    cov[(fun w => L (Z w)),(fun w => K (Z w));P]=
      h*(∑ k : Fin n,∑ j : Fin d,L (Pi.single k (Pi.single j 1))*K (Pi.single k (Pi.single j 1))) := by
  let Z := finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h n
  have hg := brownian_grid_has_gaussian_law P B h hh n
  have hl := brownian_grid_linear_moments P B h hh n L |>.2
  have hk := brownian_grid_linear_moments P B h hh n K |>.2
  have hlk := brownian_grid_linear_moments P B h hh n (L+K) |>.2
  have hv := variance_add (hg.map L).memLp_two (hg.map K).memLp_two
  simp only [ContinuousLinearMap.add_apply] at hlk
  simp only [Function.comp_def,Pi.add_apply] at hv
  rw [hl,hk] at hv
  change Var[(fun w => L (Z w)+K (Z w));P]=_ at hv
  rw [hlk] at hv
  have hs : (∑ k : Fin n,∑ j : Fin d,(L (Pi.single k (Pi.single j 1))+K (Pi.single k (Pi.single j 1)))^2)=
      (∑ k : Fin n,∑ j : Fin d,L (Pi.single k (Pi.single j 1))^2)+
      (∑ k : Fin n,∑ j : Fin d,K (Pi.single k (Pi.single j 1))^2)+
      2*(∑ k : Fin n,∑ j : Fin d,L (Pi.single k (Pi.single j 1))*K (Pi.single k (Pi.single j 1))) := by
    simp only [Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro j _
    ring
  rw [hs] at hv
  linarith

end Asakura.Chapter6
