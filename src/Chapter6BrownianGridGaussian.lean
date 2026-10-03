import Chapter4BrownianSystem
import Chapter6FiniteGaussianRegression

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The law of every linear functional of the actual Brownian grid. -/
theorem brownian_grid_linear_map_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (h : ℝ) (hh : 0≤h) (n : ℕ) (L : (Fin n → Fin d → ℝ) →L[ℝ] ℝ) :
    (P.map (finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h n)).map L=
      gaussianReal 0 ⟨h*(∑ k : Fin n,∑ j : Fin d,L (Pi.single k (Pi.single j 1))^2),
        mul_nonneg hh (sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _)))⟩ := by
  let Z := finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h n
  obtain ⟨hm,hchar,_⟩ := B.grid_law h hh n
  let v : ℝ≥0 := ⟨h*(∑ k : Fin n,∑ j : Fin d,L (Pi.single k (Pi.single j 1))^2),
    mul_nonneg hh (sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _)))⟩
  change (P.map Z).map L=gaussianReal 0 v
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_map_eq_charFunDual_smul,hchar,charFun_gaussianReal]
  dsimp only [gridNoiseCharacteristic]
  rw [← Complex.exp_sum]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,mul_pow]
  congr 1
  have hv : (v:ℂ)=((h*(∑ k : Fin n,∑ j : Fin d,L (Pi.single k (Pi.single j 1))^2):ℝ):ℂ) := rfl
  rw [hv]
  push_cast
  simp only [← Finset.mul_sum,← Finset.sum_div,← Finset.sum_neg_distrib]
  ring

/-- Joint Gaussianity is obtained from these actual scalar laws. -/
theorem brownian_grid_has_gaussian_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (h : ℝ) (hh : 0≤h) (n : ℕ) :
    HasGaussianLaw (finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h n) P := by
  refine ⟨(B.grid_law h hh n).1.aemeasurable,?_⟩
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  exact ⟨0,_,brownian_grid_linear_map_law P B h hh n L⟩

end Asakura.Chapter6
