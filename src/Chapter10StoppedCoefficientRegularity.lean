import Chapter10IntegrableNoiseLaw
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set Filter
open scoped BigOperators
namespace Asakura.Chapter10
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

lemma bounded_interval_integrable (f : ℝ → ℝ) (hf : Measurable f) (b C : ℝ) (hb : 0≤b)
    (hbound : ∀ s∈Icc 0 b,‖f s‖≤C) : IntervalIntegrable f volume 0 b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with s hs
  exact hbound s ⟨hs.1.le,hs.2⟩

/-- Finite linear combinations of continuously weighted stopped integrands
have all local product integrability needed for the Gaussian calculation. -/
theorem stopped_coefficient_regularity {p n : ℕ}
    (G : Fin p → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (v τ : Fin p → ℝ) :
    let H := fun j s => ∑ i,v i*(Ioc 0 (τ i)).indicator (G i j) s
    (∀ j,Measurable (H j)) ∧
      (∀ j b,0≤b → IntervalIntegrable (H j) volume 0 b) ∧
      (∀ i j b,0≤b → IntervalIntegrable (fun s => H i s*H j s) volume 0 b) := by
  let H := fun j s => ∑ i,v i*(Ioc 0 (τ i)).indicator (G i j) s
  have hm j : Measurable (H j) := Finset.measurable_sum _ (fun i _ =>
    measurable_const.mul ((hG i j).measurable.indicator measurableSet_Ioc))
  have hbnd b : ∃ C,0≤C ∧ ∀ j s,s∈Icc (0:ℝ) b → ‖H j s‖≤C := by
    have hc : Continuous (fun s i j => G i j s) := continuous_pi (fun i => continuous_pi (fun j => hG i j))
    obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := b)).exists_bound_of_continuousOn hc.continuousOn
    let c := max C 0
    refine ⟨(∑ i,‖v i‖)*c,mul_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (le_max_right _ _),?_⟩
    intro j s hs
    have hgs i : ‖G i j s‖≤c :=
      ((norm_le_pi_norm (fun j => G i j s) j).trans
        (norm_le_pi_norm (fun i j => G i j s) i)).trans ((hC s hs).trans (le_max_left _ _))
    calc
      ‖H j s‖ ≤ ∑ i,‖v i*(Ioc 0 (τ i)).indicator (G i j) s‖ := norm_sum_le _ _
      _ ≤ ∑ i,‖v i‖*c := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        by_cases ht : s ∈ Ioc 0 (τ i)
        · simpa only [Set.indicator_of_mem ht] using hgs i
        · simp only [Set.indicator_of_notMem ht,norm_zero]
          exact le_max_right _ _
      _ = _ := (Finset.sum_mul _ _ _).symm
  refine ⟨hm,?_,?_⟩
  · intro j b hb
    obtain ⟨C,_,hC⟩ := hbnd b
    exact bounded_interval_integrable (H j) (hm j) b C hb (hC j)
  · intro i j b hb
    obtain ⟨C,hC0,hC⟩ := hbnd b
    apply bounded_interval_integrable _ ((hm i).mul (hm j)) b (C^2) hb
    intro s hs
    change ‖H i s * H j s‖ ≤ C^2
    rw [norm_mul,pow_two]
    exact mul_le_mul (hC i s hs) (hC j s hs) (norm_nonneg _) hC0

end Asakura.Chapter10
