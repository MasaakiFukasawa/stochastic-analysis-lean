import CubeMoments
import HolderModification
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace Asakura

/-- Kolmogorov's theorem on the actual d-dimensional cube, for one positive
Holder exponent. No grid, summability, continuity, or modification hypothesis
is assumed: all are constructed from the manuscript's increment bound.
The displayed constant is the sharper maximum-norm constant. -/
theorem kolmogorov_cube_holder {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : UnitCube d → Ω → ℝ) (hX : ∀ s, Measurable (X s))
    (p : ℝ≥0) (hp : 1 ≤ p) (c ε α : ℝ) (hc : 0 ≤ c)
    (hα : 0 < α) (hαε : α < ε)
    (h : ∀ s t, eLpNorm (X s - X t) p μ ≤
      ENNReal.ofReal (c * (dist s t)^(ε + d/(p:ℝ)))) :
    ∃ (Y : UnitCube d → Ω → ℝ) (M : Ω → ℝ),
      (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Y t =ᵐ[μ] X t) ∧ Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
      (∀ ω s t, dist (Y s ω) (Y t ω) ≤ M ω * (dist s t)^α) ∧
      eLpNorm M p μ ≤ ENNReal.ofReal
        ((2 * 2^α) * ((c * (6:ℝ)^(d/(p:ℝ))) / (1 - 2^α * 2^(-ε)))) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hpReal : 0 < (p:ℝ) := NNReal.coe_pos.mpr hp0
  have hε : 0 < ε := hα.trans hαε
  have hβ : 0 < ε + d/(p:ℝ) := by positivity
  have hstoch := stochastic_continuity_of_power_bound μ X (p:ℝ≥0∞)
    (by exact_mod_cast hp0.ne') c (ε+d/(p:ℝ)) hβ h
  let K := cubeIncrementMax X
  have hdecay := cube_increment_lp_decay μ X hX p hp0 c ε hc hε h
  have hqr : (2:ℝ)^α * 2^(-ε) < 1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hW := weighted_geometric_lp μ (p:ℝ≥0∞) K
    (c * (6:ℝ)^(d/(p:ℝ))) (2^α) (2^(-ε)) (by positivity)
    (by positivity) (by positivity) hqr hdecay
  have hfinite : ∑' n, eLpNorm (fun ω => (2^α : ℝ)^n * K n ω) p μ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hW
  let D := DyadicSet d
  let a : ℕ → D → D := fun n s => ⟨roundCube n s.val, roundCube_mem n s.val⟩
  have hfix : ∀ s : D, ∃ N, ∀ n ≥ N, a n s = s := by
    intro s
    obtain ⟨N,hN⟩ := roundCube_eventually_fixed s.val s.property
    exact ⟨N, fun n hn => Subtype.ext (hN n hn)⟩
  have hdiam : ∀ s t : D, dist s t ≤ 1 := by
    intro s t
    exact cube_diameter d s.val.val t.val.val s.val.property t.val.property
  obtain ⟨Y,M,hYm,hYc,hYX,hMm,hM0,hYH,hMbound⟩ :=
    holder_modification_of_dyadic_lp μ D (dyadicSet_dense d) X hX hstoch a K
      (cubeIncrementMax_measurable X hX) (cubeIncrementMax_nonneg X) (p:ℝ≥0∞)
      (by exact_mod_cast hp) α hα hdiam hfinite hfix
      (fun ω n s => cubeIncrementMax_step X n s.val ω)
      (fun ω n s t hst => cubeIncrementMax_near X n s.val t.val hst ω)
  refine ⟨Y,M,hYm,hYc,hYX,hMm,hM0,hYH,hMbound.trans ?_⟩
  rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2*2^α)]
  exact mul_le_mul_of_nonneg_left hW (by positivity)
end Asakura
