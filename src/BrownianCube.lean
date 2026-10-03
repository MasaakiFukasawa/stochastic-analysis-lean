import Kolmogorov
import BrownianIncrements

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace Asakura
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma unitCube_one_distance (s t : UnitCube 1) : dist s t = |s.val 0 - t.val 0| := by
  simp [Subtype.dist_eq, dist_pi_def, Real.dist_eq]

lemma brownian_cube_lp (X : UnitCube 1 → Ω → ℝ) (hG : IsGaussianProcess X P)
    (hm : ∀ t, (∫ ω, X t ω ∂P) = 0)
    (hc : ∀ s t, (∫ ω, X s ω * X t ω ∂P) = min (s.val 0) (t.val 0))
    (p : ℝ≥0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ s t, eLpNorm (X s - X t) p P ≤
      ENNReal.ofReal (c * (dist s t) ^ (1/2 : ℝ)) := by
  let C := eLpNorm id p (gaussianReal 0 1)
  have hC : C ≠ ∞ := (memLp_id_gaussianReal p).eLpNorm_ne_top
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro s t
  rw [gaussian_increment_lp (gaussian_brownian_increment_law X hG
    (fun s => s.val 0) hm hc s t), Real.coe_toNNReal _ (abs_nonneg _)]
  rw [← unitCube_one_distance, Real.sqrt_eq_rpow, mul_comm C.toReal,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hC]

/-- For each α<1/2, construct a continuous modification with α-Holder sample paths. -/
theorem brownian_cube_holder_modification (X : UnitCube 1 → Ω → ℝ)
    (hX : ∀ t, Measurable (X t)) (hG : IsGaussianProcess X P)
    (hm : ∀ t, (∫ ω, X t ω ∂P) = 0)
    (hc : ∀ s t, (∫ ω, X s ω * X t ω ∂P) = min (s.val 0) (t.val 0))
    (α : ℝ) (hα : 0 < α) (hαh : α < 1/2) :
    ∃ (Y : UnitCube 1 → Ω → ℝ) (M : Ω → ℝ),
      (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Y t =ᵐ[P] X t) ∧ Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
      (∀ ω s t, dist (Y s ω) (Y t ω) ≤ M ω * (dist s t)^α) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (1 / (1/2 - α)))
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn0 : (0 : ℝ) < n := by linarith
  have he : α < 1/2 - 1 / (n : ℝ) := by
    have hn' : 1 / (1/2 - α) < (n : ℝ) := (le_max_right _ _).trans_lt hn
    have hh := (div_lt_iff₀ (by linarith : (0 : ℝ) < 1/2 - α)).mp hn'
    have hi : 1 / (n : ℝ) < 1/2 - α := (div_lt_iff₀ hn0).mpr (by nlinarith)
    linarith
  obtain ⟨c, hc0, hbound⟩ := brownian_cube_lp X hG hm hc (n : ℝ≥0)
  have hp : (1 : ℝ≥0) ≤ n := by exact_mod_cast hn1.le
  have hh : ∀ s t, eLpNorm (X s - X t) (n : ℝ≥0) P ≤
      ENNReal.ofReal (c * (dist s t) ^ ((1/2 - 1/(n:ℝ)) + 1/(n:ℝ))) := by
    simpa only [sub_add_cancel] using hbound
  obtain ⟨Y, M, hYm, hYc, hYX, hMm, hM0, hYH, _⟩ :=
    kolmogorov_cube_holder P X hX (n : ℝ≥0) hp c (1/2 - 1/(n:ℝ)) α hc0 hα he
      (by simpa using hh)
  exact ⟨Y, M, hYm, hYc, hYX, hMm, hM0, hYH⟩
end Asakura
