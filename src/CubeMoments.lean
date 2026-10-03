import CubeGraph
import PowerDecay
open MeasureTheory Set
open scoped ENNReal NNReal
namespace Asakura

/-- Adjacent grid vertices are at most one mesh apart in the maximum norm. -/
theorem gridEdge_distance {d : ℕ} (m : ℕ) (e : GridEdge d (2^m)) :
    dist (gridPoint m e.val.1) (gridPoint m e.val.2) ≤ (1/2 : ℝ)^m := by
  change ‖(gridPoint m e.val.1).val - (gridPoint m e.val.2).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change |((e.val.1 i).val : ℝ)/(2:ℝ)^m - ((e.val.2 i).val : ℝ)/(2:ℝ)^m| ≤ _
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0:ℝ)<2^m), one_div_pow]
  apply (div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<2^m)).mpr
  exact_mod_cast e.property i

/-- C.2: the original increment hypothesis implies geometric decay of grid maxima.
The maximum norm gives this slightly sharper constant without a factor sqrt(d). -/
theorem cube_increment_lp_decay {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : UnitCube d → Ω → ℝ) (hX : ∀ s, Measurable (X s))
    (p : ℝ≥0) (hp : 0 < p) (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε)
    (h : ∀ s t, eLpNorm (X s - X t) p μ ≤
      ENNReal.ofReal (c * (dist s t)^(ε + d/(p:ℝ)))) (m : ℕ) :
    eLpNorm (cubeIncrementMax X m) p μ ≤
      ENNReal.ofReal (c * (6:ℝ)^(d/(p:ℝ)) * ((2:ℝ)^(-ε))^m) := by
  have hp0 : 0 < (p : ℝ) := NNReal.coe_pos.mpr hp
  have hβ : 0 ≤ ε + d/(p:ℝ) := by positivity
  let F : GridEdge d (2^m) → Ω → ℝ := fun e ω =>
    X (gridPoint m e.val.1) ω - X (gridPoint m e.val.2) ω
  have hF : ∀ e, Measurable (F e) := fun e => (hX _).sub (hX _)
  have hb : ∀ e, eLpNorm (F e) p μ ≤
      ENNReal.ofReal (c * ((1/2:ℝ)^m)^(ε+d/(p:ℝ))) := by
    intro e
    exact (h _ _).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg (gridEdge_distance m e) hβ) hc))
  have hmax := finite_maximum_lp_bound μ p hp.ne' F hF _ hb
  have hcardNat : Fintype.card (GridEdge d (2^m)) ≤ (6*2^m)^d := by
    have hh := dyadic_grid_edge_cardinality d m
    apply hh.trans_eq
    rw [mul_pow, ← pow_mul]
    ring
  have hcardReal : (Fintype.card (GridEdge d (2^m)) : ℝ) ≤ (6*(2:ℝ)^m)^d := by
    exact_mod_cast hcardNat
  have hcard : (Fintype.card (GridEdge d (2^m)) : ℝ≥0∞) ≤
      ENNReal.ofReal ((6*(2:ℝ)^m)^d) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcardReal
  calc
    eLpNorm (cubeIncrementMax X m) p μ ≤
        (Fintype.card (GridEdge d (2^m)) : ℝ≥0∞)^(1/(p:ℝ)) *
          ENNReal.ofReal (c * ((1/2:ℝ)^m)^(ε+d/(p:ℝ))) := hmax
    _ ≤ (ENNReal.ofReal ((6*(2:ℝ)^m)^d))^(1/(p:ℝ)) *
          ENNReal.ofReal (c * ((1/2:ℝ)^m)^(ε+d/(p:ℝ))) :=
      mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hcard (by positivity)) (by positivity)
    _ = ENNReal.ofReal ((((6*(2:ℝ)^m)^d)^(1/(p:ℝ))) *
          (c * ((1/2:ℝ)^m)^(ε+d/(p:ℝ)))) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
      exact (ENNReal.ofReal_mul (by positivity)).symm
    _ = _ := by rw [dyadic_dimension_cancellation d m (p:ℝ) ε c hp0]
end Asakura
