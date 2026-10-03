import Chapter5Contraction
import Chapter5WeightedSpace
import Mathlib.Analysis.InnerProductSpace.ProdL2

open MeasureTheory
namespace Asakura.Chapter5

/-- Assemble the two a-priori bounds using the sum-of-squares product
norm. The ordinary product supremum norm is not silently substituted. -/
theorem bsde_product_fixed_point {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [CompleteSpace H]
    (F : WithLp 2 (H × H) → WithLp 2 (H × H))
    (D : WithLp 2 (H × H) → WithLp 2 (H × H) → ℝ)
    (T C β : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C) (hβ : 2*(1+T)*C^2 < β)
    (hY : ∀ x y, ‖(F x).fst-(F y).fst‖^2 ≤ (T/β)*D x y)
    (hZ : ∀ x y, ‖(F x).snd-(F y).snd‖^2 ≤ (1/β)*D x y)
    (hD : ∀ x y, D x y ≤ 2*C^2*(‖x.fst-y.fst‖^2+‖x.snd-y.snd‖^2)) :
    ∃! x, F x = x := by
  have hb : 0 < β := lt_of_le_of_lt (by positivity) hβ
  obtain ⟨hq,hq1⟩ := contraction_ratio T C β hT hβ
  apply fixed_point_from_squared_estimate F (2*(1+T)*C^2/β) hq hq1
  intro x y
  simp only [dist_eq_norm,WithLp.prod_norm_sq_eq_of_L2,WithLp.sub_fst,WithLp.sub_snd]
  calc
    _ ≤ (T/β)*D x y+(1/β)*D x y := add_le_add (hY x y) (hZ x y)
    _ = ((1+T)/β)*D x y := by ring
    _ ≤ ((1+T)/β)*(2*C^2*(‖x.fst-y.fst‖^2+‖x.snd-y.snd‖^2)) :=
      mul_le_mul_of_nonneg_left (hD x y) (by positivity)
    _ = _ := by ring

end Asakura.Chapter5
