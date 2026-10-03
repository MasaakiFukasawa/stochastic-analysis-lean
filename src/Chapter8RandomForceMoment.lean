import Chapter8LipschitzGrowthData
import Chapter8RandomPositionMoment

open MeasureTheory Set
open scoped NNReal ENNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- A globally Lipschitz force preserves finite second moments and has
exactly the quadratic-growth bound used in the first Gronwall step. -/
theorem random_lipschitz_force_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g) :
    ∃ G : ℝ,0≤G ∧ ∀ X : Ω → E,MemLp X 2 P →
      MemLp (fun w => g (X w)) 2 P ∧
      (∫ w,‖g (X w)‖^2 ∂P)≤G*(1+∫ w,‖X w‖^2 ∂P) := by
  obtain ⟨C,hC,hgC⟩ := lipschitz_linear_growth g L hg
  refine ⟨2*C^2,by positivity,?_⟩
  intro X hX
  have hdiff : LipschitzWith L (fun x => g x-g 0) := by
    simpa only [add_zero] using hg.sub (LipschitzWith.const (g 0))
  have hh := hdiff.comp_memLp (by simp) hX
  have hgi : MemLp (fun w => g (X w)) 2 P := by
    have hc : MemLp (fun _ : Ω => g 0) 2 P := memLp_const _
    have hsum : MemLp (fun w => (g (X w)-g 0)+g 0) 2 P := hh.add hc
    simpa only [sub_add_cancel] using hsum
  refine ⟨hgi,?_⟩
  have hpoint w : ‖g (X w)‖^2≤2*C^2*(1+‖X w‖^2) := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) (hgC (X w)) 2
    have hp := mul_nonneg (sq_nonneg C) (sq_nonneg (‖X w‖-1))
    nlinarith
  have hXsq := hX.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hI : Integrable (fun w => 2*C^2*(1+‖X w‖^2)) P := ((integrable_const 1).add hXsq).const_mul _
  have hb := integral_mono (hgi.integrable_norm_pow (by norm_num : (2:ℕ)≠0)) hI hpoint
  rw [integral_const_mul,integral_add (integrable_const 1) hXsq] at hb
  simpa using hb

/-- The Lipschitz difference bound used for Q-X is a second-moment
inequality for the actual random forces. -/
theorem random_force_difference {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (X Y : Ω → E) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    MemLp (fun w => g (X w)-g (Y w)) 2 P ∧
      (∫ w,‖g (X w)-g (Y w)‖^2 ∂P)≤(L:ℝ)^2*(∫ w,‖X w-Y w‖^2 ∂P) := by
  obtain ⟨G,hG,hgG⟩ := random_lipschitz_force_moment P g L hg
  have hdiff : MemLp (fun w => g (X w)-g (Y w)) 2 P := ((hgG X hX).1).sub ((hgG Y hY).1)
  refine ⟨hdiff,?_⟩
  rw [←integral_const_mul]
  have hXY : MemLp (fun w => X w-Y w) 2 P := hX.sub hY
  apply integral_mono (hdiff.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    ((hXY.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul _)
  intro w
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hg.norm_sub_le (X w) (Y w)) 2
end Asakura.Chapter8
