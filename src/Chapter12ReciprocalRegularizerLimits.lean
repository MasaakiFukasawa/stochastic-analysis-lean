import Chapter12ReciprocalRegularizer
import Chapter12DominatedLpLimit

open MeasureTheory Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000

theorem reciprocal_square_regularizer_bound (ε x:ℝ) (hε:0<ε) (hx:0<x) :
    ‖reciprocalSquareRegularizer ε x‖≤‖x⁻¹^2‖ := by
  simp only [reciprocalSquareRegularizer,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by positivity : 0<x^2+ε)),abs_of_nonneg (sq_nonneg (x⁻¹))]
  rw [inv_pow]
  exact inv_anti₀ (sq_pos_of_pos hx) (by linarith)

theorem reciprocal_square_regularizer_limit (x:ℝ) (hx:0<x) :
    Tendsto (fun n:ℕ => reciprocalSquareRegularizer (1/(n+1)) x) atTop (𝓝 (x⁻¹^2)) := by
  have hh := (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).inv₀
    (by positivity : x^2+(0:ℝ)≠0)
  simpa [reciprocalSquareRegularizer,inv_pow] using hh

theorem reciprocal_square_regularizer_Lp_limit {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤)
    (F:Ω → ℝ) (hF:AEStronglyMeasurable F P) (hpos:∀ᵐw∂P,0<F w)
    (hi:MemLp (fun w => (F w)⁻¹^2) p P) :
    ∃hreg:∀n:ℕ,MemLp (fun w => reciprocalSquareRegularizer (1/(n+1)) (F w)) p P,
      Tendsto (fun n => (hreg n).toLp _) atTop (𝓝 (hi.toLp _)) := by
  have hm (n:ℕ) : AEStronglyMeasurable (fun w => reciprocalSquareRegularizer (1/(n+1)) (F w)) P :=
    (reciprocal_square_regularizer_smooth (1/(n+1)) (by positivity)).continuous.comp_aestronglyMeasurable hF
  have hb (n:ℕ) : ∀ᵐw∂P, ‖reciprocalSquareRegularizer (1/(n+1)) (F w)‖≤‖(F w)⁻¹^2‖ := by
    filter_upwards [hpos] with w hw
    exact reciprocal_square_regularizer_bound _ _ (by positivity) hw
  have hreg n := hi.of_le (hm n) (hb n)
  refine ⟨hreg,?_⟩
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hreg _ hi).mpr
  apply dominated_Lp_limit P p Fact.out hp _ _ _ hi hm hi hb
  filter_upwards [hpos] with w hw
  exact reciprocal_square_regularizer_limit (F w) hw
end Asakura.Chapter12
#print axioms Asakura.Chapter12.reciprocal_square_regularizer_Lp_limit
