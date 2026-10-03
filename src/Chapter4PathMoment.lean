import Chapter4FinitePathNorm
import Chapter4EulerEstimates
import Chapter2EnergyNorm

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter4
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false

/-- Convert the L2 maximal estimate to the squared path moment appearing
in the manuscript. Square integrability is a consequence of the bound. -/
theorem path_square_moment_of_eLp_bound
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (Y : Ω → E) (B : ℝ) (hB : 0 ≤ B)
    (hn : eLpNorm Y 2 P ≤ ENNReal.ofReal (2*Real.sqrt B)) :
    MemLp Y 2 P ∧ (∫ ω, ‖Y ω‖^2 ∂P) ≤ 4*B := by
  have hy : MemLp Y 2 P := hn.trans_lt ENNReal.ofReal_lt_top
  have he := real_eLpNorm_two_energy P (fun ω => ‖Y ω‖) hy.norm
  rw [eLpNorm_norm Y hy.aestronglyMeasurable] at he
  rw [he] at hn
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn
  have hE : 0 ≤ ∫ ω, ‖Y ω‖^2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
  simp only [← ENNReal.toReal_rpow,ENNReal.toReal_ofReal hE,
    ENNReal.toReal_ofReal (show 0 ≤ 2*Real.sqrt B by positivity),← Real.sqrt_eq_rpow] at hr
  refine ⟨hy,?_⟩
  nlinarith [Real.sq_sqrt hE,Real.sq_sqrt hB,
    Real.sqrt_nonneg (∫ ω, ‖Y ω‖^2 ∂P),Real.sqrt_nonneg B]

/-- Combine drift and martingale parts in the squared supremum norm.
All integrability required by the integral inequality is derived from L2. -/
theorem path_sum_square_moment
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (D Z : Ω → E) (hD : MemLp D 2 P) (hZ : MemLp Z 2 P) :
    MemLp (fun ω => D ω+Z ω) 2 P ∧
    (∫ ω, ‖D ω+Z ω‖^2 ∂P) ≤
      2*(∫ ω, ‖D ω‖^2 ∂P)+2*(∫ ω, ‖Z ω‖^2 ∂P) := by
  have hsum := hD.add hZ
  have hiD := hD.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hiZ := hZ.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∫ ω, (2*‖D ω‖^2+2*‖Z ω‖^2) ∂P := by
      apply integral_mono (hsum.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
        ((hiD.const_mul 2).add (hiZ.const_mul 2))
      intro ω
      change ‖D ω+Z ω‖^2 ≤ 2*‖D ω‖^2+2*‖Z ω‖^2
      have hn := norm_add_le (D ω) (Z ω)
      nlinarith [norm_nonneg (D ω),norm_nonneg (Z ω),norm_nonneg (D ω+Z ω),
        sq_nonneg (‖D ω‖-‖Z ω‖)]
    _ = _ := by rw [integral_add (hiD.const_mul 2) (hiZ.const_mul 2),integral_const_mul,integral_const_mul]

/-- Convert squared moments to the L2 seminorm, retaining the actual random
path rather than passing to an unspecified Banach-space element. -/
theorem path_eLpNorm_eq_sqrt_moment
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (Y : Ω → E) (hi : MemLp Y 2 P) :
    eLpNorm Y 2 P = ENNReal.ofReal (Real.sqrt (∫ ω, ‖Y ω‖^2 ∂P)) := by
  have he := real_eLpNorm_two_energy P (fun ω => ‖Y ω‖) hi.norm
  rw [eLpNorm_norm Y hi.aestronglyMeasurable] at he
  rw [he,Real.sqrt_eq_rpow,ENNReal.ofReal_rpow_of_nonneg
    (integral_nonneg (fun ω => sq_nonneg _)) (by norm_num)]

theorem path_eLpNorm_bound_of_squared_moment
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (U V : Ω → E) (hiU : MemLp U 2 P) (hiV : MemLp V 2 P)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : (∫ ω, ‖U ω‖^2 ∂P) ≤ K*(∫ ω, ‖V ω‖^2 ∂P)) :
    eLpNorm U 2 P ≤ ENNReal.ofReal (Real.sqrt K)*eLpNorm V 2 P := by
  rw [path_eLpNorm_eq_sqrt_moment P U hiU,path_eLpNorm_eq_sqrt_moment P V hiV,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.sqrt (K*(∫ ω, ‖V ω‖^2 ∂P)) := Real.sqrt_le_sqrt hb
    _ = _ := Real.sqrt_mul hK _

end Asakura.Chapter4
