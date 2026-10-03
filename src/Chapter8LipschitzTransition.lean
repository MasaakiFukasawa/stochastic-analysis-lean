import FullAuditCovarianceDecay

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit

/-- A Lipschitz observable is square-integrable under a finite-second-moment law. -/
theorem lipschitz_observable_memLp {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → E) (hX : MemLp X 2 P) (f : E → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) : MemLp (fun ω => f (X ω)) 2 P := by
  have hzero : LipschitzWith L (fun x => f x-f 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,show (f x-f 0)-(f y-f 0) = f x-f y by ring]
    simpa only [dist_eq_norm] using hf.norm_sub_le x y
  have hh := hzero.comp_memLp (by simp) hX
  have ha := hh.add (memLp_const (f 0))
  convert ha using 1 <;> funext ω <;> simp

/-- Synchronous path contraction gives the Lipschitz constant of P_t f by
integration, including unbounded Lipschitz observables. -/
theorem lipschitz_transition_from_coupling {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : E → Ω → E) (hX : ∀ x, MemLp (X x) 2 P)
    (f : E → ℝ) (L a : ℝ≥0) (hf : LipschitzWith L f)
    (hLip : ∀ x y, ∀ᵐ ω ∂P, ‖X x ω-X y ω‖ ≤ (a:ℝ)*‖x-y‖) :
    LipschitzWith (L*a) (fun x => ∫ ω,f (X x ω) ∂P) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hfx := (lipschitz_observable_memLp P (X x) (hX x) f L hf).integrable (by norm_num)
  have hfy := (lipschitz_observable_memLp P (X y) (hX y) f L hf).integrable (by norm_num)
  rw [Real.dist_eq,← integral_sub hfx hfy]
  have hpoint : ∀ᵐ ω ∂P, ‖f (X x ω)-f (X y ω)‖ ≤ (L*a:ℝ≥0)*‖x-y‖ := by
    filter_upwards [hLip x y] with ω hω
    have hh := (hf.norm_sub_le (X x ω) (X y ω)).trans
      (mul_le_mul_of_nonneg_left hω L.coe_nonneg)
    simpa only [NNReal.coe_mul,mul_assoc] using hh
  have hh := norm_integral_le_of_norm_le_const hpoint
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one,NNReal.coe_mul,dist_eq_norm] using hh

end Asakura.Chapter8
