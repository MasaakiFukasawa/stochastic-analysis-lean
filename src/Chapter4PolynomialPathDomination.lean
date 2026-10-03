import Chapter4VectorRealPath
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4.Vector
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

lemma polynomial_norm_memLp_two {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → E) (N : ℕ) (C : ℝ) (hY : MemLp Y (2*(N:ℝ≥0∞)) P) :
    MemLp (fun w => C*(1+‖Y w‖^N)) 2 P := by
  by_cases hN : N=0
  · subst N
    simpa only [pow_zero] using (memLp_const (C*(1+1)) : MemLp (fun _ : Ω => C*(1+1)) 2 P)
  have hNe : (N:ℝ≥0∞)≠0 := by exact_mod_cast hN
  have hh := hY.norm_rpow_div (N:ℝ≥0∞)
  have hq : (2*(N:ℝ≥0∞))/(N:ℝ≥0∞)=2 := ENNReal.mul_div_cancel_right hNe (by simp)
  simp only [ENNReal.toReal_natCast,Real.rpow_natCast,hq] at hh
  have hconst : MemLp (fun _ : Ω => (1:ℝ)) 2 P := memLp_const 1
  exact (hconst.add hh).const_mul C

/-- Polynomial growth evaluated along a continuous state path has a
square-integrable uniform random bound, supplied by the proved higher
path moment. -/
theorem polynomial_path_uniform_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] {d : ℕ}
    (X : ClosedTime T → Ω → Fin d → ℝ)
    (hXc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (f g : ℝ × (Fin d → ℝ) → ℝ) (N : ℕ) (C : ℝ) (hC : 0≤C)
    (hf : ∀ r∈Icc 0 R,∀ x,|f (r,x)|≤C*(1+‖x‖^N))
    (hg : ∀ r∈Icc 0 R,∀ x,|g (r,x)|≤C*(1+‖x‖^N))
    (hMom : MemLp (realVectorPath X hXc R hRT) (2*(N:ℝ≥0∞)) P) :
    ∃ B : Ω → ℝ,MemLp B 2 P ∧
      ∀ w r,r∈Icc 0 R → |f (r,X (realTimeClamp r) w)|≤B w ∧ |g (r,X (realTimeClamp r) w)|≤B w := by
  let B := fun w => C*(1+‖realVectorPath X hXc R hRT w‖^N)
  refine ⟨B,polynomial_norm_memLp_two P _ N C hMom,?_⟩
  intro w r hr
  have hn : ‖X (realTimeClamp r) w‖≤‖realVectorPath X hXc R hRT w‖ :=
    (realVectorPath X hXc R hRT w).norm_coe_le_norm ⟨r,hr⟩
  have hh : C*(1+‖X (realTimeClamp r) w‖^N)≤B w :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hn N)) hC
  exact ⟨(hf r hr _).trans hh,(hg r hr _).trans hh⟩

end Asakura.Chapter4
