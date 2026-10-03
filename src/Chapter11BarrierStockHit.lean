import Chapter11BarrierPrintedHedge

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter7
set_option maxHeartbeats 2000000

/-- The logarithmic barrier used in Lean is exactly the stock-price
barrier in the text, with the same initial condition and first hit. -/
theorem barrier_stock_log_coordinates (b s : ℝ) (hb : 0<b) (hs : 0<s) (hsb : s<b) :
    Real.log (s/b)<0 ∧ b*Real.exp (Real.log (s/b))=s ∧
      ∀ a : ℝ,b*Real.exp (Real.log (s/b)+a)=s*Real.exp a := by
  have hx := div_pos hs hb
  refine ⟨Real.log_neg hx (div_lt_one hb |>.mpr hsb),?_,?_⟩
  · rw [Real.exp_log hx]
    field_simp
  · intro a
    rw [Real.exp_add,Real.exp_log hx]
    field_simp

theorem barrier_hit_stock_equivalence (b : ℝ) (hb : 0<b) (X : HalfClosedTime → ℝ) :
    upperBarrierHit X=sInf {t : HalfClosedTime | t=⊤ ∨ b≤b*Real.exp (X t)} := by
  unfold upperBarrierHit
  congr 1
  ext t
  have he : b≤b*Real.exp (X t) ↔ 0≤X t := by
    calc
      b≤b*Real.exp (X t) ↔ b*Real.exp 0≤b*Real.exp (X t) := by simp
      _ ↔ 0≤X t := by rw [mul_le_mul_iff_right₀ hb,Real.exp_le_exp]
  simp only [upperBarrierHit,mem_setOf_eq,he]

end Asakura.Chapter11
