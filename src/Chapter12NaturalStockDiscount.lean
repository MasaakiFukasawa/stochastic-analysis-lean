import Chapter12AsianStockGains

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The stock used by the constructed Ito formula is exactly the printed
Black--Scholes stock after discounting. -/
theorem natural_stock_discount {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hc : ∀ w,Continuous (fun t => B t w)) (x σ r T : ℝ)
    (w : Ω) (t : Icc (0:ℝ) T) :
    Real.exp (-r*t.val)*stockPathValue x σ r T (brownianCompactPath B hc T w) t=
      geometricFlow x 0 σ ![t.val,(naturalBrownianSystem P B hB hm hc).W 0 (realTimeClamp t.val) w] := by
  have ht : halfTimeReal (realTimeClamp (T:=⊤) t.val)=⟨t.val,t.property.1⟩ :=
    Subtype.ext (changed_time_real t.val t.property.1)
  change Real.exp (-r*t.val)*(x*Real.exp ((r-σ^2/2)*t.val+σ*B ⟨t.val,t.property.1⟩ w))=
    x*Real.exp ((0-σ^2/2)*t.val+σ*B (halfTimeReal (realTimeClamp t.val)) w)
  rw [ht,← mul_assoc,mul_comm (Real.exp (-r*t.val)) x,mul_assoc,← Real.exp_add]
  congr 2
  ring

end Asakura.Chapter12
#print axioms Asakura.Chapter12.natural_stock_discount
