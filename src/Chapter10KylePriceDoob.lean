import FullAuditContinuousDoobStrong
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Rational pricing and the identified terminal value give the precise
Doob bound used for admissibility, with constant two for the L2 norm. -/
theorem kyle_price_doob {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} (hT : 0≤T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (p : ClosedTime T → Ω → ℝ) (V : Ω → ℝ)
    (hp : ∀ t,Measurable[F t] (p t))
    (hc : ∀ w t,ContinuousWithinAt (fun s => p s w) (Ici t) t)
    (hV : Integrable V P)
    (hrational : ∀ t,P[V|F t]=ᵐ[P] p t)
    (hterminal : p ⟨T,hT,le_rfl⟩=ᵐ[P] V) :
    (∫⁻ w,(⨆ t,ENNReal.ofReal |p t w|)^(2:ℝ) ∂P)^((1:ℝ)/2) ≤
      2*(∫⁻ w,ENNReal.ofReal |V w|^(2:ℝ) ∂P)^((1:ℝ)/2) := by
  have hterm : (fun w => |p ⟨T,hT,le_rfl⟩ w|)=ᵐ[P] (fun w => |V w|) :=
    hterminal.mono fun w hw => congrArg abs hw
  have hdom t : (fun w => |p t w|) ≤ᵐ[P] P[(fun w => |p ⟨T,hT,le_rfl⟩ w|)|F t] := by
    have hj := norm_condExp_le (μ := P) (m := F t) V
    have he := condExp_congr_ae (m := F t) hterm
    filter_upwards [hj,hrational t,he] with w hw hr he
    simpa only [Real.norm_eq_abs,hr,he] using hw
  have hh := continuous_doob_strong_written P hT F hF hle (fun t w => |p t w|)
    (fun t => by
      letI : MeasurableSpace Ω := F t
      exact continuous_abs.measurable.comp (hp t)) (fun w t => (hc w t).abs)
    (hV.abs.congr hterm.symm) (fun t => ae_of_all _ fun w => abs_nonneg _) hdom 2 (by norm_num)
  have hi : (∫⁻ w,ENNReal.ofReal |p ⟨T,hT,le_rfl⟩ w|^(2:ℝ) ∂P)=
      ∫⁻ w,ENNReal.ofReal |V w|^(2:ℝ) ∂P := by
    apply lintegral_congr_ae
    exact hterm.mono fun w hw => by dsimp only at hw ⊢;rw [hw]
  simpa only [hi,show ENNReal.ofReal ((2:ℝ)/(2-1))=2 by norm_num] using hh

end Asakura.Chapter10
