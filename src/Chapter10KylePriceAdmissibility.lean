import FullAuditMartingalePathNorm
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Rational prices on the closed interval form a closed L2 martingale.
Doob then gives the actual square-integrable path supremum required by the
admissible strategy definition. -/
theorem kyle_rational_price_admissible {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (p : ClosedTime T → Ω → ℝ) (V : Ω → ℝ)
    (hp : ∀ t,Measurable[F t] (p t))
    (hc : ∀ w,Continuous (fun s => p s w))
    (hV : MemLp V 2 P) (hrational : ∀ t,P[V|F t]=ᵐ[P] p t) :
    (∀ s t,s≤t → P[p t|F s]=ᵐ[P] p s) ∧ MemLp (continuousPath p hc) 2 P ∧
      MemLp (fun w => ‖continuousPath p hc w‖) 2 P := by
  have h2 t : MemLp (p t) 2 P := (memLp_congr_ae (hrational t)).mp (hV.condExp (m := F t) (by norm_num))
  have hmart s t (hst : s≤t) : P[p t|F s]=ᵐ[P] p s := by
    calc
      _ =ᵐ[P] P[P[V|F t]|F s] := condExp_congr_ae (hrational t).symm
      _ =ᵐ[P] P[V|F s] := condExp_condExp_of_le (hF hst) (hle t)
      _ =ᵐ[P] p s := hrational s
  have hpath := continuous_martingale_path_memLp P F hF hle p hp h2 hc hmart
  exact ⟨hmart,hpath,hpath.norm⟩

end Asakura.Chapter10
