import FullAuditContinuousDoob
import FullAuditClosedHitting
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.ContinuousMap.Compact

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written

noncomputable def continuousPath {Ω : Type*} {T : EReal}
    (X : ClosedTime T → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => X t ω))
    (ω : Ω) : C(ClosedTime T,ℝ) := ⟨fun t => X t ω,hc ω⟩

theorem continuous_path_measurable {Ω : Type*} {m : MeasurableSpace Ω} {T : EReal}
    (X : ClosedTime T → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hm : ∀ t, Measurable[m] (X t)) : Measurable[m] (continuousPath X hc) := by
  exact ContinuousMap.measurable_iff_eval.mpr hm

/-- The precise Doob estimate used by the completeness proof, now as the L2
 norm of a random continuous path. This is only a representation of the
 supremum norm; the stochastic inequality is the previously checked proof. -/
theorem continuous_martingale_path_norm {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (h2 : ∀ t, MemLp (X t) 2 P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) :
    eLpNorm (continuousPath X hc) 2 P ≤ 2 * eLpNorm (X ⊤) 2 P := by
  have hT : 0 ≤ T := Fact.out
  have habs (t : ClosedTime T) : Measurable[F t] (fun ω => |X t ω|) := by
    letI : MeasurableSpace Ω := F t
    simpa only [Real.norm_eq_abs] using (hm t).norm
  have hi := (h2 ⊤).integrable (by norm_num)
  have hd (t : ClosedTime T) : (fun ω => |X t ω|) ≤ᵐ[P] P[(fun ω => |X ⊤ ω|) | F t] := by
    have hj := conditional_jensen_written (hle t) abs_convex_written hi hi.abs
    filter_upwards [hj,hmart t ⊤ le_top] with ω hj he
    simpa only [Function.comp_def,he] using hj
  have h := continuous_doob_strong_written P hT F hF hle (fun t ω => |X t ω|) habs
    (fun ω t => (hc ω).abs.continuousAt.continuousWithinAt) hi.abs
    (fun t => Eventually.of_forall fun ω => abs_nonneg _) hd 2 (by norm_num)
  have hmPath := continuous_path_measurable X hc (fun t => (hm t).mono (hle t) le_rfl)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmPath.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (h2 ⊤).aestronglyMeasurable]
  have hen (ω : Ω) : ‖continuousPath X hc ω‖ₑ = ⨆ t, ENNReal.ofReal |X t ω| := by
    rw [ContinuousMap.enorm_eq_iSup_enorm]
    simp only [continuousPath,ContinuousMap.coe_mk,← ofReal_norm,Real.norm_eq_abs]
  simp only [hen]
  norm_num only [ENNReal.toReal_ofNat,show (2 : ℝ)/(2-1)=2 by norm_num,ENNReal.ofReal_ofNat] at h ⊢
  have ht : (⟨T,hT,le_rfl⟩ : ClosedTime T) = ⊤ := by apply Subtype.ext; rfl
  simpa only [ht,← ofReal_norm,Real.norm_eq_abs] using h

/-- L2 membership of the path variable follows from its terminal value. -/
theorem continuous_martingale_path_memLp {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (h2 : ∀ t, MemLp (X t) 2 P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) :
    MemLp (continuousPath X hc) 2 P := by
  exact (continuous_martingale_path_norm P F hF hle X hm h2 hc hmart).trans_lt
    (ENNReal.mul_lt_top (by norm_num) (h2 ⊤).eLpNorm_lt_top)

end Asakura.FullAudit
