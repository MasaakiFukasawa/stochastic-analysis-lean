import FullAuditContinuousDoobStrong
import FullAuditDoobThresholdLimits

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written

/-- The complete continuous-time weak Doob estimate, with all three limit
 passages made explicit: c↓b, finite-grid maximum↑supremum, then b↑a. -/
theorem continuous_doob_weak_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} (hT : 0 ≤ T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : ∀ t, Measurable[F t] (X t))
    (hr : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (hY : Integrable (X ⟨T,hT,le_rfl⟩) P) (hpos : ∀ t, 0 ≤ᵐ[P] X t)
    (hdom : ∀ t, X t ≤ᵐ[P] P[X ⟨T,hT,le_rfl⟩ | F t]) (a : ℝ) (ha : 0 < a) :
    P.real {ω | ENNReal.ofReal a ≤ ⨆ t, ENNReal.ofReal (X t ω)} ≤
      a⁻¹ * ∫ ω in {ω | ENNReal.ofReal a ≤ ⨆ t, ENNReal.ofReal (X t ω)}, X ⟨T,hT,le_rfl⟩ ω ∂P := by
  let Y := X ⟨T,hT,le_rfl⟩
  let M := cumulativeMax hT X
  let Z := fun ω => ⨆ n, ENNReal.ofReal (M n ω)
  have hmY : Measurable[m] Y := (hX _).mono (hle _) le_rfl
  have hm (n : ℕ) : Measurable[m] (M n) :=
    cumulative_max_measurable hT X (fun t => (hX t).mono (hle t) le_rfl) n
  have hZ : Measurable[m] Z := Measurable.iSup fun n => (hm n).ennreal_ofReal
  have hw (n : ℕ) (b : ℝ) (hb : 0 < b) :
      b * P.real {ω | b < M n ω} ≤ ∫ ω, {ω | b < M n ω}.indicator Y ω ∂P := by
    apply weak_strict_from_closed P (M n) Y (hm n) hmY hY _ b hb
    intro c hc
    have h := cumulative_grid_weak P hT F hF hle X hX hY hpos hdom n c hc
    have hh := mul_le_mul_of_nonneg_left h hc.le
    rw [integral_indicator (measurableSet_le measurable_const (hm n))]
    simpa only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] using hh
  have hs := weak_strict_monotone_sup P M Y hm (cumulative_max_mono hT X) hmY hY hw
  have h := weak_closed_from_strict_ennreal P Z Y hZ hmY hY hs a ha
  rw [integral_indicator (measurableSet_le measurable_const hZ)] at h
  have hdiv := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ha.le)
  simp only [← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul] at hdiv
  have he : Z = fun ω => ⨆ t, ENNReal.ofReal (X t ω) := funext (cumulative_max_supremum hT X hr)
  simpa only [he] using hdiv

/-- Measurability of the supremum is part of the argument, not a hypothesis. -/
theorem continuous_sup_measurable_written {Ω : Type*} {m : MeasurableSpace Ω}
    {T : EReal} (hT : 0 ≤ T) (X : ClosedTime T → Ω → ℝ)
    (hX : ∀ t, Measurable[m] (X t))
    (hr : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t) :
    Measurable[m] (fun ω => ⨆ t, ENNReal.ofReal (X t ω)) := by
  have h := Measurable.iSup fun n => (cumulative_max_measurable hT X hX n).ennreal_ofReal
  simpa only [cumulative_max_supremum hT X hr] using h

end Asakura.FullAudit
