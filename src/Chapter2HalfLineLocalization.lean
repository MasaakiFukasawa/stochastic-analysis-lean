import Chapter2M2Localization
import Chapter2BrownianSquare

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

instance half_time_nonnegative : Fact ((0:EReal) ≤ ⊤) := ⟨le_top⟩

abbrev HalfClosedTime := ClosedTime (⊤ : EReal)

noncomputable def halfTimeReal (t : HalfClosedTime) : ℝ≥0 :=
  ⟨t.val.toReal,EReal.toReal_nonneg t.property.1⟩

theorem half_time_real_mono {s t : HalfClosedTime} (hst : s ≤ t) (ht : t < ⊤) :
    halfTimeReal s ≤ halfTimeReal t := by
  exact EReal.toReal_le_toReal hst (ne_of_gt ((EReal.bot_lt_coe 0).trans_le s.property.1)) (ne_of_lt ht)

theorem half_time_real_stopped_continuous (v : HalfClosedTime) (hv : v < ⊤) :
    Continuous (fun t => halfTimeReal (min v t)) := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (EReal.tendsto_toReal (ne_of_lt ((min_le_left v t).trans_lt hv))
    (ne_of_gt ((EReal.bot_lt_coe 0).trans_le (min v t).property.1))).comp
      (continuous_subtype_val.comp (continuous_const.min continuous_id)).continuousAt

noncomputable def halfClosedFiltration {Ω : Type*} (m : MeasurableSpace Ω)
    (F : ℝ≥0 → MeasurableSpace Ω) (t : HalfClosedTime) : MeasurableSpace Ω :=
  if t < ⊤ then F (halfTimeReal t) else m

theorem half_closed_filtration_le {Ω : Type*} (m : MeasurableSpace Ω)
    (F : ℝ≥0 → MeasurableSpace Ω) (hle : ∀ t, F t ≤ m) (t : HalfClosedTime) :
    halfClosedFiltration m F t ≤ m := by
  by_cases ht : t < ⊤ <;> simp only [halfClosedFiltration,ht,ite_true,ite_false]
  · exact hle _
  · exact le_rfl

theorem half_closed_filtration_mono {Ω : Type*} (m : MeasurableSpace Ω)
    (F : ℝ≥0 → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m) :
    Monotone (halfClosedFiltration m F) := by
  intro s t hst
  by_cases ht : t < ⊤
  · have hs : s < ⊤ := hst.trans_lt ht
    simp only [halfClosedFiltration,if_pos ht,if_pos hs]
    exact hF (half_time_real_mono hst ht)
  · simpa only [halfClosedFiltration,if_neg ht] using half_closed_filtration_le m F hle s

/-- A deterministic finite stop of a half-line martingale has an actual
continuous M2 witness on the compactified time interval, including infinity. -/
theorem half_line_stopped_m2
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ≥0 → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ℝ≥0 → Ω → ℝ) (had : ∀ t, Measurable[F t] (X t))
    (hi : ∀ t, MemLp (X t) 2 P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hM : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) (hz : X 0 =ᵐ[P] 0)
    (v : HalfClosedTime) (hv : v < ⊤) :
    ContinuousM2Witness P (halfClosedFiltration m F) (fun t ω => X (halfTimeReal (min v t)) ω) := by
  let G := halfClosedFiltration m F
  have hG := half_closed_filtration_mono m F hF hle
  have had' t : Measurable[G t] (X (halfTimeReal (min v t))) := by
    have ht : min v t < ⊤ := (min_le_left _ _).trans_lt hv
    have hg : Measurable[G (min v t)] (X (halfTimeReal (min v t))) := by
      change @Measurable Ω ℝ (if min v t < ⊤ then F (halfTimeReal (min v t)) else m) _ _
      rw [if_pos ht]
      exact had (halfTimeReal (min v t))
    exact hg.mono (hG (min_le_right _ _)) le_rfl
  refine ⟨had',fun t => hi _,fun ω => (hc ω).comp (half_time_real_stopped_continuous v hv),?_,?_⟩
  · intro s t hst
    by_cases hvs : v ≤ s
    · have hvt := hvs.trans hst
      simp only [min_eq_left hvs,min_eq_left hvt]
      apply EventuallyEq.of_eq
      apply condExp_of_stronglyMeasurable (half_closed_filtration_le m F hle s)
      · simpa only [min_eq_left hvs] using (had' s).stronglyMeasurable
      · exact (hi _).integrable (by norm_num)
    · have hsv := le_of_not_ge hvs
      have hs : s < ⊤ := hsv.trans_lt hv
      have hsm : s ≤ min v t := le_min hsv hst
      have hr := half_time_real_mono hsm ((min_le_left _ _).trans_lt hv)
      simpa only [G,halfClosedFiltration,if_pos hs,min_eq_right hsv] using hM _ _ hr
  · have he : halfTimeReal (min v ⊥) = 0 := by
      apply Subtype.ext
      simp only [min_bot_right,halfTimeReal]
      rfl
    simpa only [he] using hz

/-- A continuous square-integrable martingale on every finite interval is a
local martingale on the entire half-line. No value or limit at infinity is used. -/
theorem half_line_martingale_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ≥0 → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ℝ≥0 → Ω → ℝ) (had : ∀ t, Measurable[F t] (X t))
    (hi : ∀ t, MemLp (X t) 2 P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hM : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) (hz : X 0 =ᵐ[P] 0) :
    LocalMProcessWitness P (halfClosedFiltration m F) (fun t ω => X (halfTimeReal t) ω) := by
  obtain ⟨u,hu,hut,huc⟩ := deterministic_time_exhaustion (show (0:EReal) < ⊤ by simp)
  apply m2_localization_implies_local P _ (half_closed_filtration_mono m F hF hle)
    (half_closed_filtration_le m F hle) _ (fun n _ => u n)
    (fun n t => by by_cases ht : u n ≤ t <;> simp [ht])
    (fun _ => hu) (fun n _ => hut n) (fun _ => huc)
  intro n
  exact half_line_stopped_m2 P F hF hle X had hi hc hM hz (u n) (hut n)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.half_line_martingale_local
