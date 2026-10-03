import Chapter2LevelLocalization
import Chapter2StieltjesRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 900000

/-- For a continuous increasing path, stopping at the first level k
is exactly capping the value at k. Empty hit sets at the terminal endpoint
are included. -/
theorem increasing_level_stop_eq_cap
    {ι : Type*} [CompleteLinearOrder ι] [DenselyOrdered ι]
    [TopologicalSpace ι] [OrderTopology ι]
    (f : ι → ℝ) (hf : Continuous f) (hmono : Monotone f)
    (k : ℝ) (h0 : f ⊥ ≤ k) (t : ι) :
    f (min (sInf {s | k ≤ f s}) t) = min k (f t) := by
  let τ := sInf {s | k ≤ f s}
  by_cases ht : t ≤ τ
  · have hb := continuous_level_stop_bound f hf k h0 t ht
    rw [min_eq_right ht,min_eq_right hb]
  · have hτt : τ < t := lt_of_not_ge ht
    have hτtop : τ < ⊤ := hτt.trans_le le_top
    obtain ⟨s,hs,hlevel⟩ := (closed_hitting_lower_event f hf (Ici k) isClosed_Ici τ hτtop).1
      (show sInf {s | f s ∈ Ici k} ≤ τ by exact le_rfl)
    have hτs : τ ≤ s := sInf_le hlevel
    have hsτ : s = τ := le_antisymm hs hτs
    have hge : k ≤ f τ := by simpa only [hsτ,mem_Ici] using hlevel
    have hle := continuous_level_stop_bound f hf k h0 τ le_rfl
    have he : f τ = k := le_antisymm hle hge
    rw [min_eq_left hτt.le,he,min_eq_left (hge.trans (hmono hτt.le))]

/-- For increasing adapted continuous processes the level localizers are
actual stopping times, and their stopped paths are measurably represented
by the explicit cap. -/
theorem increasing_process_level_localization
    {Ω ι : Type*} [CompleteLinearOrder ι] [DenselyOrdered ι]
    [TopologicalSpace ι] [OrderTopology ι] [CompactSpace ι] [SecondCountableTopology ι]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F)
    (A : ι → Ω → ℝ) (ha : ∀ t, Measurable[F t] (A t))
    (hc : ∀ ω, Continuous (fun t => A t ω)) (hm : ∀ ω, Monotone (fun t => A t ω))
    (k : ℝ) (hk : ∀ ω, A ⊥ ω ≤ k) :
    (∀ t, MeasurableSet[F t] {ω | sInf {s | k ≤ A s ω} ≤ t}) ∧
    (∀ t ω, A (min (sInf {s | k ≤ A s ω}) t) ω = min k (A t ω)) ∧
    (∀ t, Measurable[F t] (fun ω => A (min (sInf {s | k ≤ A s ω}) t) ω)) := by
  have he t ω := increasing_level_stop_eq_cap (fun t => A t ω) (hc ω) (hm ω) k (hk ω) t
  refine ⟨closed_hitting_stopping_compact F hF A ha hc (Ici k) isClosed_Ici,he,?_⟩
  intro t
  simp only [he]
  exact measurable_const.min (ha t)

/-- Adding a constant to the distribution function leaves its Stieltjes
measure unchanged; only values on the defining compact interval are needed. -/
theorem interval_stieltjes_measure_congr_add_const
    (a b : ℝ) (hab : a ≤ b) (A B : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b)) (hB : MonotoneOn B (Icc a b))
    (hrA : ∀ x ∈ Icc a b, ContinuousWithinAt A (Icc a b ∩ Ici x) x)
    (hrB : ∀ x ∈ Icc a b, ContinuousWithinAt B (Icc a b ∩ Ici x) x)
    (c : ℝ) (he : ∀ x ∈ Icc a b, B x = A x+c) :
    (intervalStieltjes a b hab B hB hrB).measure =
      (intervalStieltjes a b hab A hA hrA).measure := by
  letI := intervalStieltjes_finite a b hab A hA hrA
  letI := intervalStieltjes_finite a b hab B hB hrB
  apply Measure.ext_of_Iic
  intro r
  rw [StieltjesFunction.measure_Iic _
    (interval_stieltjes_left_limit a b hab (fun _ : Unit => B) (fun _ => hB) (fun _ => hrB) ()),
    StieltjesFunction.measure_Iic _
    (interval_stieltjes_left_limit a b hab (fun _ : Unit => A) (fun _ => hA) (fun _ => hrA) ())]
  congr 1
  change B (intervalClamp a b hab r)-B a = A (intervalClamp a b hab r)-A a
  rw [he _ (intervalClamp_mem a b hab r),he a (left_mem_Icc.2 hab)]
  ring

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.increasing_level_stop_eq_cap
#print axioms Asakura.Chapter2Complete.increasing_process_level_localization
#print axioms Asakura.Chapter2Complete.interval_stieltjes_measure_congr_add_const
