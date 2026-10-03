import FullAuditFiniteRangeStopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written

/-- A countably valued measurable selector evaluates a measurable family by
 a countable union of its fibers. -/
theorem measurable_countable_evaluation {α ι : Type*} [MeasurableSpace α]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (q : α → ι) (hq : Measurable q) (hc : (range q).Countable)
    (Y : ι → α → ℝ) (hY : ∀ i ∈ range q, Measurable (Y i)) :
    Measurable (fun x => Y (q x) x) := by
  intro B hB
  have he : (fun x => Y (q x) x) ⁻¹' B = ⋃ i ∈ range q, q ⁻¹' {i} ∩ Y i ⁻¹' B := by
    ext x
    simp only [mem_preimage,mem_iUnion,mem_inter_iff,mem_singleton_iff]
    constructor
    · intro h; exact ⟨q x,mem_range_self x,rfl,h⟩
    · rintro ⟨i,hi,hq,hY⟩; simpa [hq] using hY
  rw [he]
  exact MeasurableSet.biUnion hc fun i hi => (hq (measurableSet_singleton i)).inter (hY i hi hB)

theorem extended_grid_measurable (T : EReal) (n : ℕ) : Measurable (extendedGrid T n) := by
  unfold extendedGrid upperDyadic
  apply Measurable.ite (measurableSet_le measurable_id measurable_const)
  · apply Measurable.min _ measurable_const
    exact measurable_coe_real_ereal.comp
      (((measurable_of_countable (fun k : ℤ => (k : ℝ))).comp
        ((measurable_const.mul measurable_ereal_toReal).ceil)).div_const _)
  · exact measurable_const

theorem grid_time_measurable (T : EReal) (n : ℕ) : Measurable (gridTime (T := T) n) := by
  exact ((extended_grid_measurable T n).comp measurable_subtype_coe).subtype_mk

/-- Measurability of τ∧t at deterministic time t is established from lower rays. -/
theorem stopped_min_measurable {Ω : Type*} {T : EReal}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (t : ClosedTime T) : Measurable[F t] (fun ω => min (τ ω) t) := by
  letI : MeasurableSpace Ω := F t
  apply measurable_of_Iic
  intro r
  by_cases htr : t ≤ r
  · have he : (fun ω => min (τ ω) t) ⁻¹' Iic r = univ := by
      ext ω; simp only [mem_preimage,mem_Iic,mem_univ,iff_true]
      exact (min_le_right _ _).trans htr
    rw [he]; exact MeasurableSet.univ
  · have hrt := le_of_not_ge htr
    have he : (fun ω => min (τ ω) t) ⁻¹' Iic r = {ω | τ ω ≤ r} := by
      ext ω; simp [min_le_iff,htr]
    rw [he]
    exact hF hrt _ (hτ r)

/-- The right grid approximation, clipped at t, is F_t-measurable and converges
 to the stopped process. This is the finite-step calculation behind progressiveness. -/
theorem stopped_min_value_measurable {Ω : Type*} {T : EReal}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (X : ClosedTime T → Ω → ℝ) (hX : ∀ t, Measurable[F t] (X t))
    (hr : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (t : ClosedTime T) : Measurable[F t] (fun ω => X (min (τ ω) t) ω) := by
  letI : MeasurableSpace Ω := F t
  let q : ℕ → Ω → ClosedTime T := fun n ω => min (gridTime n (min (τ ω) t)) t
  have hqm (n : ℕ) : Measurable (q n) :=
    ((grid_time_measurable T n).comp (stopped_min_measurable F hF τ hτ t)).min measurable_const
  have hqc (n : ℕ) : (range (q n)).Countable := by
    apply (((gridTime_finite_range T n).image (fun s => min s t)).countable).mono
    rintro s ⟨ω,rfl⟩
    exact ⟨gridTime n (min (τ ω) t),mem_range_self _,rfl⟩
  have hYn (n : ℕ) : Measurable (fun ω => X (q n ω) ω) := by
    apply measurable_countable_evaluation (q n) (hqm n) (hqc n) X
    rintro s ⟨ω,rfl⟩
    exact (hX _).mono (hF (min_le_right _ _)) le_rfl
  apply measurable_of_tendsto_metrizable hYn
  apply tendsto_pi_nhds.mpr
  intro ω
  apply (hr ω (min (τ ω) t)).tendsto.comp
  have ht : Tendsto (fun n => q n ω) atTop (𝓝 (min (τ ω) t)) := by
    have ht := (gridTime_tendsto (min (τ ω) t)).min
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t))
    simpa only [min_eq_left (min_le_right (τ ω) t)] using ht
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht
  exact Eventually.of_forall fun n => le_min
    (extendedGrid_bounds (min (τ ω) t).property.1 (min (τ ω) t).property.2 n).1
    (min_le_right _ _)

/-- Adapted right-continuous processes evaluated at a stopping time are
 measurable for exactly the stopped sigma algebra used in the manuscript. -/
theorem stopped_value_measurable_right_continuous {Ω : Type*} (m : MeasurableSpace Ω)
    {T : EReal} (hT : 0 ≤ T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (X : ClosedTime T → Ω → ℝ) (hX : ∀ t, Measurable[F t] (X t))
    (hr : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t) :
    Measurable[writtenStoppedSpace m F τ hτ] (fun ω => X (τ ω) ω) := by
  have hm : Measurable[m] (fun ω => X (τ ω) ω) := by
    have h := (stopped_min_value_measurable F hF τ hτ X hX hr ⟨T,hT,le_rfl⟩).mono
      (hle ⟨T,hT,le_rfl⟩) le_rfl
    have he (ω : Ω) : min (τ ω) (⟨T,hT,le_rfl⟩ : ClosedTime T) = τ ω := min_eq_left (τ ω).property.2
    simpa only [he] using h
  intro B hB
  refine ⟨hm hB,fun t => ?_⟩
  have he : (fun ω => X (τ ω) ω) ⁻¹' B ∩ {ω | τ ω ≤ t} =
      (fun ω => X (min (τ ω) t) ω) ⁻¹' B ∩ {ω | τ ω ≤ t} := by
    ext ω
    simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq]
    constructor <;> rintro ⟨hb,ht⟩ <;> simpa only [min_eq_left ht] using And.intro hb ht
  rw [he]
  exact ((stopped_min_value_measurable F hF τ hτ X hX hr t) hB).inter (hτ t)

end Asakura.FullAudit
