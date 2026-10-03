import FullAuditStoppedContinuous

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written

/-- The printed step-function proof of progressiveness, using the equivalent
 right dyadic grid and clipping at the right endpoint. The domain includes
 an infinite endpoint, where every approximation is exactly X_infinity. -/
theorem right_continuous_progressive_written {Ω : Type*} {T : EReal}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → ℝ) (hX : ∀ t, Measurable[F t] (X t))
    (hr : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (t : ClosedTime T) :
    @Measurable ((Iic t) × Ω) ℝ
      (MeasurableSpace.prod inferInstance (F t)) inferInstance
      (fun p => X p.1.val p.2) := by
  letI : MeasurableSpace Ω := F t
  let q : ℕ → ((Iic t) × Ω) → ClosedTime T :=
    fun n p => min (gridTime n p.1.val) t
  have hqm (n : ℕ) : Measurable (q n) :=
    ((grid_time_measurable T n).comp (measurable_subtype_coe.comp measurable_fst)).min measurable_const
  have hqc (n : ℕ) : (range (q n)).Countable := by
    apply (((gridTime_finite_range T n).image (fun s => min s t)).countable).mono
    rintro s ⟨p,rfl⟩
    exact ⟨gridTime n p.1.val,mem_range_self _,rfl⟩
  have hm (n : ℕ) : Measurable (fun p => X (q n p) p.2) := by
    apply measurable_countable_evaluation (q n) (hqm n) (hqc n) (fun s p => X s p.2)
    rintro s ⟨p,rfl⟩
    exact ((hX _).mono (hF (min_le_right _ _)) le_rfl).comp measurable_snd
  apply measurable_of_tendsto_metrizable hm
  apply tendsto_pi_nhds.mpr
  intro p
  apply (hr p.2 p.1.val).tendsto.comp
  have ht : Tendsto (fun n => q n p) atTop (𝓝 p.1.val) := by
    have h := (gridTime_tendsto p.1.val).min
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t))
    simpa only [min_eq_left (show p.1.val ≤ t from p.1.property)] using h
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht
  exact Eventually.of_forall fun n => le_min
    (extendedGrid_bounds p.1.val.property.1 p.1.val.property.2 n).1 p.1.property

end Asakura.FullAudit
