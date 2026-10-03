import Chapter2ContinuousLocalizers
import Chapter2ContinuousEnvelope
import Chapter2CommonStopLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- A continuous path on [0,T), with an unused zero value at T. -/
noncomputable def extendOpenPath {T : EReal} [Fact (0 ≤ T)]
    (f : C(Iio (⊤ : ClosedTime T),ℝ)) (t : ClosedTime T) : ℝ :=
  if ht : t < ⊤ then f ⟨t,ht⟩ else 0

theorem extendOpenPath_continuousAt {T : EReal} [Fact (0 ≤ T)]
    (f : C(Iio (⊤ : ClosedTime T),ℝ)) (t : ClosedTime T) (ht : t < ⊤) :
    ContinuousAt (extendOpenPath f) t := by
  have h : ContinuousOn (extendOpenPath f) (Iio ⊤) := by
    rw [continuousOn_iff_continuous_restrict]
    convert f.continuous using 1
    funext s
    change (if ht : s.val < ⊤ then f ⟨s.val,ht⟩ else 0) = f s
    split_ifs with hs
    · rfl
    · exact (hs s.property).elim
  exact h.continuousAt (isOpen_Iio.mem_nhds ht)

/-- The locally uniform limit of local martingales is a local martingale.
Here convergence is pathwise in the compact-open topology after the common
null-set removal in the manuscript. The common bounded localizers are
constructed from the continuous absolute envelope, not assumed. -/
theorem pathwise_locally_uniform_limit_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (Y : Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (hX : ∀ n, LocalMProcessWitness P F (fun t ω => extendOpenPath (X n ω) t))
    (hconv : ∀ ω, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    LocalMProcessWitness P F (fun t ω => extendOpenPath (Y ω) t) := by
  classical
  letI : LocallyCompactSpace (Iio (⊤ : ClosedTime T)) := isOpen_Iio.locallyCompactSpace
  let U (ω) : C(Iio (⊤ : ClosedTime T),ℝ) :=
    ⟨fun t => ⨆ n, |X n ω t|,continuous_absolute_envelope (fun n => X n ω) (Y ω) (hconv ω)⟩
  have hUm (t) : Measurable[F t] (fun ω => extendOpenPath (U ω) t) := by
    letI : MeasurableSpace Ω := F t
    by_cases ht : t < ⊤
    · change Measurable (fun ω => if h : t < ⊤ then U ω ⟨t,h⟩ else 0)
      simp only [dite_eq_left ht,U,ContinuousMap.coe_mk]
      apply Measurable.iSup
      intro n
      have h := ((hX n).adapted P F t ht).norm
      simpa only [extendOpenPath,dite_eq_left ht,Real.norm_eq_abs] using h
    · simp only [extendOpenPath,dite_eq_right ht]
      exact measurable_const
  have ht0 : (⊥ : ClosedTime T) < ⊤ := hT
  have hzero (n) : (fun ω => extendOpenPath (X n ω) ⊥) =ᵐ[P] 0 := by
    obtain ⟨τ,_,_,_,_,hτ⟩ := (hX n).localizers
    simpa only [min_bot_right] using (hτ 0).1.initial
  have hUzero : (fun ω => extendOpenPath (U ω) ⊥) =ᵐ[P] 0 := by
    filter_upwards [ae_all_iff.2 hzero] with ω hω
    have hz : ∀ n, X n ω ⟨⊥,ht0⟩ = 0 := by
      intro n
      simpa only [extendOpenPath,dite_eq_left ht0,Pi.zero_apply] using hω n
    simp only [extendOpenPath,dite_eq_left ht0,U,ContinuousMap.coe_mk,hz,abs_zero,ciSup_const,Pi.zero_apply]
  obtain ⟨σ,hs,hsm,hst,hsc,hbound⟩ := halfopen_continuous_bounded_localizers P hT F hF
    (fun t ω => extendOpenPath (U ω) t) hUm
    (fun ω t ht => extendOpenPath_continuousAt (U ω) t ht) hUzero
  have hleU (n ω) (t : Iio (⊤ : ClosedTime T)) : |X n ω t| ≤ U ω t := by
    have hev : Continuous (fun f : C(Iio (⊤ : ClosedTime T),ℝ) => |f t|) :=
      (continuous_id.eval continuous_const).abs
    have hb : BddAbove (range (fun k => |X k ω t|)) := by
      apply ((hconv ω).isCompact_insert_range.image hev).bddAbove.mono
      rintro y ⟨k,rfl⟩
      exact ⟨X k ω,mem_insert_of_mem _ (mem_range_self k),rfl⟩
    exact le_ciSup hb n
  refine local_limit_of_common_bounded_stops P F hF hle
    (fun n t ω => extendOpenPath (X n ω) t) hX
    (fun t ω => extendOpenPath (Y ω) t)
    (fun ω t ht => extendOpenPath_continuousAt (Y ω) t ht) ?_ σ hs hsm hst hsc (fun k => (k:ℝ)) ?_
  · intro ω t ht
    have h := (continuous_eval_const (⟨t,ht⟩ : Iio (⊤ : ClosedTime T))).tendsto (Y ω) |>.comp (hconv ω)
    simpa only [extendOpenPath,dite_eq_left ht,Function.comp_def] using h
  · intro k n
    filter_upwards [hbound k] with ω hω
    intro t
    have ht : min (σ k ω) t < ⊤ := (min_le_left _ _).trans_lt (hst k ω)
    have hu := (hleU n ω ⟨_,ht⟩).trans (le_abs_self (U ω ⟨_,ht⟩))
    have hb := hω t
    simp only [extendOpenPath,dite_eq_left ht,Real.norm_eq_abs] at hb ⊢
    exact hu.trans hb

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.extendOpenPath_continuousAt
#print axioms Asakura.Chapter2Complete.pathwise_locally_uniform_limit_local
