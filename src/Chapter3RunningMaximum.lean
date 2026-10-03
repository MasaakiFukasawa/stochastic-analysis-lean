import Chapter3RegularizedWeightRegularity
import Chapter2PathMaximum

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

noncomputable def prefixPath {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (b : ClosedTime T) (hb : b < ⊤) (ω : Ω) : C(ClosedTime T,ℝ) :=
  ⟨fun s => X (min b s) ω,continuous_iff_continuousAt.mpr (fun s =>
    (hc ω _ ((min_le_left b s).trans_lt hb)).comp
      (continuous_const.min continuous_id).continuousAt)⟩

noncomputable def runningMaximum {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (t : ClosedTime T) (ω : Ω) : ℝ :=
  if ht : t < ⊤ then ‖prefixPath X hc t ht ω‖ else 0

theorem runningMaximum_of_lt_top {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (t : ClosedTime T) (ht : t < ⊤) (ω : Ω) :
    runningMaximum X hc t ω = ‖prefixPath X hc t ht ω‖ := by
  simp only [runningMaximum,dif_pos ht]

theorem runningMaximum_nonneg {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t) (t : ClosedTime T) (ω : Ω) :
    0 ≤ runningMaximum X hc t ω := by
  unfold runningMaximum
  split <;> positivity

theorem runningMaximum_bounds {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (t : ClosedTime T) (ht : t < ⊤) (ω : Ω) :
    (∀ s, s ≤ t → |X s ω| ≤ runningMaximum X hc t ω) ∧
    (∀ L : ℝ, 0 ≤ L → (∀ s, s ≤ t → |X s ω| ≤ L) → runningMaximum X hc t ω ≤ L) := by
  rw [runningMaximum_of_lt_top X hc t ht ω]
  constructor
  · intro s hs
    simpa only [prefixPath,ContinuousMap.coe_mk,min_eq_right hs,Real.norm_eq_abs] using
      (prefixPath X hc t ht ω).norm_coe_le_norm s
  · intro L hL hbound
    apply (ContinuousMap.norm_le _ hL).mpr
    intro s
    simpa only [prefixPath,ContinuousMap.coe_mk,Real.norm_eq_abs] using hbound (min t s) (min_le_left t s)

theorem runningMaximum_monotone {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t) (ω : Ω) :
    MonotoneOn (fun t => runningMaximum X hc t ω) (Iio ⊤) := by
  intro s hs t ht hst
  exact (runningMaximum_bounds X hc s hs ω).2 _ (runningMaximum_nonneg X hc t ω)
    (fun u hus => (runningMaximum_bounds X hc t ht ω).1 u (hus.trans hst))

theorem runningMaximum_adapted {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (ha : ∀ t, t < ⊤ → Measurable[F t] (X t)) (t : ClosedTime T) (ht : t < ⊤) :
    Measurable[F t] (runningMaximum X hc t) := by
  letI : MeasurableSpace Ω := F t
  have hm : Measurable[F t] (fun ω => prefixPath X hc t ht ω) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro s
    exact (ha _ ((min_le_left t s).trans_lt ht)).mono (hF (min_le_left t s)) le_rfl
  have he : runningMaximum X hc t = (fun ω => ‖prefixPath X hc t ht ω‖) :=
    funext (runningMaximum_of_lt_top X hc t ht)
  rw [he]
  exact hm.norm

theorem runningMaximum_continuous {Ω : Type*} {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (X : ClosedTime T → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (ω : Ω) (t : ClosedTime T) (ht : t < ⊤) :
    ContinuousAt (fun s => runningMaximum X hc s ω) t := by
  obtain ⟨c,_,_,_,_,hct,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨k,hk⟩ := hcc t ht
  let b := realTimeClamp (T := T) (c k)
  let f := prefixPath X hc b (hct k) ω
  let g : ClosedTime T → C(ClosedTime T,ℝ) := fun u =>
    ⟨fun s => f (min u s), f.continuous.comp (continuous_const.min continuous_id)⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact f.continuous.comp (continuous_fst.min continuous_snd)
  have he : (fun u => ‖g u‖) =ᶠ[𝓝 t] (fun u => runningMaximum X hc u ω) := by
    filter_upwards [gt_mem_nhds hk] with u hu
    rw [runningMaximum_of_lt_top X hc u (hu.trans (hct k)) ω]
    congr 1
    ext s
    change X (min b (min u s)) ω = X (min u s) ω
    rw [min_eq_right ((min_le_left u s).trans hu.le)]
  exact hg.norm.continuousAt.congr_of_eventuallyEq he.symm

/-- The running maximum starts at zero under the original a.e. initial condition. -/
theorem runningMaximum_initial_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (X : ClosedTime T → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (h0 : ∀ᵐ ω ∂P, X ⊥ ω = 0) :
    ∀ᵐ ω ∂P, runningMaximum X hc ⊥ ω = 0 := by
  filter_upwards [h0] with ω hω
  apply le_antisymm _ (runningMaximum_nonneg X hc ⊥ ω)
  apply (runningMaximum_bounds X hc ⊥ hT ω).2 0 le_rfl
  intro s hs
  have he : s = ⊥ := le_antisymm hs bot_le
  simp only [he,hω,abs_zero,le_refl]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.runningMaximum_bounds
#print axioms Asakura.Chapter3Complete.runningMaximum_monotone
#print axioms Asakura.Chapter3Complete.runningMaximum_adapted
#print axioms Asakura.Chapter3Complete.runningMaximum_continuous

#print axioms Asakura.Chapter3Complete.runningMaximum_initial_zero
