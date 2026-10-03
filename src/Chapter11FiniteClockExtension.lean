import Chapter11RealMixedStepDensity

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem finite_clock_extension {Ω : Type*} [MeasurableSpace Ω]
    (b : ℝ) (hb : 0≤b) (A : Ω → ℝ → ℝ)
    (hA : ∀ w,MonotoneOn (A w) (Icc 0 b))
    (hAc : ∀ w,ContinuousOn (A w) (Icc 0 b))
    (hm : ∀ r,r∈Icc 0 b → Measurable (fun w => A w r)) :
    let C := fun w r => A w (intervalClamp 0 b hb r)
    ∃ hC : ∀ w,MonotoneOn (C w) (Icc 0 b),
    ∃ hCc : ∀ w,ContinuousOn (C w) (Icc 0 b),
      (∀ r,Measurable (fun w => C w r)) ∧
      (∀ w r,r∈Icc 0 b → C w r=A w r) ∧
      ∀ w,(intervalStieltjes 0 b hb (C w) (hC w) (fun r hr => (hCc w r hr).mono inter_subset_left)).measure=
        (intervalStieltjes 0 b hb (A w) (hA w) (fun r hr => (hAc w r hr).mono inter_subset_left)).measure := by
  intro C
  have hC w : MonotoneOn (C w) (Icc 0 b) := fun r _ s _ hrs =>
    hA w (intervalClamp_mem 0 b hb r) (intervalClamp_mem 0 b hb s) (intervalClamp_mono 0 b hb hrs)
  have hCc w : ContinuousOn (C w) (Icc 0 b) :=
    ((hAc w).comp_continuous (intervalClamp_continuous 0 b hb) (intervalClamp_mem 0 b hb)).continuousOn
  have he w r (hr : r∈Icc 0 b) : C w r=A w r := by dsimp only [C];rw [intervalClamp_eq 0 b hb hr]
  refine ⟨hC,hCc,(fun r => hm _ (intervalClamp_mem 0 b hb r)),he,?_⟩
  intro w
  apply interval_stieltjes_measure_congr_add_const 0 b hb (A w) (C w) (hA w) (hC w)
    (fun r hr => (hAc w r hr).mono inter_subset_left) (fun r hr => (hCc w r hr).mono inter_subset_left) 0
  intro r hr
  simpa only [add_zero] using he w r hr

theorem random_stieltjes_integral_measurable_on {Ω : Type*} [MeasurableSpace Ω]
    (b : ℝ) (hb : 0≤b) (A : Ω → ℝ → ℝ)
    (hA : ∀ w,MonotoneOn (A w) (Icc 0 b))
    (hAc : ∀ w,ContinuousOn (A w) (Icc 0 b))
    (hm : ∀ r,r∈Icc 0 b → Measurable (fun w => A w r))
    (f : Ω × ℝ → ℝ) (hf : Measurable f) :
    Measurable (fun w => ∫ r,f (w,r) ∂(intervalStieltjes 0 b hb (A w) (hA w)
      (fun r hr => (hAc w r hr).mono inter_subset_left)).measure) := by
  obtain ⟨hC,hCc,hCm,_,he⟩ := finite_clock_extension b hb A hA hAc hm
  have hh := random_stieltjes_integral_measurable 0 b hb _ hC hCc hCm f hf
  simpa only [he] using hh

end Asakura.Chapter11
