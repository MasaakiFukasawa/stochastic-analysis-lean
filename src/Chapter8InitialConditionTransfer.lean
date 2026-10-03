import Chapter8IntegratedCoupling

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- The deterministic-initial-condition step for quadratically growing
information entries. Stationarity and synchronous contraction supply the
uniform moment bounds; no fourth moment is required. -/
theorem initial_condition_time_average_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Measure E) [IsProbabilityMeasure π]
    (hπ : MemLp (fun x : E => x) 2 π)
    (X Y : Ω → ℝ → E) (hmX : Measurable (Function.uncurry X))
    (hmY : Measurable (Function.uncurry Y))
    (hlaw : ∀ t,P.map (fun w => Y w t)=π)
    (x : E) (κ : ℝ) (hκ : 0<κ)
    (hXY : ∀ t≥0,∀ᵐ w ∂P,‖X w t-Y w t‖ ≤ Real.exp (-κ*t)*‖x-Y w 0‖)
    (f : E → ℝ) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hLip : ∀ z z',|f z-f z'| ≤ C*‖z-z'‖*(1+‖z‖+‖z'‖)) :
    ∃ D : ℝ,0 ≤ D ∧ ∀ T>0,
      Integrable (fun w => timeAverage (fun t => f (X w t)-f (Y w t)) T) P ∧
      (∫ w,|timeAverage (fun t => f (X w t)-f (Y w t)) T| ∂P) ≤ D/(κ*T) := by
  have hmXt t : Measurable (fun w => X w t) := hmX.comp (measurable_id.prodMk measurable_const)
  have hmYt t : Measurable (fun w => Y w t) := hmY.comp (measurable_id.prodMk measurable_const)
  have hY t : MemLp (fun w => Y w t) 2 P := by
    have hh : MemLp (fun z : E => z) 2 (P.map (fun w => Y w t)) := by rwa [hlaw]
    simpa only [Function.comp_def] using hh.comp_of_map (hmYt t).aemeasurable
  let A := fun w => ‖x-Y w 0‖
  have hA : MemLp A 2 P := ((memLp_const x).sub (hY 0)).norm
  let D := C*(1+3*(∫ w,(A w)^2 ∂P)+2*(∫ z,‖z‖^2 ∂π))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hsecond t : (∫ w,‖Y w t‖^2 ∂P)=(∫ z,‖z‖^2 ∂π) := by
    rw [← integral_map (hmYt t).aemeasurable (by fun_prop : AEStronglyMeasurable (fun z : E => ‖z‖^2) (P.map (fun w => Y w t))),hlaw]
  have he t (ht : 0 ≤ t) := weighted_coupling_expectation P (fun w => X w t) (fun w => Y w t)
    A (hmXt t) (hmYt t) (hY t) hA (fun w => norm_nonneg _)
    (Real.exp (-κ*t)) C (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by nlinarith)) hC (hXY t ht)
    f hf hLip
  have hb t (ht : 0 ≤ t) : (∫ w,|f (X w t)-f (Y w t)| ∂P) ≤ D*Real.exp (-κ*t) := by
    have hh := (he t ht).2
    rw [hsecond] at hh
    convert hh using 1 <;> dsimp [D] <;> ring
  refine ⟨D,hD,?_⟩
  intro T hT
  exact integrated_coupling_L1 P (fun w t => f (X w t)-f (Y w t))
    ((hf.measurable.comp hmX).sub (hf.measurable.comp hmY)) (fun t ht => (he t ht).1)
    D κ T hD hκ hT hb

end Asakura.Chapter8
