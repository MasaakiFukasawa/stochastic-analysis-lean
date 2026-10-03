import Chapter12ConditionalTimeContraction
import Chapter12ConditionalProgressive

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem deterministic_time_progressive {Ω S : Type*} [Preorder S] [MeasurableSpace S]
    (F : S → MeasurableSpace Ω) (h : S → ℝ) (hh : Measurable h) :
    @Measurable _ _ (progressiveSpace F) inferInstance (fun z : Ω × S => h z.2) := by
  apply (measurable_progressive_iff _ _).mpr
  intro t
  exact hh.comp (measurable_subtype_coe.comp measurable_snd)

/-- Conditional expectation of a separated cylinder-gradient term. The
conditional process is progressive and has the required integrated L2 bound. -/
theorem conditional_tensor_L2 {Ω S : Type*} [m : MeasurableSpace Ω]
    [Preorder S] [OrderTop S] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure S) [SigmaFinite ν]
    (F : S → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (U : Ω → ℝ) (hUm : Measurable U) (hU : MemLp U 2 P)
    (h : S → ℝ) (hhm : Measurable h) (hh : MemLp h 2 ν)
    (C : Ω × S → ℝ) (hC : @Measurable _ _ (progressiveSpace F) inferInstance C)
    (he : ∀ t,(fun w => C (w,t)) =ᵐ[P] P[U|F t]) :
    @Measurable _ _ (progressiveSpace F) inferInstance (fun z : Ω × S => h z.2*C z) ∧
    MemLp (fun z : Ω × S => h z.2*C z) 2 (P.prod ν) ∧
    (∀ t,(fun w => h t*C (w,t)) =ᵐ[P] P[(fun w => h t*U w)|F t]) ∧
    (∫ z,(h z.2*C z)^2 ∂P.prod ν) ≤ ∫ z : Ω × S,(h z.2*U z.1)^2 ∂P.prod ν := by
  have hup : MemLp (fun z : Ω × S => h z.2*U z.1) 2 (P.prod ν) := by
    apply (memLp_two_iff_integrable_sq ((hhm.comp measurable_snd).mul
      (hUm.comp measurable_fst)).aestronglyMeasurable).mpr
    convert hU.integrable_sq.mul_prod hh.integrable_sq using 1
    funext z
    change (h z.2*U z.1)^2=U z.1^2*h z.2^2
    ring
  have hqp := (deterministic_time_progressive F h hhm).mul hC
  have hqm := hqp.mono (progressive_space_le_product F hle) le_rfl
  have hcond t : (fun w => h t*C (w,t)) =ᵐ[P] P[(fun w => h t*U w)|F t] := by
    have hs := condExp_smul (h t) U (F t) (μ := P)
    change P[(fun w => h t*U w)|F t] =ᵐ[P] (fun w => h t*P[U|F t] w) at hs
    filter_upwards [he t,hs] with w hw hsw
    rw [hw]
    exact hsw.symm
  have hb := conditional_time_L2_contraction P ν F hle _ _
    ((hhm.comp measurable_snd).mul (hUm.comp measurable_fst)) hqm hup (ae_of_all ν hcond)
  exact ⟨hqp,hb.1,hcond,hb.2⟩

end Asakura.Chapter12
