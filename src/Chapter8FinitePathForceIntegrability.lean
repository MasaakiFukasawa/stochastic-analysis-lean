import Chapter8RandomPositionMoment
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

open MeasureTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Finite-path L2 integrability gives joint time-probability L2
integrability of the force, including the integrability used in Fubini. -/
theorem finite_path_force_integrability {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0≤T)
    (X : Ω → C(Icc (0:ℝ) T,E)) (hXm : Measurable X) (hX : MemLp X 2 P)
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g) :
    Measurable (fun z : Ω × ℝ => g (X z.1 (projIcc 0 T hT z.2))) ∧
      ∀ t∈Icc 0 T,MemLp (fun z : Ω × ℝ => g (X z.1 (projIcc 0 T hT z.2)))
        2 (P.prod (volume.restrict (Ioc 0 t))) := by
  have hm : Measurable (fun z : Ω × ℝ => X z.1 (projIcc 0 T hT z.2)) :=
    (measurable_uncurry_of_continuous_of_measurable (fun w => (X w).continuous.comp continuous_projIcc)
      (fun s => by
        change Measurable (fun w => X w (projIcc 0 T hT s))
        exact (continuous_eval_const (projIcc 0 T hT s)).measurable.comp hXm)).comp measurable_swap
  refine ⟨hg.continuous.measurable.comp hm,?_⟩
  intro t ht
  let μ := volume.restrict (Ioc 0 t)
  have hX2 : MemLp (fun z : Ω × ℝ => X z.1 (projIcc 0 T hT z.2)) 2 (P.prod μ) := by
    apply (hX.comp_fst μ).of_le hm.aestronglyMeasurable
    exact ae_of_all _ (fun z => (X z.1).norm_coe_le_norm _)
  have hdiff : LipschitzWith L (fun x => g x-g 0) := by
    simpa only [add_zero] using hg.sub (LipschitzWith.const (g 0))
  have hh := hdiff.comp_memLp (by simp) hX2
  have hconst : MemLp (fun _ : Ω × ℝ => g 0) 2 (P.prod μ) := memLp_const _
  have hsum : MemLp (fun z : Ω × ℝ => (g (X z.1 (projIcc 0 T hT z.2))-g 0)+g 0) 2 (P.prod μ) := hh.add hconst
  simpa only [sub_add_cancel] using hsum
end Asakura.Chapter8
