import FullAuditTransportFlow
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

open MeasureTheory
namespace Asakura.Chapter8
open Asakura.FullAudit

/-- A common-noise Lipschitz flow preserves finite second moments; only the
solution started at zero needs a separate moment estimate. -/
theorem flow_second_moment {E Ω : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    (μ : Measure E) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (X : E → Ω → E) (hX : Measurable (Function.uncurry X))
    (hμ : MemLp (fun x : E => x) 2 μ) (h₀ : MemLp (X 0) 2 P)
    (a : ℝ) (hLip : ∀ x,∀ᵐ w ∂P,‖X x w-X 0 w‖≤a*‖x‖) :
    MemLp (fun x : E => x) 2 (flowLaw μ P X) := by
  have hb : ∀ᵐ z ∂μ.prod P,‖X z.1 z.2‖≤a*‖z.1‖+‖X 0 z.2‖ := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) (by fun_prop))).mpr
    apply ae_of_all
    intro x
    filter_upwards [hLip x] with w hw
    exact (norm_le_norm_sub_add (X x w) (X 0 w)).trans (add_le_add hw le_rfl)
  have hg : MemLp (fun z : E × Ω => a*‖z.1‖+‖X 0 z.2‖) 2 (μ.prod P) :=
    ((hμ.norm.comp_fst P).const_mul a).add (h₀.norm.comp_snd μ)
  have hi : MemLp (Function.uncurry X) 2 (μ.prod P) :=
    hg.mono' hX.aestronglyMeasurable hb
  exact (memLp_map_measure_iff (by fun_prop) hX.aemeasurable).mpr hi

end Asakura.Chapter8
