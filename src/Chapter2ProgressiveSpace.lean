import FullAuditProgressive
import FullAuditLpComplete
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- The sigma algebra of progressively measurable subsets of sample-time
space: every restriction to times <= t is F_t times Borel measurable. -/
def progressiveSpace {Ω ι : Type*} [Preorder ι] [MeasurableSpace ι]
    (F : ι → MeasurableSpace Ω) : MeasurableSpace (Ω × ι) :=
  ⨅ t, MeasurableSpace.map (fun p : Ω × Iic t => (p.1,p.2.val))
    ((F t).prod inferInstance)

theorem measurable_progressive_iff {Ω ι E : Type*} [Preorder ι] [MeasurableSpace ι]
    [MeasurableSpace E] (F : ι → MeasurableSpace Ω) (H : Ω × ι → E) :
    @Measurable _ _ (progressiveSpace F) inferInstance H ↔
      ∀ t, @Measurable _ _ ((F t).prod inferInstance) inferInstance
        (fun p : Ω × Iic t => H (p.1,p.2.val)) := by
  constructor
  · intro h t S hS
    exact MeasurableSpace.measurableSet_iInf.1 (h hS) t
  · intro h S hS
    exact MeasurableSpace.measurableSet_iInf.2 (fun t => h t hS)

theorem progressive_space_le_product {Ω ι : Type*} {m : MeasurableSpace Ω}
    [Preorder ι] [OrderTop ι] [MeasurableSpace ι]
    (F : ι → MeasurableSpace Ω) (hle : ∀ t, F t ≤ m) :
    progressiveSpace F ≤ m.prod inferInstance := by
  intro S hS
  have hp := MeasurableSpace.measurableSet_iInf.1 hS ⊤
  have hf : @Measurable (Ω × ι) Ω (m.prod inferInstance) (F ⊤) Prod.fst :=
    measurable_fst.mono le_rfl (hle ⊤)
  have ht : Measurable (fun p : Ω × ι => (⟨p.2,le_top⟩ : Iic (⊤ : ι))) :=
    measurable_snd.subtype_mk
  exact (hf.prodMk ht) hp

/-- The Hilbert space used in the density proof is the actual L2 space of
the progressive sigma algebra and the restricted finite measure. Completeness
uses the manuscript's previously checked Lp proof. -/
theorem progressive_L2_complete {Ω ι : Type*} {m : MeasurableSpace Ω}
    [Preorder ι] [OrderTop ι] [MeasurableSpace ι]
    (F : ι → MeasurableSpace Ω) (hle : ∀ t, F t ≤ m)
    (μ : @Measure (Ω × ι) (m.prod inferInstance)) :
    letI : MeasurableSpace (Ω × ι) := progressiveSpace F
    CompleteSpace (Lp ℝ 2 (μ.trim (progressive_space_le_product F hle))) := by
  exact current_lp_complete

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.measurable_progressive_iff
#print axioms Asakura.Chapter2Complete.progressive_space_le_product
#print axioms Asakura.Chapter2Complete.progressive_L2_complete
