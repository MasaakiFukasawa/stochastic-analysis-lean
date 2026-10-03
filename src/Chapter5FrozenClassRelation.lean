import Chapter5WeightedGeneratorEnergy
import Chapter5FrozenDifferenceApriori

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable def frozenBSDEClassRelation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (W : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ) (hco : ∀ r,∃ j,r≤c j)
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β) (ξ : Ω → ℝ)
    (f : (Ω × ℝ) × (ℝ × ℝ) → ℝ) :
    WithLp 2 ((progressiveEnergyRange F (fun _ => R) (exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β)) ×
      (progressiveEnergyRange F (fun _ => R) (exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β))) →
    WithLp 2 ((progressiveEnergyRange F (fun _ => R) (exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β)) ×
      (progressiveEnergyRange F (fun _ => R) (exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β))) → Prop :=
  fun x y => ∃ i j : FiniteProgressiveProcess P F R,
    i.realize P F R β hR hβ=x.fst ∧ j.realize P F R β hR hβ=x.snd ∧
    ∃ u : BSDEFiniteEnergyData P F W c R,
    ∃ hp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => u.Y (realTimeClamp z.2.val) z.1),
    (u.Y (realTimeClamp R) =ᵐ[P] ξ) ∧
    (∀ w r,r∈Icc 0 R → u.B (w,r)= -f ((w,r),i.value (w,r),j.value (w,r))) ∧
    (u.outputY P F W c R hp).realize P F R β hR hβ=y.fst ∧
    (u.outputZ P F W c hco R).realize P F R β hR hβ=y.snd

end Asakura.Chapter5
