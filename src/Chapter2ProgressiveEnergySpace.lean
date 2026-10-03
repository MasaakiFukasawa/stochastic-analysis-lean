import Chapter2ProgressiveSpace
import FullAuditBoundedKW

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Actual progressively measurable finite-energy integrands, before
identifying functions equal for the sample-time Stieltjes measure. -/
noncomputable def progressiveEnergyIntegrands
    {Ω : Type*} [MeasurableSpace Ω] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (c : ℕ → ℝ)
    (ν : Measure (Ω × ℝ)) : Submodule ℝ (Ω × ℝ → ℝ) where
  carrier := {H | Measurable H ∧
    (∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val))) ∧ MemLp H 2 ν}
  zero_mem' := ⟨measurable_const,fun _ => measurable_const,MemLp.zero⟩
  add_mem' := by
    rintro H G ⟨hm,hp,hi⟩ ⟨gm,gp,gi⟩
    exact ⟨hm.add gm,fun n => (hp n).add (gp n),hi.add gi⟩
  smul_mem' := by
    rintro a H ⟨hm,hp,hi⟩
    exact ⟨hm.const_smul a,fun n => (hp n).const_smul a,hi.const_smul a⟩

/-- The quotient map is the actual L2 realization for the Stieltjes measure. -/
noncomputable def progressiveEnergyToLp
    {Ω : Type*} [MeasurableSpace Ω] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (c : ℕ → ℝ)
    (ν : Measure (Ω × ℝ)) : progressiveEnergyIntegrands F c ν →ₗ[ℝ] Lp ℝ 2 ν where
  toFun H := H.property.2.2.toLp H.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The normed domain is the subspace of L2 classes which admit a progressive
representative, not the larger space of all product-measurable integrands. -/
noncomputable def progressiveEnergyRange
    {Ω : Type*} [MeasurableSpace Ω] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (c : ℕ → ℝ)
    (ν : Measure (Ω × ℝ)) : Submodule ℝ (Lp ℝ 2 ν) :=
  (progressiveEnergyToLp F c ν).range

theorem progressive_energy_toLp_eq_iff
    {Ω : Type*} [MeasurableSpace Ω] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (c : ℕ → ℝ) (ν : Measure (Ω × ℝ))
    (H G : progressiveEnergyIntegrands F c ν) :
    progressiveEnergyToLp F c ν H = progressiveEnergyToLp F c ν G ↔ H.val =ᵐ[ν] G.val :=
  MemLp.toLp_eq_toLp_iff H.property.2.2 G.property.2.2

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.progressive_energy_toLp_eq_iff
