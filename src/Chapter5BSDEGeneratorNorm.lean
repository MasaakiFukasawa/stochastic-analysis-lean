import Chapter5FiniteEnergyNorm
import Chapter5BSDEFiniteEnergyData

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

lemma finiteEnergyNorm_sub_comm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (R β : ℝ) (H G : Ω × ℝ → ℝ) :
    finiteEnergyNorm P R β (fun z => H z-G z)=finiteEnergyNorm P R β (fun z => G z-H z) := by
  unfold finiteEnergyNorm
  simp_rw [sub_sq_comm (H _) (G _)]

lemma bsde_generator_difference_norm
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (W : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ) (R β : ℝ) (hR : 0≤R) (hβ : 0≤β)
    (u v : BSDEFiniteEnergyData P F W c R)
    (f : (Ω × ℝ) × (ℝ × ℝ) → ℝ) (hfm : Measurable f)
    (hf0 : MemLp (fun z => f (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (C : ℝ) (hC : 0≤C)
    (hl : ∀ z y₁ z₁ y₂ z₂,|f (z,y₁,z₁)-f (z,y₂,z₂)|≤C*(|y₁-y₂|+|z₁-z₂|)) :
    finiteEnergyNorm P R β (fun z => f (z,u.Y (realTimeClamp z.2) z.1,u.Z z)-f (z,v.Y (realTimeClamp z.2) z.1,v.Z z))≤
      C*(finiteEnergyNorm P R β (fun z => u.Y (realTimeClamp z.2) z.1-v.Y (realTimeClamp z.2) z.1)+
        finiteEnergyNorm P R β (fun z => u.Z z-v.Z z)) := by
  have hmu := hfm.comp (measurable_id.prodMk (u.measurableY.prodMk u.measurableZ))
  have hmv := hfm.comp (measurable_id.prodMk (v.measurableY.prodMk v.measurableZ))
  have hiu := generator_memLp _ f hfm _ _ u.measurableY u.measurableZ u.energyY u.energyZ hf0 C hC
    (fun z y z' => by simpa only [sub_zero] using hl z y z' 0 0)
  have hiv := generator_memLp _ f hfm _ _ v.measurableY v.measurableZ v.energyY v.energyZ hf0 C hC
    (fun z y z' => by simpa only [sub_zero] using hl z y z' 0 0)
  exact finite_energy_generator_norm_bound P R β hR hβ _ _ _
    (u.measurableY.sub v.measurableY) (u.measurableZ.sub v.measurableZ) (hmu.sub hmv)
    (u.energyY.sub v.energyY) (u.energyZ.sub v.energyZ) (hiu.sub hiv) C hC (fun z => hl z _ _ _ _)

end Asakura.Chapter5
