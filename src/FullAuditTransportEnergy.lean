import FullAuditLangevinPaths
import FullAuditGaussianCovariance
import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

structure QuadraticCoupling {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (μ ν : Measure E) where
  measure : Measure (E × E)
  probability : IsProbabilityMeasure measure
  left : measure.map Prod.fst = μ
  right : measure.map Prod.snd = ν
  finite : Integrable (fun z : E × E => ‖z.1-z.2‖^2) measure

instance {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {μ ν : Measure E}
    (c : QuadraticCoupling μ ν) : IsProbabilityMeasure c.measure := c.probability

noncomputable def couplingEnergy {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {μ ν : Measure E} (c : QuadraticCoupling μ ν) : ℝ := ∫ z, ‖z.1-z.2‖^2 ∂c.measure

noncomputable def transportEnergy {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (μ ν : Measure E) : ℝ := sInf (range fun c : QuadraticCoupling μ ν => couplingEnergy c)

noncomputable def transportDistance {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (μ ν : Measure E) : ℝ := Real.sqrt (transportEnergy μ ν)

theorem coupling_energy_nonnegative {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {μ ν : Measure E} (c : QuadraticCoupling μ ν) : 0 ≤ couplingEnergy c :=
  integral_nonneg fun _ => sq_nonneg _

theorem transport_energy_nonnegative {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (μ ν : Measure E) [Nonempty (QuadraticCoupling μ ν)] : 0 ≤ transportEnergy μ ν := by
  apply le_csInf (range_nonempty _)
  rintro _ ⟨c,rfl⟩
  exact coupling_energy_nonnegative c

theorem transport_energy_le_coupling {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {μ ν : Measure E} (c : QuadraticCoupling μ ν) : transportEnergy μ ν ≤ couplingEnergy c := by
  apply csInf_le ⟨0,?_⟩ (mem_range_self c)
  rintro _ ⟨d,rfl⟩
  exact coupling_energy_nonnegative d

/-- Taking the infimum of the squared coupling costs, without assuming an
 optimal coupling exists. -/
theorem transport_contraction_from_lift {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (μ ν μt νt : Measure E) [Nonempty (QuadraticCoupling μ ν)]
    (a : ℝ) (ha : 0 < a)
    (lift : QuadraticCoupling μ ν → QuadraticCoupling μt νt)
    (hbound : ∀ c, couplingEnergy (lift c) ≤ a^2*couplingEnergy c) :
    transportDistance μt νt ≤ a*transportDistance μ ν := by
  letI : Nonempty (QuadraticCoupling μt νt) := ⟨lift (Classical.choice inferInstance)⟩
  have hE : transportEnergy μt νt/a^2 ≤ transportEnergy μ ν := by
    apply le_csInf (range_nonempty _)
    rintro _ ⟨c,rfl⟩
    exact (div_le_iff₀ (sq_pos_of_pos ha)).mpr (by simpa only [mul_comm] using (transport_energy_le_coupling (lift c)).trans (hbound c))
  have hboundE : transportEnergy μt νt ≤ a^2*transportEnergy μ ν := by
    have := (div_le_iff₀ (sq_pos_of_pos ha)).mp hE
    simpa only [mul_comm] using this
  apply (Real.sqrt_le_iff).mpr
  refine ⟨mul_nonneg ha.le (Real.sqrt_nonneg _),?_⟩
  rw [mul_pow,transportDistance,Real.sq_sqrt (transport_energy_nonnegative μ ν)]
  exact hboundE

/-- The product law supplies a finite-cost coupling of any two finite-second-
 moment distributions. -/
theorem quadratic_coupling_nonempty {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x : E => x) 2 μ) (hν : MemLp (fun x : E => x) 2 ν) :
    Nonempty (QuadraticCoupling μ ν) := by
  have hm : MemLp (fun z : E × E => z.1) 2 (μ.prod ν) := by
    simpa only [Function.comp_def] using hμ.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ν))
  have hn : MemLp (fun z : E × E => z.2) 2 (μ.prod ν) := by
    simpa only [Function.comp_def] using hν.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := ν))
  have hd := hm.sub hn
  have hi : Integrable (fun z : E × E => ‖z.1-z.2‖^2) (μ.prod ν) := by
    simpa using (memLp_two_iff_integrable_sq hd.norm.aestronglyMeasurable).mp hd.norm
  exact ⟨⟨μ.prod ν,inferInstance,(measurePreserving_fst (μ := μ) (ν := ν)).map_eq,
    (measurePreserving_snd (μ := μ) (ν := ν)).map_eq,hi⟩⟩

end Asakura.FullAudit
