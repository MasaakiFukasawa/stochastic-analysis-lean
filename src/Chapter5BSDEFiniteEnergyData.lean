import Chapter5BSDECalculusData

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Finite-horizon energy obligations appearing in the a-priori proof. -/
structure BSDEFiniteEnergyData
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (W : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ) (R : ℝ)
    extends BSDECalculusData P F W c where
  measurableY : Measurable (fun z : Ω × ℝ => Y (realTimeClamp z.2) z.1)
  energyY : MemLp (fun z : Ω × ℝ => Y (realTimeClamp z.2) z.1) 2 (P.prod (volume.restrict (Ioc 0 R)))
  energyZ : MemLp Z 2 (P.prod (volume.restrict (Ioc 0 R)))
  energyB : MemLp B 2 (P.prod (volume.restrict (Ioc 0 R)))
  terminal : MemLp (Y (realTimeClamp R)) 2 P

noncomputable def BSDEFiniteEnergyData.sub
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t≤m)
    (W : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (R : ℝ)
    (u v : BSDEFiniteEnergyData P F W c R) : BSDEFiniteEnergyData P F W c R where
  toBSDECalculusData := u.toBSDECalculusData.sub P F hF hle W c hc v.toBSDECalculusData
  measurableY := u.measurableY.sub v.measurableY
  energyY := u.energyY.sub v.energyY
  energyZ := u.energyZ.sub v.energyZ
  energyB := u.energyB.sub v.energyB
  terminal := u.terminal.sub v.terminal

end Asakura.Chapter5
