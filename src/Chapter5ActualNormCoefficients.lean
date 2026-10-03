import Chapter5FiniteEnergyNorm
import Chapter5PerturbationNormCoefficients

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The weighted energy inequalities for concrete processes imply the
printed two norm coefficients, with lambda explicitly positive. -/
theorem actual_energy_norm_coefficients
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R C β ell mu ε : ℝ) (hR : 0≤R) (hell : 0<ell) (hgap : C<ell^2) (hmu : 0<mu)
    (Y Z G : Ω × ℝ → ℝ)
    (hY : (∫ w,(∫ r in 0..R,Real.exp (β*r)*Y (w,r)^2) ∂P)≤
      R*(ε^2*(∫ w,(∫ r in 0..R,Real.exp (β*r)*G (w,r)^2) ∂P)/mu^2))
    (hZ : (∫ w,(∫ r in 0..R,Real.exp (β*r)*Z (w,r)^2) ∂P)≤
      ell^2/(ell^2-C)*(ε^2*(∫ w,(∫ r in 0..R,Real.exp (β*r)*G (w,r)^2) ∂P)/mu^2)) :
    finiteEnergyNorm P R β Y≤|ε| *(Real.sqrt R/mu)*finiteEnergyNorm P R β G ∧
    finiteEnergyNorm P R β Z≤|ε| *(ell/(mu*Real.sqrt (ell^2-C)))*finiteEnergyNorm P R β G := by
  have hy : (finiteEnergyNorm P R β Y)^2≤R*(ε^2*(finiteEnergyNorm P R β G)^2/mu^2) := by
    simpa only [finiteEnergyNorm_sq P R β hR] using hY
  have hz : (finiteEnergyNorm P R β Z)^2≤ell^2/(ell^2-C)*(ε^2*(finiteEnergyNorm P R β G)^2/mu^2) := by
    simpa only [finiteEnergyNorm_sq P R β hR] using hZ
  have hh := perturbation_norm_coefficients R C ell mu ε (finiteEnergyNorm P R β G)
    (finiteEnergyNorm P R β Y) (finiteEnergyNorm P R β Z) 0 hR hell hgap hmu
    (finiteEnergyNorm_nonneg _ _ _ _) (finiteEnergyNorm_nonneg _ _ _ _) (finiteEnergyNorm_nonneg _ _ _ _)
    le_rfl hy hz (by
      simpa only [zero_pow (by decide : 2≠0)] using
        div_nonneg (mul_nonneg (sq_nonneg ε) (sq_nonneg (finiteEnergyNorm P R β G))) (sq_nonneg mu))
  exact ⟨hh.1,hh.2.1⟩

end Asakura.Chapter5
