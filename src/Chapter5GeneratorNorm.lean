import Chapter5WeightedGeneratorEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The unsquared Lipschitz estimate in the perturbation proof uses the
L² triangle inequality, giving C times the sum of the two error norms. -/
theorem generator_L2_norm_bound
    {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (Y Z G : E → ℝ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) (hG : MemLp G 2 μ)
    (C : ℝ) (hC : 0≤C)
    (hb : ∀ᵐ z ∂μ,|G z|≤C*(|Y z|+|Z z|)) :
    ‖hG.toLp G‖≤C*(‖hY.toLp Y‖+‖hZ.toLp Z‖) := by
  let H := fun z => ‖Y z‖+‖Z z‖
  have hH : MemLp H 2 μ := hY.norm.add hZ.norm
  have hh : ‖hG.toLp G‖≤C*‖hH.toLp H‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hG.coeFn_toLp,hH.coeFn_toLp,hb] with z hgz hhz hbz
    rw [hgz,hhz]
    simpa only [H,Real.norm_eq_abs,abs_of_nonneg (add_nonneg (abs_nonneg (Y z)) (abs_nonneg (Z z)))] using hbz
  have heY : ‖hY.norm.toLp (fun z => ‖Y z‖)‖=‖hY.toLp Y‖ := by
    simp only [Lp.norm_toLp,eLpNorm_norm Y hY.aestronglyMeasurable]
  have heZ : ‖hZ.norm.toLp (fun z => ‖Z z‖)‖=‖hZ.toLp Z‖ := by
    simp only [Lp.norm_toLp,eLpNorm_norm Z hZ.aestronglyMeasurable]
  have hsum : ‖hH.toLp H‖≤‖hY.toLp Y‖+‖hZ.toLp Z‖ := by
    rw [show hH.toLp H=hY.norm.toLp (fun z => ‖Y z‖)+hZ.norm.toLp (fun z => ‖Z z‖) from MemLp.toLp_add hY.norm hZ.norm]
    exact (norm_add_le _ _).trans_eq (by rw [heY,heZ])
  exact hh.trans (mul_le_mul_of_nonneg_left hsum hC)

end Asakura.Chapter5
