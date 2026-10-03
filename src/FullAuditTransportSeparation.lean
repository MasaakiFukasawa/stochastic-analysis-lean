import FullAuditTransportEnergy

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Bounded Lipschitz tests are controlled by each actual coupling's quadratic
 cost, using variance nonnegativity and the pointwise Lipschitz inequality. -/
theorem coupling_lipschitz_test_bound {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E}
    (c : QuadraticCoupling μ ν) (f : E →ᵇ ℝ) (L : ℝ≥0) (hL : LipschitzWith L f) :
    ((∫ x, f x ∂μ)-(∫ x, f x ∂ν))^2 ≤ (L:ℝ)^2*couplingEnergy c := by
  have hfl : MemLp (fun z : E × E => f z.1) 2 c.measure :=
    MemLp.of_bound (f.continuous.measurable.comp measurable_fst).aestronglyMeasurable ‖f‖
      (ae_of_all _ (fun z => f.norm_coe_le_norm z.1))
  have hfr : MemLp (fun z : E × E => f z.2) 2 c.measure :=
    MemLp.of_bound (f.continuous.measurable.comp measurable_snd).aestronglyMeasurable ‖f‖
      (ae_of_all _ (fun z => f.norm_coe_le_norm z.2))
  have hd : MemLp (fun z : E × E => f z.1-f z.2) 2 c.measure := hfl.sub hfr
  have hv := variance_nonneg (fun z : E × E => f z.1-f z.2) c.measure
  rw [variance_eq_sub hd] at hv
  simp only [Pi.pow_apply] at hv
  have hi : (∫ z, (f z.1-f z.2)^2 ∂c.measure) ≤ (L:ℝ)^2*couplingEnergy c := by
    rw [couplingEnergy,← integral_const_mul]
    apply integral_mono ((memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mp hd) (c.finite.const_mul _)
    intro z
    have h := hL.dist_le_mul z.1 z.2
    rw [Real.dist_eq,dist_eq_norm] at h
    have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
    simpa only [sq_abs,mul_pow] using hsq
  have he : (∫ z, f z.1-f z.2 ∂c.measure) = (∫ x, f x ∂μ)-(∫ x, f x ∂ν) := by
    rw [integral_sub (hfl.integrable (by norm_num)) (hfr.integrable (by norm_num)),
      ← integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable,
      ← integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable,c.left,c.right]
  rw [he] at hv
  linarith

/-- Zero infimum cost identifies all bounded Lipschitz integrals. -/
theorem zero_transport_tests {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ ν : Measure E)
    [Nonempty (QuadraticCoupling μ ν)] (hz : transportEnergy μ ν = 0)
    (f : E →ᵇ ℝ) (L : ℝ≥0) (hL : LipschitzWith L f) :
    (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
  let D := (∫ x, f x ∂μ)-(∫ x, f x ∂ν)
  have hD : D^2 ≤ 0 := by
    by_cases hl : L=0
    · have h := coupling_lipschitz_test_bound (Classical.choice inferInstance : QuadraticCoupling μ ν) f L hL
      simpa [D,hl] using h
    · have hp : 0 < (L:ℝ)^2 := sq_pos_of_ne_zero (by exact_mod_cast hl)
      have hi : D^2/(L:ℝ)^2 ≤ transportEnergy μ ν := by
        apply le_csInf (range_nonempty _)
        rintro _ ⟨c,rfl⟩
        apply (div_le_iff₀ hp).mpr
        simpa only [mul_comm] using coupling_lipschitz_test_bound c f L hL
      rw [hz] at hi
      have := (div_le_iff₀ hp).mp hi
      simpa only [zero_mul] using this
  have : D=0 := by nlinarith [sq_nonneg D]
  exact sub_eq_zero.mp this

/-- Bounded Lipschitz tests separate probability measures, by the standard
 weak-convergence criterion applied to a constant sequence. -/
theorem zero_transport_measures_equal {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [Nonempty (QuadraticCoupling μ ν)] (hz : transportEnergy μ ν = 0) : μ=ν := by
  let p : ProbabilityMeasure E := ⟨μ,inferInstance⟩
  let q : ProbabilityMeasure E := ⟨ν,inferInstance⟩
  have hconv : Tendsto (fun _ : ℕ => p) atTop (nhds q) := by
    apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
    intro f hb hl
    let b : E →ᵇ ℝ := { toFun := f, continuous_toFun := hl.choose_spec.continuous, map_bounded' := hb }
    have he := zero_transport_tests μ ν hz b hl.choose hl.choose_spec
    change Tendsto (fun _ : ℕ => ∫ x, b x ∂μ) atTop (nhds (∫ x, b x ∂ν))
    rw [he]
    exact tendsto_const_nhds
  have he : p=q := tendsto_nhds_unique tendsto_const_nhds hconv
  exact congrArg (fun r : ProbabilityMeasure E => (r : Measure E)) he

end Asakura.FullAudit
