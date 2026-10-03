import Chapter8ConjugateFlow

open MeasureTheory Set
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- A Lipschitz map sends every finite-cost coupling to a coupling of its
pushforwards, with the expected squared-cost bound. -/
theorem coupling_map_bound {E G : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    {μ ν : Measure E} (c : QuadraticCoupling μ ν) (f : E → G) (hf : Measurable f)
    (a : ℝ) (ha : 0 ≤ a) (hb : ∀ x y, ‖f x-f y‖ ≤ a*‖x-y‖) :
    ∃ d : QuadraticCoupling (μ.map f) (ν.map f), couplingEnergy d ≤ a^2*couplingEnergy c := by
  let Z := Prod.map f f
  have hZ : Measurable Z := hf.prodMap hf
  have hl : (c.measure.map Z).map Prod.fst = μ.map f := by
    rw [Measure.map_map measurable_fst hZ]
    change c.measure.map (f ∘ Prod.fst) = _
    rw [← Measure.map_map hf measurable_fst,c.left]
  have hr : (c.measure.map Z).map Prod.snd = ν.map f := by
    rw [Measure.map_map measurable_snd hZ]
    change c.measure.map (f ∘ Prod.snd) = _
    rw [← Measure.map_map hf measurable_snd,c.right]
  have hb' (z : E × E) : ‖(Z z).1-(Z z).2‖^2 ≤ a^2*‖z.1-z.2‖^2 := by
    change ‖f z.1-f z.2‖^2 ≤ a^2*‖z.1-z.2‖^2
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hb z.1 z.2) 2
    rw [mul_pow] at hh
    exact hh
  have hi : Integrable (fun z : E × E => ‖(Z z).1-(Z z).2‖^2) c.measure := by
    apply (c.finite.const_mul (a^2)).mono' (by fun_prop)
    apply ae_of_all _
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hb' z
  have hi' : Integrable (fun z : G × G => ‖z.1-z.2‖^2) (c.measure.map Z) :=
    (integrable_map_measure (by fun_prop) hZ.aemeasurable).mpr hi
  let d : QuadraticCoupling (μ.map f) (ν.map f) :=
    ⟨c.measure.map Z,(Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).mpr inferInstance,hl,hr,hi'⟩
  refine ⟨d,?_⟩
  change (∫ z, ‖z.1-z.2‖^2 ∂c.measure.map Z) ≤ _
  rw [integral_map hZ.aemeasurable (by fun_prop)]
  have hh := integral_mono hi (c.finite.const_mul (a^2)) hb'
  rwa [integral_const_mul] at hh

/-- The infimum argument works even when the image is a different normed
space; this gives both norm comparison and marginal projection bounds. -/
theorem transport_map_bound {E G : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ ν : Measure E) [Nonempty (QuadraticCoupling μ ν)]
    (f : E → G) (hf : Measurable f) (a : ℝ) (ha : 0 < a)
    (hb : ∀ x y, ‖f x-f y‖ ≤ a*‖x-y‖) :
    transportDistance (μ.map f) (ν.map f) ≤ a*transportDistance μ ν := by
  choose lift hlift using fun c : QuadraticCoupling μ ν => coupling_map_bound c f hf a ha.le hb
  letI : Nonempty (QuadraticCoupling (μ.map f) (ν.map f)) := ⟨lift (Classical.choice inferInstance)⟩
  have hE : transportEnergy (μ.map f) (ν.map f)/a^2 ≤ transportEnergy μ ν := by
    apply le_csInf (range_nonempty _)
    rintro _ ⟨c,rfl⟩
    exact (div_le_iff₀ (sq_pos_of_pos ha)).mpr (by
      simpa only [mul_comm] using (transport_energy_le_coupling (lift c)).trans (hlift c))
  apply (Real.sqrt_le_iff).mpr
  refine ⟨mul_nonneg ha.le (Real.sqrt_nonneg _),?_⟩
  rw [mul_pow,transportDistance,Real.sq_sqrt (transport_energy_nonnegative μ ν)]
  simpa only [mul_comm] using (div_le_iff₀ (sq_pos_of_pos ha)).mp hE

/-- An invertible continuous linear change of coordinates transfers the
quadratic-norm convergence estimate back to the original norm. -/
theorem transport_coordinate_comparison {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G]
    (A : E ≃L[ℝ] G) (μ ν : Measure E)
    [Nonempty (QuadraticCoupling (μ.map A) (ν.map A))] :
    transportDistance μ ν ≤ (‖A.symm.toContinuousLinearMap‖+1)*
      transportDistance (μ.map A) (ν.map A) := by
  have hh := transport_map_bound (μ.map A) (ν.map A) A.symm A.symm.continuous.measurable
    (‖A.symm.toContinuousLinearMap‖+1) (by positivity) (fun x y => by
      rw [← map_sub]
      exact (A.symm.toContinuousLinearMap.le_opNorm (x-y)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)))
  have hμ : (μ.map A).map A.symm = μ := by
    rw [Measure.map_map A.symm.continuous.measurable A.continuous.measurable]
    simp only [Function.comp_def,A.symm_apply_apply]
    exact Measure.map_id
  have hν : (ν.map A).map A.symm = ν := by
    rw [Measure.map_map A.symm.continuous.measurable A.continuous.measurable]
    simp only [Function.comp_def,A.symm_apply_apply]
    exact Measure.map_id
  rwa [hμ,hν] at hh

end Asakura.Chapter8
