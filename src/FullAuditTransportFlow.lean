import FullAuditTransportSeparation
import Mathlib.Topology.Order.Monotone

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable def flowLaw {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (μ : Measure E) (P : Measure Ω) (F : E → Ω → E) := (μ.prod P).map (Function.uncurry F)

/-- Lift an arbitrary coupling by giving its two coordinates the same noise,
 and identify both output marginals by product pushforwards. -/
theorem coupling_lift_shared_noise {E Ω : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    {μ ν : Measure E} (c : QuadraticCoupling μ ν) (P : Measure Ω) [IsProbabilityMeasure P]
    (F : E → Ω → E) (hF : Measurable (Function.uncurry F)) (a : ℝ) (ha : 0 ≤ a)
    (hLip : ∀ x y, ∀ᵐ ω ∂P, ‖F x ω-F y ω‖ ≤ a*‖x-y‖) :
    ∃ d : QuadraticCoupling (flowLaw μ P F) (flowLaw ν P F), couplingEnergy d ≤ a^2*couplingEnergy c := by
  let R := c.measure.prod P
  let Z : (E × E) × Ω → E × E := fun q => (F q.1.1 q.2,F q.1.2 q.2)
  have hZ : Measurable Z :=
    (hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (hF.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hl : (R.map Z).map Prod.fst = flowLaw μ P F := by
    rw [Measure.map_map measurable_fst hZ]
    have hm : R.map (Prod.map Prod.fst id) = μ.prod P := by
      dsimp only [R]
      rw [← Measure.map_prod_map _ _ measurable_fst measurable_id,c.left,Measure.map_id]
    rw [flowLaw,← hm,Measure.map_map hF (measurable_fst.prodMap measurable_id)]
    rfl
  have hr : (R.map Z).map Prod.snd = flowLaw ν P F := by
    rw [Measure.map_map measurable_snd hZ]
    have hm : R.map (Prod.map Prod.snd id) = ν.prod P := by
      dsimp only [R]
      rw [← Measure.map_prod_map _ _ measurable_snd measurable_id,c.right,Measure.map_id]
    rw [flowLaw,← hm,Measure.map_map hF (measurable_snd.prodMap measurable_id)]
    rfl
  have hi : Integrable (fun q : (E × E) × Ω => ‖q.1.1-q.1.2‖^2) R := by
    simpa only [Function.comp_def] using
      (measurePreserving_fst (μ := c.measure) (ν := P)).integrable_comp_of_integrable c.finite
  have hb : ∀ᵐ q ∂R, ‖(Z q).1-(Z q).2‖^2 ≤ a^2*‖q.1.1-q.1.2‖^2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) (by fun_prop))).mpr
    apply ae_of_all _
    intro z
    filter_upwards [hLip z.1 z.2] with ω hω
    have h := pow_le_pow_left₀ (norm_nonneg _) hω 2
    simpa only [mul_pow] using h
  have hZi : Integrable (fun q => ‖(Z q).1-(Z q).2‖^2) R := by
    apply (hi.const_mul (a^2)).mono' (by fun_prop)
    filter_upwards [hb] with q hq
    rwa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hfini : Integrable (fun z : E × E => ‖z.1-z.2‖^2) (R.map Z) :=
    (integrable_map_measure (by fun_prop) hZ.aemeasurable).mpr hZi
  have hp : IsProbabilityMeasure (R.map Z) := (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).mpr inferInstance
  let d : QuadraticCoupling (flowLaw μ P F) (flowLaw ν P F) := ⟨R.map Z,hp,hl,hr,hfini⟩
  refine ⟨d,?_⟩
  change (∫ z, ‖z.1-z.2‖^2 ∂R.map Z) ≤ _
  rw [integral_map hZ.aemeasurable (by fun_prop)]
  calc
    _ ≤ ∫ q, a^2*‖q.1.1-q.1.2‖^2 ∂R := integral_mono_ae hZi (hi.const_mul _) hb
    _ = a^2*couplingEnergy c := by
      rw [integral_const_mul]
      congr 1
      change (∫ q : (E × E) × Ω, ‖q.1.1-q.1.2‖^2 ∂c.measure.prod P) = ∫ z, ‖z.1-z.2‖^2 ∂c.measure
      rw [← integral_map (μ := c.measure.prod P) (φ := Prod.fst) (f := fun z : E × E => ‖z.1-z.2‖^2) measurable_fst.aemeasurable (by fun_prop),Measure.map_fst_prod,measure_univ,one_smul]

/-- The manuscript's infimum of square-root costs equals the square root of
 the infimum used in the construction. -/
theorem transport_distance_infimum {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (μ ν : Measure E) [Nonempty (QuadraticCoupling μ ν)] :
    transportDistance μ ν = sInf (range fun c : QuadraticCoupling μ ν => Real.sqrt (couplingEnergy c)) := by
  rw [transportDistance,transportEnergy,
    Monotone.map_csInf_of_continuousAt Real.continuous_sqrt.continuousAt (fun x y h => Real.sqrt_le_sqrt h)
      (range_nonempty _) ⟨0,by rintro _ ⟨c,rfl⟩; exact coupling_energy_nonnegative c⟩]
  congr 1
  ext r
  simp only [mem_image,mem_range]
  constructor
  · rintro ⟨s,⟨c,rfl⟩,rfl⟩
    exact ⟨c,rfl⟩
  · rintro ⟨c,rfl⟩
    exact ⟨couplingEnergy c,⟨c,rfl⟩,rfl⟩

theorem shared_noise_transport_contraction {E Ω : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    (μ ν : Measure E) [Nonempty (QuadraticCoupling μ ν)]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : E → Ω → E)
    (hF : Measurable (Function.uncurry F)) (a : ℝ) (ha : 0 < a)
    (hLip : ∀ x y, ∀ᵐ ω ∂P, ‖F x ω-F y ω‖ ≤ a*‖x-y‖) :
    transportDistance (flowLaw μ P F) (flowLaw ν P F) ≤ a*transportDistance μ ν := by
  choose lift hlift using fun c : QuadraticCoupling μ ν => coupling_lift_shared_noise c P F hF a ha.le hLip
  exact transport_contraction_from_lift μ ν _ _ a ha lift hlift

end Asakura.FullAudit
