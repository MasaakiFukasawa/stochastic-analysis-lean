import Chapter5WeightedProcess

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

lemma finite_weighted_square_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β)
    (G : Ω × ℝ → ℝ) (hGm : Measurable G) (hG : MemLp G 2 (P.prod (volume.restrict (Ioc 0 R)))) :
    (∫ z,G z^2 ∂exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β)=
      ∫ w,(∫ r in 0..R,Real.exp (β*r)*G (w,r)^2) ∂P := by
  have hw := (finite_time_weighted_energy P R hR β hβ G hGm hG).1
  unfold exponentialEnergyMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]
    rw [integral_prod _ hw]
    simp only [intervalIntegral.integral_of_le hR]
  · exact (measurable_const.mul measurable_snd).exp.ennreal_ofReal
  · exact ae_of_all _ fun _ => ENNReal.ofReal_lt_top

/-- The generator's Lipschitz bound is integrated for the actual weighted
process representatives; the resulting energies are exactly the quotient
Hilbert norms used in the fixed-point argument. -/
theorem weighted_generator_difference_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β)
    (u v u' v' : FiniteProgressiveProcess P F R)
    (f : (Ω × ℝ) × (ℝ × ℝ) → ℝ) (hfm : Measurable f)
    (hf0 : MemLp (fun z => f (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (C : ℝ) (hC : 0≤C)
    (hl : ∀ z y₁ z₁ y₂ z₂,|f (z,y₁,z₁)-f (z,y₂,z₂)|≤C*(|y₁-y₂|+|z₁-z₂|)) :
    (∫ w,(∫ r in 0..R,Real.exp (β*r)*
      (f ((w,r),u.value (w,r),v.value (w,r))-f ((w,r),u'.value (w,r),v'.value (w,r)))^2) ∂P)≤
      2*C^2*(‖u.realize P F R β hR hβ-u'.realize P F R β hR hβ‖^2+
        ‖v.realize P F R β hR hβ-v'.realize P F R β hR hβ‖^2) := by
  let G := fun z => f (z,u.value z,v.value z)
  let H := fun z => f (z,u'.value z,v'.value z)
  have hGm : Measurable G := hfm.comp (measurable_id.prodMk (u.measurable.prodMk v.measurable))
  have hHm : Measurable H := hfm.comp (measurable_id.prodMk (u'.measurable.prodMk v'.measurable))
  have hG := generator_memLp _ f hfm u.value v.value u.measurable v.measurable u.energy v.energy hf0 C hC
    (fun z y z' => by simpa only [sub_zero] using hl z y z' 0 0)
  have hH := generator_memLp _ f hfm u'.value v'.value u'.measurable v'.measurable u'.energy v'.energy hf0 C hC
    (fun z y z' => by simpa only [sub_zero] using hl z y z' 0 0)
  have hy := (finite_weighted_memLp_two_iff P R hR β hβ _ (u.measurable.sub u'.measurable)).mpr (u.energy.sub u'.energy)
  have hz := (finite_weighted_memLp_two_iff P R hR β hβ _ (v.measurable.sub v'.measurable)).mpr (v.energy.sub v'.energy)
  have hf := (finite_weighted_memLp_two_iff P R hR β hβ _ (hGm.sub hHm)).mpr (hG.sub hH)
  have hh := generator_difference_energy _ _ _ _ hy hz hf C hC (ae_of_all _ fun z => hl z _ _ _ _)
  rw [finite_weighted_square_integral P R β hR hβ _ (hGm.sub hHm) (hG.sub hH),
    finite_weighted_square_integral P R β hR hβ _ (u.measurable.sub u'.measurable) (u.energy.sub u'.energy),
    finite_weighted_square_integral P R β hR hβ _ (v.measurable.sub v'.measurable) (v.energy.sub v'.energy)] at hh
  rw [u.difference_norm P F R β hR hβ u',v.difference_norm P F R β hR hβ v']
  exact hh

end Asakura.Chapter5
