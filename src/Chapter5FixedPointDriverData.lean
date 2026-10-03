import Chapter5FrozenClassRelation
import Chapter5ReplaceFiniteDriver

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- A fixed point of the constructed relation solves the original
nonlinear BSDE, not merely an equation for arbitrarily chosen L² classes. -/
theorem frozen_class_fixed_point_driver_data
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (W : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ)
    (hc : ∀ j,0≤c j) (hcT : ∀ j,(c j:EReal)<T) (hco : ∀ r,∃ j,r≤c j)
    (R β : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (hβ : 0≤β) (ξ : Ω → ℝ)
    (f : (Ω × ℝ) × (ℝ × ℝ) → ℝ) (hfm : Measurable f)
    (hf0 : MemLp (fun z => f (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (C : ℝ) (hC : 0≤C)
    (hl : ∀ z y z',|f (z,y,z')-f (z,0,0)|≤C*(|y|+|z'|))
    (x : WithLp 2 ((progressiveEnergyRange F (fun _ => R) (exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β)) ×
      (progressiveEnergyRange F (fun _ => R) (exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β))))
    (hx : frozenBSDEClassRelation P F W c hco R β hR hβ ξ f x x) :
    ∃ u : BSDEFiniteEnergyData P F W c R,
      (u.Y (realTimeClamp R) =ᵐ[P] ξ) ∧
      (∀ w r,r∈Icc 0 R → u.B (w,r)= -f ((w,r),u.Y (realTimeClamp r) w,u.Z (w,r))) ∧
      (@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) R => u.Y (realTimeClamp z.2.val) z.1)) := by
  obtain ⟨i,j,hi,hj,u,hup,hut,huB,huy,huz⟩ := hx
  have hiy := (i.realize_eq_iff P F R β hR hβ (u.outputY P F W c R hup)).mp (hi.trans huy.symm)
  have hjz := (j.realize_eq_iff P F R β hR hβ (u.outputZ P F W c hco R)).mp (hj.trans huz.symm)
  let G := fun z => f (z,u.Y (realTimeClamp z.2) z.1,u.Z z)
  have hGm : Measurable G := hfm.comp (measurable_id.prodMk (u.measurableY.prodMk u.measurableZ))
  have hG2 := generator_memLp _ f hfm _ _ u.measurableY u.measurableZ u.energyY u.energyZ hf0 C hC hl
  have hs : ∀ᵐ z ∂P.prod (volume.restrict (Ioc 0 R)),z.2∈Ioc 0 R := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).mpr
    exact ae_of_all _ fun _ => ae_restrict_mem measurableSet_Ioc
  have he : u.B =ᵐ[P.prod (volume.restrict (Ioc 0 R))] fun z => -G z := by
    filter_upwards [hiy,hjz,hs] with z hy hz hs
    change i.value z=u.Y (realTimeClamp z.2) z.1 at hy
    change j.value z=u.Z z at hz
    change u.B z= -f (z,u.Y (realTimeClamp z.2) z.1,u.Z z)
    rw [huB z.1 z.2 ⟨hs.1.le,hs.2⟩,hy,hz]
  let v := u.replaceFiniteDriver P F W c hc R (fun z => -G z) hGm.neg he
  refine ⟨v,hut,?_,hup⟩
  intro w r hr
  change (if r∈Icc 0 R then -G (w,r) else u.B (w,r))= -G (w,r)
  exact if_pos hr

end Asakura.Chapter5
