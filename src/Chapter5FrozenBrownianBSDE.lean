import Chapter5FrozenFromRepresentation
import Chapter5NaturalObservationMeasurable
import Chapter5ProgressivePrefixRestriction

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- The frozen BSDE step, with the terminal Brownian representation,
conditional process, adaptedness, continuity and both L² memberships
constructed from the manuscript's data. -/
theorem frozen_brownian_bsde_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (W A : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0<c j) (hcm : StrictMono c) (hcT : ∀ j,(c j:EReal)<T)
    (hct : StrictMono (fun j => realTimeClamp (T := T) (c j)))
    (hcut : ∀ j,realTimeClamp (T := T) (c j)<⊤)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    (hco : ∀ r,∃ j,r≤c j)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hFnat : F (realTimeClamp R)=Asakura.nullAugmentation (m := m) P (pastSigma W (realTimeClamp R)))
    (ξ : Ω → ℝ) (hξ : MemLp ξ 2 P) (hξm : Measurable[F (realTimeClamp R)] ξ)
    (f : Ω × ℝ → ℝ) (hfm : Measurable f)
    (hfp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => f (z.1,z.2.val)))
    (hfi : MemLp f 2 (P.prod (volume.restrict (Ioc 0 R)))) :
    ∃ Y Z : Ω × ℝ → ℝ,∃ M : ClosedTime T → Ω → ℝ,
      ContinuousM2Witness P F M ∧ ItoCovarianceFormula P F W Z M ∧
      Measurable Y ∧ Measurable Z ∧
      MemLp Y 2 (P.prod (volume.restrict (Ioc 0 R))) ∧ MemLp Z 2 (P.prod (volume.restrict (Ioc 0 R))) ∧
      (@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) R => Y (z.1,z.2.val))) ∧
      (@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) R => Z (z.1,z.2.val))) ∧
      (∀ t : Icc (0:ℝ) R,Measurable[F (realTimeClamp t.val)] (fun w => Y (w,t.val))) ∧
      (∀ᵐ w ∂P,ContinuousOn (fun t => Y (w,t)) (Icc 0 R)) ∧
      ((fun w => Y (w,R)) =ᵐ[P] ξ) ∧
      (∀ t∈Icc 0 R,(fun w => Y (w,t)) =ᵐ[P]
        fun w => ξ w+(∫ r in t..R,f (w,r))-(M (realTimeClamp R) w-M (realTimeClamp t) w)) ∧
      (∃ a : ℝ,Y=(fun z => a+M (realTimeClamp z.2) z.1-(∫ r in 0..z.2,f (z.1,r)))) ∧
      MemLp Z 2 (P.prod (volume.restrict (Ioi 0))) ∧
      (∀ j,@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c j) => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) (c j) => Z (z.1,z.2.val))) := by
  classical
  let U := fun w => ξ w+(∫ r in 0..R,f (w,r))
  have hU : MemLp U 2 P := hξ.add (time_primitive_memLp_two P R hR f hfm hfi R ⟨hR,le_rfl⟩)
  have hUm : Measurable[F (realTimeClamp R)] U :=
    hξm.add (progressive_time_primitive_adapted R hR
      (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val)) f hfp ⟨R,hR,le_rfl⟩)
  have hRt : realTimeClamp (T := T) R<⊤ := by
    change (realTimeClamp R:EReal)<T
    rw [real_time_clamp_eq R hR hRT.le]
    exact hRT
  have hUg := (natural_observation_aestronglyMeasurable P F W (realTimeClamp R) hRt hFnat U hUm).congr hU.coeFn_toLp.symm
  have hCs (i j : Fin 1) : LocalCovarianceWitness P F W W (fun t w => if i=j then A t w else 0) := by
    have he : i=j := Subsingleton.elim _ _
    simpa only [he,ite_true] using hA
  obtain ⟨H,M,hM,hMI,he⟩ := brownian_ito_representation_actual P hT F hF hle hnull (fun _ : Fin 1 => W) A
    (fun _ => hW) hCs hclock c hc hcm hcT hct hcut hcc hco (hU.toLp U) hUg
  have hmean : (∫ w,(hU.toLp U) w ∂P)=∫ w,U w ∂P := integral_congr_ae hU.coeFn_toLp
  have hrep : U =ᵐ[P] fun w => (∫ w,U w ∂P)+M 0 ⊤ w := by
    filter_upwards [he,hU.coeFn_toLp] with w hw huw
    simpa only [huw,hmean,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] using hw
  obtain ⟨Y,hYeq,hYm,hYL,hYp,hYa,hYc,hYT,hBSDE⟩ := frozen_bsde_from_terminal_representation P F hF hle R hR
    ξ hξ hξm f hfm hfp hfi (M 0) (hM 0) (∫ w,U w ∂P) hrep
  have hZL : MemLp (H 0).val 2 (P.prod (volume.restrict (Ioc 0 R))) :=
    (H 0).property.2.2.mono_measure (Measure.prod_mono (le_refl P)
      (Measure.restrict_mono (fun r hr => hr.1) (le_refl volume)))
  have hZp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => (H 0).val (z.1,z.2.val)) := by
    obtain ⟨l,hl⟩ := hco R
    exact progressive_real_prefix_restriction (fun r => F (realTimeClamp r)) (H 0).val R (c l) hl ((H 0).property.2.1 l)
  exact ⟨Y,(H 0).val,M 0,hM 0,hMI 0,hYm,(H 0).property.1,hYL,hZL,hYp,hZp,hYa,hYc,hYT,hBSDE,⟨_,hYeq⟩,(H 0).property.2.2,(H 0).property.2.1⟩

end Asakura.Chapter5
