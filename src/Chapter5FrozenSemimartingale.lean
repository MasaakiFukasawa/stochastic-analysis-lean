import Chapter5FiniteDriftRepresentative
import Chapter5ClippedDriftIntegral
import Chapter5ConditionalProcessConstructed

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- The frozen formula has an actual continuous semimartingale
realization. The time drift is constructed from the progressive L²
driver, after removal of one common sample-null set. -/
theorem frozen_semimartingale_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)≤T)
    (G : Ω × ℝ → ℝ) (hGm : Measurable G)
    (hGp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => G (z.1,z.2.val)))
    (hG2 : MemLp G 2 (P.prod (volume.restrict (Ioc 0 R))))
    (M : ClosedTime T → Ω → ℝ) (hM : ContinuousM2Witness P F M)
    (hMl : LocalMProcessWitness P F M) (a : ℝ) :
    ∃ Y V : ClosedTime T → Ω → ℝ,
      SemimartingaleDecomposition P F Y V M ∧
      (∀ w,Continuous (fun t => Y t w)) ∧
      (∀ᵐ w ∂P,∀ r∈Icc 0 R,Y (realTimeClamp r) w=a+M (realTimeClamp r) w-(∫ s in 0..r,G (w,s))) ∧
      (∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)≤T →
        V (realTimeClamp r) w=V ⊥ w+(∫ s in 0..r,-(Iic R).indicator (fun s => G (w,s)) s)) := by
  obtain ⟨J,hJm,hJp,hJi,hJe⟩ := finite_energy_drift_representative P F hnull R hR G hGm hGp hG2
  obtain ⟨B,hBv,hBc,hBe⟩ := progressive_integrable_drift_variation hT F hF R hR hRT J hJp hJi
  have hconst : AdaptedVariationWitness F (fun _ (_ : Ω) => a) := by
    refine ⟨(fun _ _ => a),(fun _ _ => 0),?_,?_,?_,?_⟩
    · exact fun _ => ⟨measurable_const,measurable_const⟩
    · exact fun _ => ⟨monotone_const,monotone_const⟩
    · exact fun _ _ => ⟨continuousWithinAt_const,continuousWithinAt_const⟩
    · exact fun _ _ => (sub_zero _).symm
  have hVv : AdaptedLocalVariationWitness F (fun t w => a-B t w) := by
    have hh := (global_variation_localized hT F hF _ hconst).add (hBv.smul (-1)) hF
    simpa only [neg_one_mul,← sub_eq_add_neg] using hh
  let V := fun t w => a-B t w
  let Y := fun t w => V t w+M t w
  have hB0 w : B ⊥ w=0 := by
    rw [hBe]
    have hp : (finitePrefixTime (T := T) R hR ⊥).val=0 := by
      change (min (0:EReal) (R:EReal)).toReal=0
      rw [min_eq_left (by exact_mod_cast hR)]
      rfl
    rw [hp,intervalIntegral.integral_same]
  refine ⟨Y,V,⟨hVv,hMl,?_,fun _ _ _ => rfl⟩,(fun w => (continuous_const.sub (hBc w)).add (hM.path w)),?_,?_⟩
  · intro w t ht
    exact ((continuous_const.sub (hBc w)).add (hM.path w)).continuousAt
  · filter_upwards [hJe] with w hw
    intro r hr
    have he : (∫ s in 0..r,J (w,s))=∫ s in 0..r,G (w,s) := by
      exact intervalIntegral.integral_congr (fun s _ => hw s)
    dsimp only [Y,V]
    rw [hBe,finite_prefix_time_min R r hR hr.1 ((EReal.coe_le_coe hr.2).trans hRT),min_eq_left hr.2,he]
    ring
  · filter_upwards [hJe] with w hw
    intro r hr hrT
    dsimp only [V]
    rw [hB0,hBe,finite_prefix_time_min R r hR hr hrT,intervalIntegral.integral_neg,
      clipped_driver_integral (fun s => G (w,s)) R r hR hr]
    have he : (∫ s in 0..min r R,J (w,s))=∫ s in 0..min r R,G (w,s) :=
      intervalIntegral.integral_congr (fun s _ => hw s)
    rw [he]
    ring

end Asakura.Chapter5

