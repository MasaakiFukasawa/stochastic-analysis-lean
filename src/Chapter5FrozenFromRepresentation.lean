import Chapter5ConditionalProcessConstructed
import Chapter5FrozenBSDEConstruction
import Chapter5FrozenProgressive
import Chapter2ContinuousIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The actual terminal integral representation produces the frozen BSDE
solution and its progressive L² membership. The conditional expectation
process is constructed rather than supplied as an input. -/
theorem frozen_bsde_from_terminal_representation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t≤m)
    (R : ℝ) (hR : 0≤R)
    (ξ : Ω → ℝ) (hξ : MemLp ξ 2 P) (hξm : Measurable[F (realTimeClamp R)] ξ)
    (f : Ω × ℝ → ℝ) (hfm : Measurable f)
    (hfp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => f (z.1,z.2.val)))
    (hfi : MemLp f 2 (P.prod (volume.restrict (Ioc 0 R))))
    (M : ClosedTime T → Ω → ℝ) (hM : ContinuousM2Witness P F M) (c : ℝ)
    (hrep : (fun w => ξ w+(∫ r in 0..R,f (w,r))) =ᵐ[P] fun w => c+M ⊤ w) :
    ∃ Y : Ω × ℝ → ℝ,
      Y=(fun z => c+M (realTimeClamp z.2) z.1-(∫ r in 0..z.2,f (z.1,r))) ∧
      Measurable Y ∧ MemLp Y 2 (P.prod (volume.restrict (Ioc 0 R))) ∧
      (@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) R => Y (z.1,z.2.val))) ∧
      (∀ t : Icc (0:ℝ) R,Measurable[F (realTimeClamp t.val)] (fun w => Y (w,t.val))) ∧
      (∀ᵐ w ∂P,ContinuousOn (fun t => Y (w,t)) (Icc 0 R)) ∧
      ((fun w => Y (w,R)) =ᵐ[P] ξ) ∧
      (∀ t∈Icc 0 R,(fun w => Y (w,t)) =ᵐ[P]
        fun w => ξ w+(∫ r in t..R,f (w,r))-(M (realTimeClamp R) w-M (realTimeClamp t) w)) := by
  let U := fun w => ξ w+(∫ r in 0..R,f (w,r))
  have hU : MemLp U 2 P := hξ.add (time_primitive_memLp_two P R hR f hfm hfi R ⟨hR,le_rfl⟩)
  obtain ⟨hKm,hKc,hKa,hKCE⟩ := conditional_process_from_represented_terminal P F hle U hU M hM c hrep
  let K := fun z : Ω × ℝ => c+M (realTimeClamp z.2) z.1
  obtain ⟨Y,hYeq,hYm,hYL,hYa,hYc,hYT,hBSDE⟩ := frozen_bsde_from_conditional_process P R hR
    (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val)) (fun t => hle _) ξ hξ hξm f hfm hfp hfi K hKm
    (fun t => hKa _) (fun w => (hKc w).continuousOn) (fun t => hKCE (realTimeClamp t.val))
  refine ⟨Y,hYeq,hYm,hYL,?_,hYa,hYc,hYT,?_⟩
  · rw [hYeq]
    apply frozen_output_progressive R hR _ K f _ hfp
    exact continuous_adapted_real_progressive F hF K R hR
      (fun r _ => hKa _) (fun w => (hKc w).continuousOn)
  · intro t ht
    filter_upwards [hBSDE t ht] with w hw
    dsimp only [K] at hw
    linarith only [hw]

end Asakura.Chapter5
