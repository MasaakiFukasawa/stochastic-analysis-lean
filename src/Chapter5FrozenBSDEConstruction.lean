import Chapter5PrimitiveEnergySpace
import Chapter5ConditionalProcessEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Given the continuous conditional-expectation process supplied by the
preceding martingale representation theorem, construct the frozen BSDE
solution. Adaptedness, sample-time L², continuity and the terminal equation
are conclusions. No frozen BSDE solution is assumed. -/
theorem frozen_bsde_from_conditional_process
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0 ≤ R)
    (F : Icc (0:ℝ) R → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (ξ : Ω → ℝ) (hξ : MemLp ξ 2 P) (hξm : Measurable[F ⟨R,⟨hR,le_rfl⟩⟩] ξ)
    (f : Ω × ℝ → ℝ) (hfm : Measurable f)
    (hfp : @Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => f (z.1,z.2.val)))
    (hfi : MemLp f 2 (P.prod (volume.restrict (Ioc 0 R))))
    (M : Ω × ℝ → ℝ) (hMm : Measurable M)
    (hMa : ∀ t : Icc (0:ℝ) R,Measurable[F t] (fun w => M (w,t.val)))
    (hMc : ∀ w,ContinuousOn (fun t => M (w,t)) (Icc 0 R))
    (hCE : ∀ t : Icc (0:ℝ) R,(fun w => M (w,t.val)) =ᵐ[P]
      P[(fun w => ξ w+(∫ r in 0..R,f (w,r)))|F t]) :
    ∃ Y : Ω × ℝ → ℝ,
      Y=(fun z => M z-(∫ r in 0..z.2,f (z.1,r))) ∧
      Measurable Y ∧ MemLp Y 2 (P.prod (volume.restrict (Ioc 0 R))) ∧
      (∀ t : Icc (0:ℝ) R,Measurable[F t] (fun w => Y (w,t.val))) ∧
      (∀ᵐ w ∂P,ContinuousOn (fun t => Y (w,t)) (Icc 0 R)) ∧
      ((fun w => Y (w,R)) =ᵐ[P] ξ) ∧
      (∀ t ∈ Icc 0 R,(fun w => Y (w,t)) =ᵐ[P]
        fun w => ξ w+(∫ r in t..R,f (w,r))-(M (w,R)-M (w,t))) := by
  let U := fun w => ξ w+(∫ r in 0..R,f (w,r))
  have hU : MemLp U 2 P := hξ.add (time_primitive_memLp_two P R hR f hfm hfi R ⟨hR,le_rfl⟩)
  have hMp : MemLp M 2 (P.prod (volume.restrict (Ioc 0 R))) := by
    apply conditional_process_sample_time_memLp_two P R hR (fun r => F (projIcc 0 R hR r))
      (fun r hr => hle _) U hU M hMm
    intro t ht
    simpa only [projIcc_of_mem hR ht] using hCE ⟨t,ht⟩
  have hUm : Measurable[F ⟨R,⟨hR,le_rfl⟩⟩] U :=
    hξm.add (progressive_time_primitive_adapted R hR F f hfp ⟨R,⟨hR,le_rfl⟩⟩)
  have hMR : (fun w => M (w,R)) =ᵐ[P] U := by
    have hh := hCE ⟨R,⟨hR,le_rfl⟩⟩
    change (fun w => M (w,R)) =ᵐ[P] P[U|F ⟨R,⟨hR,le_rfl⟩⟩] at hh
    rw [condExp_of_stronglyMeasurable (hle _) hUm.stronglyMeasurable (hU.integrable (by norm_num))] at hh
    exact hh
  let Y := fun z : Ω × ℝ => M z-(∫ r in 0..z.2,f (z.1,r))
  have hYm : Measurable Y := hMm.sub (time_primitive_joint_measurable f hfm)
  have hYL : MemLp Y 2 (P.prod (volume.restrict (Ioc 0 R))) :=
    hMp.sub (time_primitive_sample_time_memLp_two P R hR f hfm hfi)
  have hYadapt t : Measurable[F t] (fun w => Y (w,t.val)) :=
    (hMa t).sub (progressive_time_primitive_adapted R hR F f hfp t)
  obtain ⟨hsec,_⟩ := finite_time_L2_sections P R hR f hfm hfi
  have hpath : ∀ᵐ w ∂P,IntervalIntegrable (fun r => f (w,r)) volume 0 R := by
    filter_upwards [hsec] with w hw
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr (hw.integrable (by norm_num))
  have hpc := progressive_time_primitive_continuous P R hR f hpath
  refine ⟨Y,rfl,hYm,hYL,hYadapt,?_,?_,?_⟩
  · filter_upwards [hpc] with w hw
    exact (hMc w).sub hw
  · filter_upwards [hMR] with w hw
    change M (w,R)-(∫ r in 0..R,f (w,r)) = ξ w
    dsimp [U] at hw
    linarith
  intro t ht
  filter_upwards [hMR,hpath] with w hMw hw
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0) (b := t) (c := R)
    (hw.mono_set (by simpa [uIcc_of_le ht.1,uIcc_of_le hR] using Icc_subset_Icc_right ht.2))
    (hw.mono_set (by simpa [uIcc_of_le ht.2,uIcc_of_le hR] using Icc_subset_Icc_left ht.1))
  change M (w,t)-(∫ r in 0..t,f (w,r)) = _
  dsimp [U] at hMw
  linarith

end Asakura.Chapter5
