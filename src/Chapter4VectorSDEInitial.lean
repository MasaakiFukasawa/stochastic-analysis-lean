import Chapter4VectorFiniteLift

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000

lemma finite_sde_initial_value
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (ξ : Ω → Fin dim → ℝ)
    (U : Fin dim → Ω × ℝ → ℝ)
    (N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P F (N i j))
    (he : ∀ᵐ w ∂P,∀ r i,Y w r i=ξ w i+(∫ s in 0..r.val,U i (w,s))+∑ j,N i j (realTimeClamp r.val) w) :
    (fun w => Y w (finitePrefixTime (T := T) R hR ⊥))=ᵐ[P] ξ := by
  have hzero : realTimeClamp (T := T) 0=⊥ := by
    apply Subtype.ext
    rw [real_time_clamp_eq 0 le_rfl ((EReal.coe_le_coe hR).trans hRT.le)]
    rfl
  have htime : finitePrefixTime (T := T) R hR ⊥=⟨0,le_rfl,hR⟩ := by
    apply Subtype.ext
    rw [← hzero,finite_prefix_time_of_real R 0 hR ⟨le_rfl,hR⟩ hRT.le]
  have hi : ∀ᵐ w ∂P,∀ i j,N i j ⊥ w=0 :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => (hN i j).initial P F))
  filter_upwards [he,hi] with w hw hz
  funext i
  rw [htime,hw ⟨0,le_rfl,hR⟩ i]
  simp only [intervalIntegral.integral_same,add_zero,hzero,hz,Finset.sum_const_zero]

end Asakura.Chapter4.Vector
