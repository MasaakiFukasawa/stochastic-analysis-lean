import Chapter12FirstVolterraVariation
import Chapter12ContinuousForcingResolvent

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem first_variation_resolvent {E:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b:E → E) (hb:ContDiff ℝ ∞ b)
    (hbound:∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T:ℝ) (hT:0≤T) (S:C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E))
    (hS:ContDiff ℝ ∞ S)
    (heq:∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT s)))
    (a h:C(Icc (0:ℝ) T,E))
    (A J Q:ℝ → E →L[ℝ] E)
    (hA:∀s,A s=fderiv ℝ b (S a (projIcc 0 T hT s)))
    (hcA:Continuous A) (hcJ:Continuous J) (hcQ:Continuous Q)
    (K:ℝ≥0) (hAK:∀s,‖A s‖≤(K:ℝ))
    (hdJ:∀t∈Icc 0 T,HasDerivAt J (A t*J t) t)
    (hJQ:∀t∈Icc 0 T,J t*Q t=1) (t:Icc (0:ℝ) T) :
    (fderiv ℝ S a h) t=h t+J t (∫s in 0..t.val,Q s (A s (h (projIcc 0 T hT s)))) := by
  let R := fun s => h (projIcc 0 T hT s)
  let X := fun s => (fderiv ℝ S a h) (projIcc 0 T hT s)
  let Y := fun t => R t+J t (∫s in 0..t,Q s (A s (R s)))
  have hcR:Continuous R := h.continuous.comp continuous_projIcc
  have hcX:Continuous X := (fderiv ℝ S a h).continuous.comp continuous_projIcc
  have hcY:Continuous Y := hcR.add (hcJ.clm_apply
    (intervalIntegral.differentiable_integral_of_continuous (hcQ.clm_apply (hcA.clm_apply hcR))).continuous)
  have hp s (hs:s∈Icc 0 T):projIcc 0 T hT s=⟨s,hs⟩ := Subtype.ext (by simp [projIcc,hs.1,hs.2])
  have hX s (hs:s∈Icc 0 T):X s=0+(∫r in 0..s,A r (X r))+R s := by
    have hh := first_volterra_variation b hb hbound T hT S hS heq a h ⟨s,hs⟩
    simp only [X,R,hp s hs,zero_add]
    simp_rw [hA]
    exact hh.trans (add_comm _ _)
  have hY s (hs:s∈Icc 0 T):Y s=0+(∫r in 0..s,A r (Y r))+R s := by
    simpa only [zero_add] using (continuous_forcing_resolvent_solves A J Q hcA hcJ hcQ T hT hdJ hJQ R hcR s hs).trans (add_comm _ _)
  have hLip s:LipschitzWith K (A s) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hAK s) (norm_nonneg _))
  have hu := Asakura.Chapter10.time_dependent_solution_causal (fun s z => A s z) K
    ((hcA.comp continuous_fst).clm_apply continuous_snd) hLip X Y R R hcX hcY 0 T hT
    (fun _ _ => rfl) hX hY t.val t.property
  simpa only [X,Y,R,hp t.val t.property] using hu
end Asakura.Chapter12
#print axioms Asakura.Chapter12.first_variation_resolvent
