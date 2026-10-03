import Chapter12FirstVariationResolvent
import Chapter12HilbertResolventGradient
import Chapter12BrownianResolventKernel
import Chapter12FundamentalTransition

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] forcingGradient

theorem brownian_first_variation_kernel {E:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (b:E → E) (hb:ContDiff ℝ ∞ b)
    (hbound:∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T:ℝ) (hT:0≤T) (S:C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E))
    (hS:ContDiff ℝ ∞ S)
    (heq:∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT s)))
    (a:C(Icc (0:ℝ) T,E)) (d:ℕ) (v:Fin (d+1) → E)
    (K:ℝ≥0) (hK:∀x,‖fderiv ℝ b x‖≤(K:ℝ)) :
    ∃J Q:ℝ → E →L[ℝ] E,Continuous J ∧ Continuous Q ∧
      (∀s∈Icc 0 T,∃e:E ≃L[ℝ] E,e.toContinuousLinearMap=J T*Q s ∧
        ‖e.symm.toContinuousLinearMap‖≤Real.exp ((K:ℝ)*(T-s))) ∧
      ∀(ell:E →L[ℝ] ℝ) (i:Fin (d+1)),
        (brownianCoordinateProjection T i (forcingGradient S a (hilbertKernelForcing (brownianKernelPath d T) v) ell ⟨T,hT,le_rfl⟩):ℝ → ℝ)=ᵐ[
          (volume.restrict (Ioi (0:ℝ))).restrict (Iic T)] (fun s => ell (J T (Q s (v i)))) := by
  let A := fun s => fderiv ℝ b (S a (projIcc 0 T hT s))
  have hcA:Continuous A := (hb.fderiv_right (m:=∞) (by simp)).continuous.comp
    ((S a).continuous.comp continuous_projIcc)
  obtain ⟨J,Q,hcJ,hcQ,hJ0,hQ0,hdJ,hdQ,hJQ⟩ := fundamental_inverse_pair A hcA K (fun s => hK _) T hT
  refine ⟨J,Q,hcJ,hcQ,?_,?_⟩
  · intro s hs
    exact fundamental_transition_inverse_bound A J Q hcJ K (fun r => hK _) T hdJ
      (fun r hr => (hJQ r hr).2) s hs
  intro ell i
  let c := fun j => ell (v j)
  let f := fun j s => ell (J T (Q s (A s (v j))))
  have hfc j:Continuous (f j) := ell.continuous.comp ((J T).continuous.comp
    (hcQ.clm_apply (hcA.clm_apply continuous_const)))
  have hg := hilbert_resolvent_gradient T hT (brownianKernelPath d T) v S a (J T) A Q hcA hcQ ell
    ⟨T,hT,le_rfl⟩ (fun u => first_variation_resolvent b hb hbound T hT S hS heq a
      (hilbertKernelForcing (brownianKernelPath d T) v u) A J Q (fun _ => rfl) hcA hcJ hcQ K
      (fun s => hK _) hdJ (fun s hs => (hJQ s hs).2) ⟨T,hT,le_rfl⟩)
  have hk := brownian_resolvent_kernel T hT c f hfc _ hg i
  have hp:∀ᵐs∂(volume.restrict (Ioi (0:ℝ))).restrict (Iic T),s∈Icc 0 T := by
    filter_upwards [ae_restrict_mem (μ:=volume.restrict (Ioi (0:ℝ))) measurableSet_Iic,
      ae_restrict_of_ae (s:=Iic T) (ae_restrict_mem (μ:=volume) measurableSet_Ioi)] with s hs ht
    exact ⟨ht.le,hs⟩
  filter_upwards [hk,hp] with s hs ht
  rw [hs]
  have he := fundamental_transition_integral A J Q hcA hcQ T hdQ (hJQ T ⟨hT,le_rfl⟩).2 s ht
  let ev:(E →L[ℝ] E) →L[ℝ] ℝ := ell.comp (ContinuousLinearMap.apply ℝ E (v i))
  have hci:Continuous (fun r => (J T).comp ((Q r).comp (A r))) :=
    continuous_const.clm_comp (hcQ.clm_comp hcA)
  have hi := ev.intervalIntegral_comp_comm (hci.intervalIntegrable (μ:=volume) s T)
  have hev := congrArg ev he
  rw [map_add] at hev
  change ell (J T (Q s (v i)))=ell (v i)+ev (∫r in s..T,(J T).comp ((Q r).comp (A r))) at hev
  rw [←hi] at hev
  exact hev.symm
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_first_variation_kernel
