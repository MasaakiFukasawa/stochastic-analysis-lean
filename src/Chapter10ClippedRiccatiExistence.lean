import Chapter10RiccatiLipschitz
import Chapter8ForcedIntegralExistence

open Set Filter Matrix
open scoped Topology NNReal Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Construct the auxiliary truncated Riccati solution on any finite horizon
by the proved contraction argument. Coefficients are only assumed continuous. -/
theorem clipped_riccati_exists {d : ℕ}
    (A H Q : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (hA : Continuous A) (hH : Continuous H) (hQ : Continuous Q)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (R : ℝ≥0) (T : ℝ) (hT : 0≤T) :
    ∃ S : ℝ → Matrix (Fin d) (Fin d) ℝ,Continuous S ∧ S 0=S₀ ∧
      (∀ t∈Icc 0 T,S t=S₀+∫ s in 0..t,
        A s*matrixClip R (S s)+matrixClip R (S s)*(A s).transpose+Q s-matrixClip R (S s)*H s*matrixClip R (S s)) ∧
      ∀ t∈Ico 0 T,HasDerivWithinAt S
        (A t*matrixClip R (S t)+matrixClip R (S t)*(A t).transpose+Q t-matrixClip R (S t)*H t*matrixClip R (S t)) (Ici t) t := by
  obtain ⟨a,ha⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨h,hh⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hH.continuousOn
  let p := fun t => (projIcc 0 T hT t).val
  have hpc : Continuous p := continuous_subtype_val.comp continuous_projIcc
  let L : ℝ≥0 := ⟨2*(d:ℝ)*max a 0+2*(d:ℝ)^2*max h 0*R,by positivity⟩
  let b := fun t S => A (p t)*matrixClip R S+matrixClip R S*(A (p t)).transpose+
    Q (p t)-matrixClip R S*H (p t)*matrixClip R S
  have hclip : Continuous (matrixClip (d := d) R) := (matrixClip_lipschitz R).continuous
  have hbc : Continuous (Function.uncurry b) := by
    dsimp [b,Function.uncurry]
    fun_prop
  have hbl t : LipschitzWith L (b t) := by
    apply (clipped_riccati_lipschitz (A (p t)) (H (p t)) (Q (p t)) R).weaken
    change 2*(d:ℝ)*‖A (p t)‖+2*(d:ℝ)^2*‖H (p t)‖*R≤_
    dsimp only [L]
    gcongr
    · exact (ha _ (projIcc 0 T hT t).property).trans (le_max_left _ _)
    · exact (hh _ (projIcc 0 T hT t).property).trans (le_max_left _ _)
  obtain ⟨S,hSc,hSe⟩ := forced_integral_equation_exists T hT L b hbc hbl (fun _ => S₀) continuous_const
  have he t (ht : t∈Icc 0 T) : S t=S₀+∫ s in 0..t,
      A s*matrixClip R (S s)+matrixClip R (S s)*(A s).transpose+Q s-matrixClip R (S s)*H s*matrixClip R (S s) := by
    rw [hSe t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hp : p s=s := by simp [p,projIcc,hs.1,hs.2.trans ht.2]
    simp only [b,hp]
  refine ⟨S,hSc,?_,he,?_⟩
  · simpa using he 0 ⟨le_rfl,hT⟩
  · intro t ht
    have hc : Continuous (fun s => A s*matrixClip R (S s)+matrixClip R (S s)*(A s).transpose+
        Q s-matrixClip R (S s)*H s*matrixClip R (S s)) := by fun_prop
    have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add S₀
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · have hlt : ∀ᶠ s in 𝓝[Ici t] t,s<T := (eventually_lt_nhds ht.2).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin,hlt] with s hs hsT
      exact he s ⟨ht.1.trans hs,hsT.le⟩
    · exact (show t∈Ici t from le_refl t)

end Asakura.Chapter10
