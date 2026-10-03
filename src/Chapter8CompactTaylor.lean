import Chapter8FlowTaylorBound
import Mathlib.Topology.UniformSpace.HeineCantor

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Uniform first-order Taylor remainder on a compact set. Continuity of
the derivative suffices; a Lipschitz derivative is not required. -/
theorem compact_taylor_remainder {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (D : E → E →L[ℝ] F)
    (hD : ∀ x,HasFDerivAt f (D x) x) (hcD : Continuous D)
    (S : Set E) (hS : IsCompact S) (ε : ℝ) (hε : 0<ε) :
    ∃ δ>0,∀ y∈S,∀ h,‖h‖<δ → ‖f (y+h)-f y-D y h‖ ≤ ε*‖h‖ := by
  have hu := hS.uniformContinuousAt_of_continuousAt D (fun _ _ => hcD.continuousAt)
    (Metric.dist_mem_uniformity hε)
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_uniformity_dist.mp hu
  refine ⟨δ,hδ,?_⟩
  intro y hy h hh
  have hp : Continuous (fun s : ℝ => y+s • h) := by fun_prop
  have hc : Continuous (fun s : ℝ => (D (y+s • h)-D y) h) :=
    ((hcD.comp hp).sub continuous_const).clm_apply continuous_const
  have he : (∫ s in (0:ℝ)..1,(D (y+s • h)-D y) h)=f (y+h)-f y-D y h := by
    simp_rw [ContinuousLinearMap.sub_apply]
    rw [intervalIntegral.integral_sub
      (f := fun s => D (y+s • h) h) (g := fun _ => D y h)
      (((hcD.comp hp).clm_apply continuous_const).intervalIntegrable 0 1)
      intervalIntegrable_const,intervalIntegral.integral_const]
    have hder s : HasDerivAt (fun s : ℝ => f (y+s • h)) (D (y+s • h) h) s := by
      apply (hD _).comp_hasDerivAt s
      simpa using (((hasDerivAt_id s).smul_const h).const_add y)
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder s)
      (((hcD.comp hp).clm_apply continuous_const).intervalIntegrable 0 1)
    simpa using congrArg (fun z => z-D y h) heq
  rw [← he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun s => (D (y+s • h)-D y) h) (C := ε*‖h‖) (by
      intro s hs
      have hs' : s∈Ioc (0:ℝ) 1 := by simpa using hs
      have hh' : dist y (y+s • h)<δ := by
        rw [dist_comm,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hs'.1]
        exact (mul_le_of_le_one_left (norm_nonneg _) hs'.2).trans_lt hh
      have hd' : ‖D (y+s • h)-D y‖ ≤ ε := by
        have hh := hd hh' hy
        change dist (D y) (D (y+s • h))<ε at hh
        have hh2 := hh.le
        simpa only [dist_comm (D y),dist_eq_norm] using hh2
      exact ((D (y+s • h)-D y).le_opNorm h).trans
        (mul_le_mul_of_nonneg_right hd' (norm_nonneg _)))
  simpa using hb

end Asakura.Chapter8
