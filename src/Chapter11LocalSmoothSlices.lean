import Chapter11ScalarSlice

open Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter11
open Asakura.Chapter9
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

/-- Local joint smoothness supplies the jointly continuous partial
 derivatives required by C1,2, without extending the function globally. -/
theorem local_smooth_partial_regular (F : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ))
    (hU : IsOpen U) (hF : ∀ z∈U,ContDiffAt ℝ ∞ F z) :
    ContinuousOn (fun z => deriv (fun s => F (s,z.2)) z.1) U ∧
    ContinuousOn (fun z => deriv (fun s => F (z.1,s)) z.2) U ∧
    ContinuousOn (fun z => deriv (deriv (fun s => F (z.1,s))) z.2) U := by
  have hdt z (hz : z∈U) := (scalar_time_slice_derivative F z.1 z.2 (hF z hz)).deriv
  have hdx z (hz : z∈U) := (scalar_space_slice_derivative F z.1 z.2 (hF z hz)).deriv
  have hdxx z (hz : z∈U) : deriv (deriv (fun s => F (z.1,s))) z.2=
      iteratedFDeriv ℝ 2 F z (fun _ => (0,1)) := by
    have hd := second_jet_line F z (0,1) (hF z hz)
    have hh := hd.comp_of_eq z.2 ((hasDerivAt_id z.2).sub_const z.2) (by simp)
    have he : (fun a => iteratedFDeriv ℝ 1 F (z+(a-z.2) • (0,1)) (fun _ => (0,1)))=ᶠ[𝓝 z.2]
        deriv (fun s => F (z.1,s)) := by
      have hp : ContinuousAt (fun a : ℝ => (z.1,a)) z.2 := continuousAt_const.prodMk continuousAt_id
      filter_upwards [hp.tendsto.eventually (hU.mem_nhds hz)] with a ha
      have hpoint : z+(a-z.2) • (0,1)=(z.1,a) := by ext <;> simp <;> ring
      rw [hpoint]
      exact (hdx (z.1,a) ha).symm
    have hh' : HasDerivAt (fun a => iteratedFDeriv ℝ 1 F (z+(a-z.2) • (0,1)) (fun _ => (0,1)))
        (iteratedFDeriv ℝ 2 F z (fun _ => (0,1))) z.2 := by
      simpa only [Function.comp_def,mul_one,id_eq] using hh
    exact (hh'.congr_of_eventuallyEq he.symm).deriv
  have hj (k : ℕ) (e : Fin k → ℝ × ℝ) : ContinuousOn (fun z => iteratedFDeriv ℝ k F z e) U := by
    intro z hz
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) z :=
      ((hF z hz).iteratedFDeriv_right (m:=1) (by simp)).differentiableAt (by norm_num)
    exact (hd.continuousMultilinear_apply_const e).continuousAt.continuousWithinAt
  exact ⟨(hj 1 (fun _ => (1,0))).congr hdt,
    (hj 1 (fun _ => (0,1))).congr hdx,(hj 2 (fun _ => (0,1))).congr hdxx⟩

end Asakura.Chapter11
