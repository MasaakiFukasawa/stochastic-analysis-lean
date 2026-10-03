import Chapter9DirectionalJets
import Chapter9AdjointProduct

open Set
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

theorem spatial_slice_smooth {d : ℕ} (F : ℝ × (Fin d → ℝ) → ℝ) (t : ℝ)
    (hF : ∀ x,ContDiffAt ℝ ∞ F (t,x)) : ContDiff ℝ ∞ (fun x => F (t,x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (hF x).comp x (contDiffAt_const.prodMk contDiffAt_id)

theorem spatial_slice_first_jet {d : ℕ} (F : ℝ × (Fin d → ℝ) → ℝ) (t : ℝ)
    (x h : Fin d → ℝ) (hF : ContDiffAt ℝ ∞ F (t,x)) :
    iteratedFDeriv ℝ 1 F (t,x) (fun _ => (0,h))=
      directional (fun y => F (t,y)) h x := by
  have hs : ContDiffAt ℝ ∞ (fun y => F (t,y)) x :=
    hF.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hd := first_jet_line F (t,x) (0,h) hF
  have he := first_jet_line (fun y => F (t,y)) x h hs
  have hh : (fun r : ℝ => F ((t,x)+r • (0,h)))=(fun r => F (t,x+r • h)) := by
    funext r
    simp
  rw [hh] at hd
  simpa only [iteratedFDeriv_one_apply,directional] using hd.unique he

theorem spatial_slice_second_jet {d : ℕ} (F : ℝ × (Fin d → ℝ) → ℝ) (t : ℝ)
    (x h : Fin d → ℝ) (hF : ∀ y,ContDiffAt ℝ ∞ F (t,y)) :
    iteratedFDeriv ℝ 2 F (t,x) (fun _ => (0,h))=
      directional (directional (fun y => F (t,y)) h) h x := by
  have hs := spatial_slice_smooth F t hF
  have hd := second_jet_line F (t,x) (0,h) (hF x)
  have he := first_jet_line (directional (fun y => F (t,y)) h) x h
    (directional_smooth _ hs h).contDiffAt
  have hh (r : ℝ) : (t,x)+r • (0,h)=(t,x+r • h) := by simp
  simp_rw [hh,spatial_slice_first_jet F t _ h (hF _)] at hd
  simpa only [iteratedFDeriv_one_apply,directional] using hd.unique he

theorem time_slice_derivative {d : ℕ} (F : ℝ × (Fin d → ℝ) → ℝ) (t : ℝ)
    (x : Fin d → ℝ) (hF : ContDiffAt ℝ ∞ F (t,x)) :
    HasDerivAt (fun s => F (s,x)) (iteratedFDeriv ℝ 1 F (t,x) (fun _ => (1,0))) t := by
  have h := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  simpa only [Function.comp_def,iteratedFDeriv_one_apply] using! h
end Asakura.Chapter9
