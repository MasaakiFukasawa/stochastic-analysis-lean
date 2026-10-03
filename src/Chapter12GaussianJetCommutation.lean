import Chapter12GaussianJetAlgebra
import Chapter12MixedDerivatives

open MeasureTheory
open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem GaussianJet.partial_second {n : ℕ} (f : GaussianJet n)
    (i j : Fin n) (x : Fin n → ℝ) :
    ((f.partial i).partial j).f x=
      fderiv ℝ (fderiv ℝ f.f) x (Pi.single j 1) (Pi.single i 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f.f) x := ((f.smooth.fderiv_right (by simp : ∞+1≤∞)).differentiable
    (by simp)).differentiableAt
  change (fderiv ℝ (fun y => fderiv ℝ f.f y (Pi.single i 1)) x) (Pi.single j 1)=_
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem GaussianJet.partial_commute {n : ℕ} (f : GaussianJet n)
    (i j : Fin n) (x : Fin n → ℝ) :
    ((f.partial i).partial j).f x=((f.partial j).partial i).f x := by
  rw [f.partial_second,f.partial_second]
  exact second_derivative_symmetric
    (fun z => ((f.smooth.differentiable (by simp)).differentiableAt).hasFDerivAt)
    (((f.smooth.fderiv_right (by simp : ∞+1≤∞)).differentiable (by simp)).differentiableAt.hasFDerivAt)
    _ _

/-- The commutator holds for every smooth Gaussian jet, including all
iterated coordinate derivatives appearing later in the expansion. -/
theorem GaussianJet.divergence_partial {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
    ((GaussianJet.divergence u).partial i).f x=
      (u i).f x+(GaussianJet.divergence (fun j => (u j).partial i)).f x := by
  let z := i.removeNth x
  let y := x i
  have hex : i.insertNth y z=x := by simpa [y,z] using Fin.insertNth_removeNth i (x i) x
  have hh := finite_divergence_commutation (fun j => (u j).f)
    (fun i j => ((u j).partial i).f)
    (fun i j k => (((u k).partial j).partial i).f)
    (fun i j => (u j).coordinate_derivative i)
    (fun i j k => ((u k).partial j).coordinate_derivative i)
    (fun i j k x => (u k).partial_commute j i x) i z y
  have hefun : gaussianDivergence (fun j => (u j).f) (fun i j => ((u j).partial i).f)=
      (GaussianJet.divergence u).f := by
    funext z
    simp [gaussianDivergence]
  rw [hefun,hex] at hh
  have hu := (GaussianJet.divergence u).coordinate_derivative i z y
  rw [hex] at hu
  have h := hu.unique hh
  simpa only [GaussianJet.divergence_apply] using h

end Asakura.Chapter12
