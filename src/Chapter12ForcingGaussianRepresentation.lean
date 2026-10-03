import Chapter12CylinderAllSobolevOrders

import Chapter12ForcingGaussianJet
import Chapter12GaussianJetCylinder

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem forcing_gaussian_representation {Ω : Type*} {E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (P : Measure Ω)
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (T : ℝ)
    (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS : ContDiff ℝ ∞ S)
    (hSB : ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀q,‖iteratedFDeriv ℝ k S q‖≤C)
    (n : ℕ) (e : Fin n → H) (L : (Fin n → ℝ) →L[ℝ] C(Icc (0:ℝ) T,E))
    (a : C(Icc (0:ℝ) T,E)) (ell : E →L[ℝ] ℝ) (t : Icc (0:ℝ) T)
    (Y : Ω → C(Icc (0:ℝ) T,E))
    (hY : ∀ᵐw ∂P,L (fun j => W (e j) w)=Y w) :
    ∃f : GaussianJet n,(f.f=fun z => ell (S (a+L z) t)) ∧
      (f.toCylinder e).value P W=ᵐ[P] (fun w => ell (S (a+Y w) t)) := by
  obtain ⟨f,hf⟩ := forcing_gaussian_jet T S hS hSB n L a ell t
  refine ⟨f,hf,?_⟩
  filter_upwards [hY] with w hw
  change f.f (fun j => W (e j) w)=_
  rw [hf]
  dsimp only
  rw [hw]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.forcing_gaussian_representation
