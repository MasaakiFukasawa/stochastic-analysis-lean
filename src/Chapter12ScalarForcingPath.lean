import Chapter12ForcingGaussianJet
import Chapter12ScalarPathDerivatives

open Set
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable def scalarForcingPath {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E))
    (a : C(Icc (0:ℝ) T,E)) {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] C(Icc (0:ℝ) T,E))
    (ell : E →L[ℝ] ℝ) (z : Fin N → ℝ) : C(Icc (0:ℝ) T,ℝ) :=
  ell.compLeftContinuous ℝ _ (S (a+L z))

theorem scalarForcingPath_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS : ContDiff ℝ ∞ S)
    (a : C(Icc (0:ℝ) T,E)) {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] C(Icc (0:ℝ) T,E))
    (ell : E →L[ℝ] ℝ) : ContDiff ℝ ∞ (scalarForcingPath T S a L ell) := by
  unfold scalarForcingPath
  exact (ell.compLeftContinuous ℝ (Icc (0:ℝ) T)).contDiff.comp
    (hS.comp (contDiff_const.add L.contDiff))

theorem scalarForcingPath_jets {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS : ContDiff ℝ ∞ S)
    (hSB : ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀a,‖iteratedFDeriv ℝ k S a‖≤C)
    (a : C(Icc (0:ℝ) T,E)) {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] C(Icc (0:ℝ) T,E))
    (ell : E →L[ℝ] ℝ) (t : Icc (0:ℝ) T) :
    ∃f : GaussianJet N,f.f=fun z => scalarForcingPath T S a L ell z t :=
  forcing_gaussian_jet T S hS hSB N L a ell t
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalarForcingPath_jets
