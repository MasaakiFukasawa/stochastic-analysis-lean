import Chapter12BasketMatrixHedge
import Chapter12BrownianEnergyIntegrals
open MeasureTheory Set Matrix
open scoped BigOperators
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem matrix_energy_allocation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det≠0)
    (φ : Fin d → progressiveEnergyIntegrands B.F canonicalClock (P.prod (volume.restrict (Ioi (0:ℝ))))) :
    ∃ ψ : Fin d → progressiveEnergyIntegrands B.F canonicalClock (P.prod (volume.restrict (Ioi (0:ℝ)))),
      (∀ i z,(ψ i).val z=∑ j,(A.transpose)⁻¹ i j*(φ j).val z) ∧
      ∀ j z,(∑ i,A i j*(ψ i).val z)=(φ j).val z := by
  let ψ i := ∑ j,(A.transpose)⁻¹ i j • φ j
  have he i z : (ψ i).val z=∑ j,(A.transpose)⁻¹ i j*(φ j).val z := by
    simp [ψ,Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  refine ⟨ψ,he,?_⟩
  intro j z
  have hd : IsUnit A.transpose.det := isUnit_iff_ne_zero.mpr (by simpa only [Matrix.det_transpose] using hA)
  have hh : A.transpose.mulVec ((A.transpose)⁻¹.mulVec (fun i => (φ i).val z))=(fun i => (φ i).val z) := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hd,Matrix.one_mulVec]
  simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,he] using congrFun hh j
end Asakura.Chapter12
#print axioms Asakura.Chapter12.matrix_energy_allocation
