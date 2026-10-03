import Chapter12GaussianLp
import Chapter12WienerCylinder

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every polynomially growing cylinder has all finite moments, even when
its original Wiener directions are linearly dependent. -/
theorem wiener_cylinder_memLp {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {m : ℕ} (u : Fin m → H) (f : (Fin m → ℝ) → ℝ)
    (hm : Measurable f) (hf : PolyGrowth f) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun w => f (fun j => W (u j) w)) p P := by
  obtain ⟨n,e,c,he,hc⟩ := finite_common_orthonormal u
  let A := cylinderCoordinateMap c
  let Z := fun w i => W (e i) w
  have hlaw := wiener_orthonormal_law P W (wiener_gaussian_law_from_dense_core P W S hS hcore) e he
  have hi := hlaw.memLp_comp (polynomial_growth_gaussian_memLp
    (hm.comp A.continuous.measurable) (hf.comp_linear A) p hp)
  have hcoord j : (W (u j) : Ω → ℝ) =ᵐ[P] fun w => A (Z w) j := by
    rw [hc j]
    simpa only [A,Z,cylinder_coordinate_map_apply,LinearIsometry.coe_toLinearMap] using wiener_finite_linearity P W.toLinearMap e (c j)
  apply hi.ae_eq
  filter_upwards [ae_all_iff.mpr hcoord] with w hw
  change f (A (Z w)) = f (fun j => W (u j) w)
  congr 1
  exact (funext hw).symm

/-- All moments for the original H-valued cylindrical derivative follow by
finite sums; no bound on D as an operator on Lp is asserted. -/
theorem wiener_cylinder_derivative_memLp {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {m : ℕ} (u : Fin m → H) (df : Fin m → (Fin m → ℝ) → ℝ)
    (hm : ∀ j, Measurable (df j)) (hf : ∀ j, PolyGrowth (df j))
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun w => ∑ j, df j (fun i => W (u i) w) • u j) p P := by
  apply memLp_finsetSum
  intro j _
  exact (wiener_cylinder_memLp P W S hS hcore u (df j) (hm j) (hf j) p hp).continuousLinearMap_comp
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (u j))

end Asakura.Chapter12
