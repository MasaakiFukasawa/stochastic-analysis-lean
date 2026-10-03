import Chapter12CylinderMoments

open MeasureTheory ProbabilityTheory Set Filter ENNReal
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The explicit Holder exponents for a product of two variables with all
finite moments. -/
theorem holder_double_exponent (p : ℝ≥0∞) : HolderTriple (2*p) (2*p) p := by
  constructor
  rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by simp)),
    ← add_mul,ENNReal.inv_two_add_inv_two,one_mul]

/-- The right-hand test in the manuscript's closability proof belongs to Lq.
Its integrability is derived from the Gaussian cylinder data. -/
theorem gaussian_ibp_test_memLp {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {m : ℕ} (u : Fin m → H) (g : (Fin m → ℝ) → ℝ)
    (dg : Fin m → (Fin m → ℝ) → ℝ)
    (hg : Measurable g) (hpg : PolyGrowth g)
    (hdg : ∀ j, Measurable (dg j)) (hpdg : ∀ j, PolyGrowth (dg j))
    (h : H) (q : ℝ≥0∞) (hq : q ≠ ∞) :
    MemLp (fun w => g (fun j => W (u j) w)*W h w-
      ⟪∑ j, dg j (fun i => W (u i) w) • u j,h⟫) q P := by
  letI := holder_double_exponent q
  have ht : 2*q ≠ ∞ := ENNReal.mul_ne_top (by simp) hq
  have hG := wiener_cylinder_memLp P W S hS hcore u g hg hpg (2*q) ht
  have hWh := (wiener_gaussian_law_from_dense_core P W S hS hcore h).memLp
    (memLp_id_gaussianReal' (2*q) ht)
  have hDG := wiener_cylinder_derivative_memLp P W S hS hcore u dg hdg hpdg q hq
  have hi := hDG.continuousLinearMap_comp (innerSL ℝ h)
  have hprod : MemLp (fun w => g (fun j => W (u j) w)*W h w) q P := hG.mul hWh
  convert hprod.sub hi using 1
  funext w
  change _-⟪∑ j, dg j (fun i => W (u i) w) • u j,h⟫ =
    _-⟪h,∑ j, dg j (fun i => W (u i) w) • u j⟫
  rw [real_inner_comm]

end Asakura.Chapter12
