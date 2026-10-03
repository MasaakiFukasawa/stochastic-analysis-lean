import FullAuditCylinderCoordinates

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable def cylindricalDirections {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {n m : ℕ} (e : Fin (n+1) → H)
    (A : (Fin (n+1) → ℝ) →L[ℝ] (Fin m → ℝ)) (j : Fin m) : H :=
  ∑ i, (A (Pi.single i 1)) j • e i

/-- The original cylindrical derivative becomes the derivative in the chosen
 orthonormal coordinates. The matrix may be rectangular and singular. -/
theorem cylindrical_derivative_rebasis {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {n m : ℕ} (e : Fin (n+1) → H)
    (A : (Fin (n+1) → ℝ) →L[ℝ] (Fin m → ℝ))
    (D : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ) (z : Fin (n+1) → ℝ) :
    (∑ j, D (A z) (Pi.single j 1) • cylindricalDirections e A j) =
      ∑ i, transformedPartial A D i z • e i := by
  simp only [cylindricalDirections,transformedPartial,Finset.smul_sum,Finset.sum_smul,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

/-- Gaussian integration by parts for two arbitrary finite cylindrical
 representations rewritten in a common finite orthonormal system. Both the
 change of coordinates and its chain rule are derived, including growth. -/
theorem cylindrical_gaussian_ibp_rebased {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) {n m k : ℕ} (e : Fin (n+1) → H) (he : Orthonormal ℝ e)
    (Z : Ω → (Fin (n+1) → ℝ)) (hZ : HasLaw Z (Measure.pi fun _ => gaussianReal 0 1) P)
    (a : Fin (n+1) → ℝ) (Wh : Ω → ℝ) (hWh : Wh =ᵐ[P] fun ω => ∑ i, a i*Z ω i)
    (A : (Fin (n+1) → ℝ) →L[ℝ] (Fin m → ℝ))
    (B : (Fin (n+1) → ℝ) →L[ℝ] (Fin k → ℝ))
    (f : (Fin m → ℝ) → ℝ) (g : (Fin k → ℝ) → ℝ)
    (Df : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ)
    (Dg : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hg : ∀ x, HasFDerivAt g (Dg x) x)
    (hmdf : ∀ j, Measurable (fun x => Df x (Pi.single j 1)))
    (hmdg : ∀ j, Measurable (fun x => Dg x (Pi.single j 1)))
    (hpf : PolyGrowth f) (hpg : PolyGrowth g)
    (hpdf : ∀ j, PolyGrowth (fun x => Df x (Pi.single j 1)))
    (hpdg : ∀ j, PolyGrowth (fun x => Dg x (Pi.single j 1))) :
    (∫ ω, g (B (Z ω))*⟪∑ j, Df (A (Z ω)) (Pi.single j 1) • cylindricalDirections e A j,
      ∑ i, a i • e i⟫ ∂P) =
    ∫ ω, f (A (Z ω))*(g (B (Z ω))*Wh ω-
      ⟪∑ j, Dg (B (Z ω)) (Pi.single j 1) • cylindricalDirections e B j,∑ i, a i • e i⟫) ∂P := by
  simp_rw [cylindrical_derivative_rebasis]
  have hmf : Measurable (fun z => f (A z)) :=
    (continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)).measurable.comp A.continuous.measurable
  have hmg : Measurable (fun z => g (B z)) :=
    (continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)).measurable.comp B.continuous.measurable
  exact cylindrical_gaussian_ibp_written P e he Z hZ a Wh hWh
    (transformed_partial_derivative A f Df hf) (transformed_partial_derivative B g Dg hg)
    hmf hmg (transformed_partial_measurable A Df hmdf) (transformed_partial_measurable B Dg hmdg)
    (hpf.comp_linear A) (hpg.comp_linear B) (transformed_partial_growth A Df hpdf)
    (transformed_partial_growth B Dg hpdg)

end Asakura.FullAudit
