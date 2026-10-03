import FullAuditGaussianDirectionalIBP
import Mathlib.Analysis.InnerProductSpace.Orthonormal

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
namespace Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false

/-- Expand the H-valued cylindrical derivative in a finite orthonormal system. -/
theorem cylindrical_inner_direction {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (e : Fin (n+1) → H) (he : Orthonormal ℝ e) (a c : Fin (n+1) → ℝ) :
    ⟪∑ i, c i • e i, ∑ i, a i • e i⟫ = ∑ i, a i*c i := by
  simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,conj_trivial]
  simp_rw [orthonormal_iff_ite.mp he]
  simp [mul_comm]

/-- The manuscript's Gaussian IBP in its finite orthonormal cylindrical
 representation. The joint standard-normal law and the deterministic Wiener
 integral's linearity are prior Gaussian/Ito facts. Arbitrary initial
 cylindrical representations still require their chain-rule basis change. -/
theorem cylindrical_gaussian_ibp_written {Ω H : Type*} {m : MeasurableSpace Ω}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) {n : ℕ}
    (e : Fin (n+1) → H) (he : Orthonormal ℝ e)
    (Z : Ω → (Fin (n+1) → ℝ)) (hZ : HasLaw Z (Measure.pi fun _ => gaussianReal 0 1) P)
    (a : Fin (n+1) → ℝ) (Wh : Ω → ℝ) (hWh : Wh =ᵐ[P] fun ω => ∑ i, a i*Z ω i)
    {f g : (Fin (n+1) → ℝ) → ℝ} {df dg : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    (hf : ∀ i z y, HasDerivAt (fun x => f (i.insertNth x z)) (df i (i.insertNth y z)) y)
    (hg : ∀ i z y, HasDerivAt (fun x => g (i.insertNth x z)) (dg i (i.insertNth y z)) y)
    (hmf : Measurable f) (hmg : Measurable g)
    (hmdf : ∀ i, Measurable (df i)) (hmdg : ∀ i, Measurable (dg i))
    (hpf : PolyGrowth f) (hpg : PolyGrowth g)
    (hpdf : ∀ i, PolyGrowth (df i)) (hpdg : ∀ i, PolyGrowth (dg i)) :
    (∫ ω, g (Z ω)*⟪∑ i, df i (Z ω) • e i, ∑ i, a i • e i⟫ ∂P) =
      ∫ ω, f (Z ω)*(g (Z ω)*Wh ω-⟪∑ i, dg i (Z ω) • e i,∑ i, a i • e i⟫) ∂P := by
  simp_rw [cylindrical_inner_direction e he]
  have hr : (fun ω => f (Z ω)*(g (Z ω)*Wh ω-∑ i, a i*dg i (Z ω))) =ᵐ[P]
      (fun ω => f (Z ω)*((∑ i, a i*Z ω i)*g (Z ω)-∑ i, a i*dg i (Z ω))) := by
    filter_upwards [hWh] with ω hω
    rw [hω,mul_comm (g (Z ω))]
  rw [integral_congr_ae hr]
  have hlm : Measurable (fun z => g z*(∑ i, a i*df i z)) :=
    hmg.mul (Finset.measurable_sum _ fun i _ => (hmdf i).const_mul _)
  have hrm : Measurable (fun z => f z*((∑ i, a i*z i)*g z-∑ i, a i*dg i z)) :=
    hmf.mul (((Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _).mul hmg).sub
      (Finset.measurable_sum _ fun i _ => (hmdg i).const_mul _))
  have hlaw := hZ.integral_comp hlm.aestronglyMeasurable
  have hraw := hZ.integral_comp hrm.aestronglyMeasurable
  simp only [Function.comp_def] at hlaw hraw
  rw [hlaw,hraw]
  exact gaussian_directional_ibp_polynomial hf hg hmf hmg hmdf hmdg hpf hpg hpdf hpdg a

end Asakura.FullAudit
