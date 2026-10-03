import FullAuditCylinderOriginal
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Full support turns equality of cylindrical random variables into equality
of their smooth coordinate functions, hence of their differentials. -/
theorem gaussian_coordinate_derivative_unique {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {n : ℕ} (Z : Ω → (Fin n → ℝ))
    (hZ : HasLaw Z (Measure.pi fun _ => gaussianReal 0 1) P)
    (f g : (Fin n → ℝ) → ℝ)
    (Df Dg : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
    (hf : ∀ z, HasFDerivAt f (Df z) z)
    (hg : ∀ z, HasFDerivAt g (Dg z) z)
    (heq : (fun ω => f (Z ω)) =ᵐ[P] fun ω => g (Z ω)) : Df = Dg := by
  haveI : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun z => (hf z).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun z => (hg z).continuousAt
  have hfg : f = g := MeasureTheory.Measure.eq_of_ae_eq
    ((hZ.ae_iff (hfc.measurable.eq hgc.measurable)).mp heq) hfc hgc
  subst g
  exact funext fun z => (hf z).unique (hg z)

/-- The finite-coordinate step works for rectangular, singular coordinate
maps: no independence of the originally supplied directions is assumed. -/
theorem rebased_derivative_unique {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : Measure Ω) {n m k : ℕ} (e : Fin (n+1) → H)
    (Z : Ω → (Fin (n+1) → ℝ))
    (hZ : HasLaw Z (Measure.pi fun _ => gaussianReal 0 1) P)
    (A : (Fin (n+1) → ℝ) →L[ℝ] (Fin m → ℝ))
    (B : (Fin (n+1) → ℝ) →L[ℝ] (Fin k → ℝ))
    (f : (Fin m → ℝ) → ℝ) (g : (Fin k → ℝ) → ℝ)
    (Df : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ)
    (Dg : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (hf : ∀ z, HasFDerivAt f (Df z) z)
    (hg : ∀ z, HasFDerivAt g (Dg z) z)
    (heq : (fun ω => f (A (Z ω))) =ᵐ[P] fun ω => g (B (Z ω))) :
    ∀ z, (∑ j, Df (A z) (Pi.single j 1) • cylindricalDirections e A j) =
      ∑ j, Dg (B z) (Pi.single j 1) • cylindricalDirections e B j := by
  have hd := gaussian_coordinate_derivative_unique P Z hZ
    (fun z => f (A z)) (fun z => g (B z))
    (fun z => (Df (A z)).comp A) (fun z => (Dg (B z)).comp B)
    (fun z => (hf (A z)).comp z A.hasFDerivAt)
    (fun z => (hg (B z)).comp z B.hasFDerivAt) heq
  intro z
  rw [cylindrical_derivative_rebasis,cylindrical_derivative_rebasis]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg (fun L => L (Pi.single i 1)) (congrFun hd z)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [finite_differential_coordinates (Df (A z)),
    finite_differential_coordinates (Dg (B z))] at h
  exact congrArg (fun c : ℝ => c • e i) h

theorem cylindrical_derivative_representation_independent {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) (W : H → Ω → ℝ)
    (hlinear : ∀ (l : ℕ) (v : Fin l → H) (c : Fin l → ℝ),
      W (∑ i, c i • v i) =ᵐ[P] fun ω => ∑ i, c i * W (v i) ω)
    (hnormal : ∀ (n : ℕ) (e : Fin (n+1) → H), Orthonormal ℝ e →
      HasLaw (fun ω i => W (e i) ω) (Measure.pi fun _ => gaussianReal 0 1) P)
    {m k : ℕ} (u : Fin m → H) (v : Fin k → H)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin k → ℝ) → ℝ)
    (Df : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ)
    (Dg : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hg : ∀ x, HasFDerivAt g (Dg x) x)
    (heq : (fun ω => f (fun j => W (u j) ω)) =ᵐ[P]
      fun ω => g (fun j => W (v j) ω)) :
    (fun ω => ∑ j, Df (fun j => W (u j) ω) (Pi.single j 1) • u j) =ᵐ[P]
      fun ω => ∑ j, Dg (fun j => W (v j) ω) (Pi.single j 1) • v j := by
  classical
  let dirs : Fin m ⊕ (Fin k ⊕ Unit) → H := Sum.elim u (Sum.elim v (fun _ => (0 : H)))
  obtain ⟨n,e,c,he,hc⟩ := finite_common_orthonormal dirs
  let a := c (Sum.inr (Sum.inr ()))
  let cu := fun j => c (Sum.inl j)
  let cv := fun j => c (Sum.inr (Sum.inl j))
  have hu (j : Fin m) : u j = ∑ i, cu j i • e i := hc (Sum.inl j)
  have hv (j : Fin k) : v j = ∑ i, cv j i • e i := hc (Sum.inr (Sum.inl j))
  have hh : (0 : H) = ∑ i, a i • e i := hc (Sum.inr (Sum.inr ()))
  let Z := fun ω i => W (e i) ω
  let A := cylinderCoordinateMap cu
  let B := cylinderCoordinateMap cv
  have hWh : W (0 : H) =ᵐ[P] fun ω => ∑ i, a i*Z ω i := by
    rw [hh]
    exact hlinear (n+1) e a
  have hWu (j : Fin m) : W (u j) =ᵐ[P] fun ω => A (Z ω) j := by
    rw [hu]
    simpa only [A,cylinder_coordinate_map_apply] using hlinear (n+1) e (cu j)
  have hWv (j : Fin k) : W (v j) =ᵐ[P] fun ω => B (Z ω) j := by
    rw [hv]
    simpa only [B,cylinder_coordinate_map_apply] using hlinear (n+1) e (cv j)
  have hWus : ∀ᵐ ω ∂P, (fun j => W (u j) ω) = A (Z ω) := by
    filter_upwards [ae_all_iff.mpr hWu] with ω hω
    exact funext hω
  have hWvs : ∀ᵐ ω ∂P, (fun j => W (v j) ω) = B (Z ω) := by
    filter_upwards [ae_all_iff.mpr hWv] with ω hω
    exact funext hω
  have hdu (j : Fin m) : cylindricalDirections e A j = u j := by
    rw [cylindrical_directions_from_coordinates]
    exact (hu j).symm
  have hdv (j : Fin k) : cylindricalDirections e B j = v j := by
    rw [cylindrical_directions_from_coordinates]
    exact (hv j).symm
  have heq' : (fun ω => f (A (Z ω))) =ᵐ[P] fun ω => g (B (Z ω)) := by
    filter_upwards [heq,hWus,hWvs] with ω hω huω hvω
    simpa only [huω,hvω] using hω
  have hd := rebased_derivative_unique P e Z (hnormal n e he) A B f g Df Dg hf hg heq'
  simp_rw [hdu,hdv] at hd
  filter_upwards [hWus,hWvs] with ω huω hvω
  rw [huω,hvω]
  exact hd (Z ω)

end Asakura.Chapter12
