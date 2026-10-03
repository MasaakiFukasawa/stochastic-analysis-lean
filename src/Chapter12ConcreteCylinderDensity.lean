import Chapter12ConcreteCylinderOperator
import Chapter12CylinderDenseSet
import Mathlib.Analysis.Calculus.FDeriv.Const

open MeasureTheory ProbabilityTheory Set Filter ENNReal
open scoped Topology RealInnerProductSpace ContDiff
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Compactly supported continuous functions have polynomial growth of
order zero, as do the derivatives of a smooth compactly supported function. -/
theorem compact_support_polynomial_growth {E : Type*} [NormedAddCommGroup E]
    (f : E → ℝ) (hf : Continuous f) (hs : HasCompactSupport f) : PolyGrowth f := by
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hf
  refine ⟨max C 0,le_max_right _ _,0,fun x => ?_⟩
  simpa only [pow_zero,mul_one,Real.norm_eq_abs] using (hC x).trans (le_max_left C 0)

noncomputable def compactSmoothCylinder {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (u : Fin n → H)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    SmoothCylinder H where
  dim := n
  direction := u
  f := f
  df := fderiv ℝ f
  smooth := hf
  derivative := fun x => (hf.differentiable (by simp) x).hasFDerivAt
  growth := compact_support_polynomial_growth f hf.continuous hs
  derivative_measurable := fun j =>
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.measurable
  derivative_growth := fun j => compact_support_polynomial_growth _
    (((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous)
    (hs.fderiv_apply ℝ (Pi.single j 1))
  all_derivatives_growth := by
    intro k
    obtain ⟨C,hC,hb⟩ := hs.exists_bound_iteratedFDeriv hf k
    exact ⟨C,hC,0,fun x => by simpa using hb k le_rfl x⟩

/-- Actual continuous process coordinates supply the dense range of the
concrete smooth cylinder values. Equality with Wiener integrals is needed
only almost everywhere at each coordinate. -/
theorem concrete_cylinder_dense {Ω H K : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    [TopologicalSpace K] [FirstCountableTopology K]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ)
      (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : K → Ω → ℝ) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ w, Continuous (fun t => X t w))
    (direction : K → H) (hXW : ∀ t, X t =ᵐ[P] (W (direction t) : Ω → ℝ))
    (times : ℕ → K) (htimes : DenseRange times)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hgen : ∀ f : Lp ℝ p P,
      AEStronglyMeasurable[MeasurableSpace.comap (fun w t => X t w) inferInstance] f P) :
    DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore p hp) := by
  apply cylinder_class_dense P X hXm hXc times htimes p hp hgen
  intro n g hgc hgd hi
  let c := compactSmoothCylinder (fun i : Fin n => direction (times i)) g hgd hgc
  refine ⟨c,?_⟩
  apply Lp.ext
  filter_upwards [(c.value_memLp P W S hS hcore p hp).coeFn_toLp,hi.coeFn_toLp,
    ae_all_iff.mpr (fun i : Fin n => hXW (times i))] with w hw hg hcoord
  change (c.value_memLp P W S hS hcore p hp).toLp _ w = hi.toLp _ w
  rw [hw,hg]
  dsimp only [SmoothCylinder.value,c,compactSmoothCylinder]
  congr 1
  exact (funext hcoord).symm

end Asakura.Chapter12
