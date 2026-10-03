import Chapter12DivergenceDuality
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open Set Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Testing against a dense family of adapted step integrands identifies
the representing integrand with the orthogonal projection of DF. -/
theorem clark_integrand_projection
    (A : Submodule ℝ H) [A.HasOrthogonalProjection]
    (S : Set A) (hS : Dense S) (u : H) (ψ : A)
    (htest : ∀ v ∈ S, ⟪u,(v : H)⟫ = ⟪(ψ : H),(v : H)⟫) :
    (ψ : H) = A.starProjection u := by
  have h : ∀ v : A, ⟪u,(v : H)⟫ = ⟪(ψ : H),(v : H)⟫ :=
    hS.induction htest (isClosed_eq (by fun_prop) (by fun_prop))
  symm
  apply A.eq_starProjection_of_mem_of_inner_eq_zero ψ.property
  intro v hv
  rw [inner_sub_left,h ⟨v,hv⟩,sub_self]

/-- Once the representing integrand has been identified by the preceding
test argument, substitution gives the Clark--Ocone representation. -/
theorem clark_representation_from_tests
    (A : Submodule ℝ H) [A.HasOrthogonalProjection]
    (I : A →ₗᵢ[ℝ] E) (S : Set A) (hS : Dense S)
    (F c : E) (u : H) (ψ : A) (hrep : F = c+I ψ)
    (htest : ∀ v ∈ S, ⟪u,(v : H)⟫ = ⟪(ψ : H),(v : H)⟫) :
    F = c+I (A.orthogonalProjectionOnto u) := by
  have hψ : ψ = A.orthogonalProjectionOnto u :=
    Subtype.ext (clark_integrand_projection A S hS u ψ htest)
  simpa only [hψ] using hrep

/-- The equality of divergence and Ito integration on adapted L2 integrands
uses the just-established representation and the Ito isometry. -/
theorem divergence_equals_ito_on_adapted
    (D : E →ₗ.[ℝ] H) (A : Submodule ℝ H) [A.HasOrthogonalProjection]
    (I : A →ₗᵢ[ℝ] E) (mean : E → E)
    (hrep : ∀ f : D.domain, (f : E) = mean f + I (A.orthogonalProjectionOnto (D f)))
    (hmean : ∀ f : D.domain, ∀ v : A, ⟪mean f,I v⟫ = 0)
    (v : A) : IsDivergence D (v : H) (I v) := by
  intro f
  have hproj : ⟪D f,(v : H)⟫ = ⟪(A.orthogonalProjectionOnto (D f) : H),(v : H)⟫ := by
    have h := A.starProjection_inner_eq_zero (D f) v v.property
    rw [inner_sub_left] at h
    exact sub_eq_zero.mp h
  calc
    ⟪D f,(v : H)⟫ = ⟪(A.orthogonalProjectionOnto (D f) : H),(v : H)⟫ := hproj
    _ = ⟪I (A.orthogonalProjectionOnto (D f)),I v⟫ := (I.inner_map_map _ _).symm
    _ = ⟪(f : E),I v⟫ := by
      conv_rhs => rw [hrep f]
      rw [inner_add_left,hmean,zero_add]

end Asakura.Chapter12
