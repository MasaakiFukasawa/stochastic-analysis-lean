import Chapter12MalliavinTensorPowers
import Chapter12GaussianArrayNorm

open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem completed_tensor_orthonormal {E F I J : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : I → E) (f : J → F) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f) :
    Orthonormal ℝ (fun ij : I×J => hilbertPureTensor (e ij.1) (f ij.2)) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  rw [hilbert_pure_inner,orthonormal_iff_ite.mp he,orthonormal_iff_ite.mp hf]
  by_cases h1 : a.1=b.1 <;> by_cases h2 : a.2=b.2 <;> simp [h1,h2,Prod.ext_iff]

theorem orthonormal_sum_norm {E I : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : I → E) (he : Orthonormal ℝ e) (a : I → ℝ) :
    ‖∑ i,a i • e i‖=Real.sqrt (∑ i,a i^2) := by
  rw [norm_eq_sqrt_real_inner]
  simpa only [starRingEnd_apply,star_trivial,pow_two] using
    congrArg Real.sqrt (he.inner_sum a a Finset.univ)

/-- An orthonormal coordinate frame in every completed Hilbert tensor
power, with the newest derivative index first. -/
noncomputable def tensorCoordinateFrame (H : RealHilbertSpaceData) {N : ℕ}
    (e : Fin N → H) : (k : ℕ) → (Fin (k+1) → Fin N) → positiveMalliavinTensorPower H k
  | 0,b => e (b 0)
  | k+1,b => hilbertPureTensor (e (b 0)) (tensorCoordinateFrame H e k (Fin.tail b))

theorem tensorCoordinateFrame_orthonormal (H : RealHilbertSpaceData) {N : ℕ}
    (e : Fin N → H) (he : Orthonormal ℝ e) (k : ℕ) :
    Orthonormal ℝ (tensorCoordinateFrame H e k) := by
  classical
  induction k with
  | zero =>
    apply he.comp (fun b : Fin 1 → Fin N => b 0)
    intro a b hab
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    simpa only [hi] using hab
  | succ k ih =>
    have hp := completed_tensor_orthonormal e (tensorCoordinateFrame H e k) he ih
    apply hp.comp (fun b : Fin (k+1+1) → Fin N => (b 0,Fin.tail b))
    intro a b hab
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrArg Prod.fst hab
    · exact congrFun (congrArg Prod.snd hab) j

/-- The component square sum is exactly the completed Hilbert norm,
not a bound carrying the coordinate dimension. -/
theorem tensor_coordinate_sum_norm (H : RealHilbertSpaceData) {N : ℕ}
    (e : Fin N → H) (he : Orthonormal ℝ e) (k : ℕ)
    (a : (Fin (k+1) → Fin N) → ℝ) :
    ‖∑ b,a b • tensorCoordinateFrame H e k b‖=Real.sqrt (∑ b,a b^2) :=
  orthonormal_sum_norm _ (tensorCoordinateFrame_orthonormal H e he k) a

end Asakura.Chapter12
