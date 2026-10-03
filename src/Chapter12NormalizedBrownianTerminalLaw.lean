import Chapter12OrthogonalWienerLaw

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Normalizing the actual terminal Wiener directions gives independent
standard Gaussian coordinates. -/
theorem normalized_brownian_terminal_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ) (hT : 0<T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P) :
    HasLaw (fun w i => W (brownianTimeDirection (i,⟨T,hT.le,le_rfl⟩)) w/Real.sqrt T)
      (Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) P := by
  let e : Fin (d+1) → FiniteWienerHilbert d T :=
    fun i => (Real.sqrt T)⁻¹ • brownianTimeDirection (i,⟨T,hT.le,le_rfl⟩)
  have he : Orthonormal ℝ e := by
    apply orthonormal_iff_ite.mpr
    intro i j
    simp only [e,inner_smul_left,inner_smul_right,conj_trivial]
    rw [brownian_terminal_direction_inner d T hT.le]
    split_ifs with hij
    · have ht : Real.sqrt T≠0 := (Real.sqrt_pos.mpr hT).ne'
      have hs := Real.sq_sqrt hT.le
      field_simp
      nlinarith
    · simp
  have hh := wiener_orthonormal_law P W hlaw e he
  apply hh.congr
  have ha (i : Fin (d+1)) : (W (e i) : Ω → ℝ) =ᵐ[P]
      (fun w => W (brownianTimeDirection (i,⟨T,hT.le,le_rfl⟩)) w/Real.sqrt T) := by
    dsimp only [e]
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (Real.sqrt T)⁻¹ (W (brownianTimeDirection (i,⟨T,hT.le,le_rfl⟩)))] with w hw
    rw [hw]
    simp [smul_eq_mul,div_eq_mul_inv,mul_comm]
  filter_upwards [ae_all_iff.mpr ha] with w hw
  funext i
  exact (hw i).symm

end Asakura.Chapter12
