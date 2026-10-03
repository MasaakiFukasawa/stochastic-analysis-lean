import Chapter12TriangularGaussianCoordinates

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

theorem two_wiener_smooth_positive_density {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (h g : H) (a b c : ℝ) (hb : b≠0) (hc : c≠0)
    (hh : inner ℝ h h=b^2) (hg : inner ℝ h g=a*b^2)
    (hgg : inner ℝ g g=a^2*b^2+c^2) :
    ∃ ρ : (Fin 2 → ℝ) → ℝ,ContDiff ℝ ⊤ ρ ∧ (∀ x,0<ρ x) ∧
      HasLaw (fun w => ![W h w,W g w]) (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) P := by
  let e : Fin 2 → H := ![b⁻¹ • h,c⁻¹ • (g-a • h)]
  have he := two_direction_orthonormalization h g a b c hb hc hh hg hgg
  let L := triangularGaussianEquiv a b c hb hc
  obtain ⟨hl,hs,hp⟩ := wiener_affine_smooth_density P W hlaw e he L 0
  refine ⟨affineGaussianDensity L 0,hs,hp,hl.congr ?_⟩
  have heh : (∑ i : Fin 2,(![b,0] : Fin 2 → ℝ) i • e i)=h := by
    simp [Fin.sum_univ_two,e,smul_smul,hb]
  have heg : (∑ i : Fin 2,(![a*b,c] : Fin 2 → ℝ) i • e i)=g := by
    simp only [Fin.sum_univ_two,e,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.head_cons,Matrix.head_fin_const,smul_smul]
    rw [mul_assoc,mul_inv_cancel₀ hb,mul_one,mul_inv_cancel₀ hc,one_smul]
    exact add_sub_cancel _ _
  have h0 := wiener_finite_linearity P W.toLinearMap e (![b,0] : Fin 2 → ℝ)
  have h1 := wiener_finite_linearity P W.toLinearMap e (![a*b,c] : Fin 2 → ℝ)
  rw [heh] at h0
  rw [heg] at h1
  filter_upwards [h0,h1] with w hw0 hw1
  change W h w=∑ i,(![b,0] : Fin 2 → ℝ) i*W (e i) w at hw0
  change W g w=∑ i,(![a*b,c] : Fin 2 → ℝ) i*W (e i) w at hw1
  simp only [zero_add]
  funext i
  fin_cases i
  · change W h w=b*W (e 0) w
    simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.head_cons,Matrix.head_fin_const,zero_mul,add_zero] using hw0
  · change W g w=a*b*W (e 0) w+c*W (e 1) w
    simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.head_cons,Matrix.head_fin_const] using hw1

end Asakura.Chapter12
