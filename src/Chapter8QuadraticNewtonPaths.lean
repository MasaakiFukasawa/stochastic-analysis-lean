import Chapter8AnisotropicNewtonCoordinates
import Chapter8QuadraticDirections
import Chapter8NewtonSpectral

open Set
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter8
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Diagonalize the actual positive force matrix and combine the scalar
energy estimates. Every strictly positive friction is allowed. -/
theorem quadratic_newton_path_contraction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (K : E →L[ℝ] E) (hs : K.toLinearMap.IsSymmetric)
    (hK : ∀ z≠0,0<⟪z,K z⟫) (δ : ℝ) (hδ : 0<δ) :
    ∃ (A : (E × E) ≃L[ℝ] WithLp 2
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
      (r : ℝ),0<r ∧ ∀ (q v : ℝ → E) (T : ℝ),0≤T →
      ContinuousOn q (Icc 0 T) → ContinuousOn v (Icc 0 T) →
      (∀ t∈Ioo 0 T,HasDerivAt q (v t) t) →
      (∀ t∈Ioo 0 T,HasDerivAt v (-K (q t)-δ • v t) t) →
      ∀ t∈Icc 0 T,‖A (q t,v t)‖≤Real.exp (-r*t)*‖A (q 0,v 0)‖ := by
  let B := hs.eigenvectorBasis rfl
  let ev := hs.eigenvalues rfl
  have he i : K (B i)=ev i • B i := hs.apply_eigenvectorBasis rfl i
  have hp i : 0<ev i := by
    have hh := hK (B i) (B.orthonormal.ne_zero i)
    rw [he,inner_smul_right,real_inner_self_eq_norm_sq,B.orthonormal.norm_eq_one] at hh
    simpa using hh
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  obtain ⟨b,r,hr,hb,hpath⟩ := quadratic_direction_contraction ev hp δ hδ
  let c := fun i => Real.sqrt (b i+δ^2/4)
  let C := diagonalEuclideanEquiv c (fun i => (Real.sqrt_pos.mpr (hb i)).ne')
  let R := B.repr.toContinuousLinearEquiv.prodCongr B.repr.toContinuousLinearEquiv
  let A := R.trans (anisotropicNewtonEquiv C δ)
  have hcoord i x : ⟪B i,K x⟫=ev i*⟪B i,x⟫ := by
    have hh : ⟪K (B i),x⟫=⟪B i,K x⟫ := hs (B i) x
    rw [←hh,he,real_inner_smul_left]
  have hnorm (q v : E) : ‖A (q,v)‖^2=∑ i,newtonEnergy δ (b i) ⟪B i,q⟫ ⟪B i,v⟫ := by
    have hh := anisotropic_newton_energy b δ hb (B.repr q,B.repr v)
    simpa [A, R, C, c, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply, B.repr_apply_apply] using hh
  refine ⟨A,r,hr,?_⟩
  intro q v T hT hq hv hdq hdv t ht
  have hdq' i s (hs : s∈Ioo 0 T) : HasDerivAt (fun u => ⟪B i,q u⟫) ⟪B i,v s⟫ s :=
    (innerSL ℝ (B i)).hasFDerivAt.comp_hasDerivAt s (hdq s hs)
  have hdv' i s (hs : s∈Ioo 0 T) : HasDerivAt (fun u => ⟪B i,v u⟫)
      (-ev i*⟪B i,q s⟫-δ*⟪B i,v s⟫) s := by
    have hh := (innerSL ℝ (B i)).hasFDerivAt.comp_hasDerivAt s (hdv s hs)
    simpa only [Function.comp_def,innerSL_apply_apply,inner_sub_right,inner_neg_right,inner_smul_right,hcoord,neg_mul] using hh
  have hh := hpath (fun i s => ⟪B i,q s⟫) (fun i s => ⟪B i,v s⟫) T hT
    (fun i => continuousOn_const.inner hq) (fun i => continuousOn_const.inner hv) hdq' hdv' t ht
  rw [←hnorm,←hnorm] at hh
  have he : Real.exp (-2*r*t)=Real.exp (-r*t)^2 := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  rw [he,←mul_pow] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hh

end Asakura.Chapter8
