import Chapter8CosinePotentialCoordinates
import Chapter8PotentialDriftRegularity

open scoped BigOperators NNReal
namespace Asakura.Chapter8
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2400000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency true

noncomputable local instance scalarTriNormed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
noncomputable local instance scalarTriSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The nonlinear Newton example has globally bounded second and third
Frechet derivatives, as required by the invariant-law theorem. -/
theorem cosine_potential_bounded_derivatives (d : ℕ) (k c : ℝ) :
    ∃ A₂ A₃ : ℝ≥0,
      (∀ x,‖fderiv ℝ (fderiv ℝ (cosinePotential d k c)) x‖≤(A₂:ℝ)) ∧
      (∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (cosinePotential d k c))) x‖≤(A₃:ℝ)) := by
  let E := Fin d → ℝ
  let a := fun i : Fin d => (ContinuousLinearMap.proj i : E →L[ℝ] ℝ)
  let B := fun i => (a i).smulRight (a i)
  let C := fun i => (a i).smulRight (B i)
  have h1 : fderiv ℝ (cosinePotential d k c)=fun x => ∑ i,(k*x i+c*Real.sin (x i)) • a i := by
    funext x
    apply ContinuousLinearMap.ext
    intro z
    have hz : z=∑ i,z i • (Pi.single i 1 : E) := by
      ext j
      simp [Pi.single_apply]
    rw [hz,map_sum]
    simp only [map_smul,cosine_potential_coordinate_derivative d k c |>.2]
    simp [a,Pi.single_apply,Finset.sum_mul,Finset.mul_sum]
  have hD x : HasFDerivAt (fun y : E => ∑ i,(k*y i+c*Real.sin (y i)) • a i)
      (∑ i,(k+c*Real.cos (x i)) • B i) x := by
    have hi (i : Fin d) : HasFDerivAt (fun y : E => (k*y i+c*Real.sin (y i)) • a i)
        ((k+c*Real.cos (x i)) • B i) x := by
      have hscalar : HasFDerivAt (fun y : E => k*y i+c*Real.sin (y i))
          ((k+c*Real.cos (x i)) • a i) x := by
        convert (a i).hasFDerivAt.comp x (cosine_gradient_derivative d k c x) using 1
        all_goals ext z; simp [a]
      convert hscalar.smul_const (a i) using 1
      ext z j
      simp [B,ContinuousLinearMap.smulRight_apply,mul_assoc]
    convert HasFDerivAt.sum (u := Finset.univ) (fun i _ => hi i) using 1
    ext y
    simp only [Finset.sum_apply]
  have h2 : fderiv ℝ (fderiv ℝ (cosinePotential d k c))=
      fun x => ∑ i,(k+c*Real.cos (x i)) • B i := by
    rw [h1]
    funext x
    exact (hD x).fderiv
  have hDD x : HasFDerivAt (fun y : E => ∑ i,(k+c*Real.cos (y i)) • B i)
      (∑ i,(-c*Real.sin (x i)) • C i) x := by
    have hi (i : Fin d) : HasFDerivAt (fun y : E => (k+c*Real.cos (y i)) • B i)
        ((-c*Real.sin (x i)) • C i) x := by
      have hh : HasDerivAt (fun z : ℝ => k+c*Real.cos z) (-c*Real.sin (x i)) (x i) := by
        convert ((Real.hasDerivAt_cos (x i)).const_mul c).const_add k using 1 <;> ring
      have hs : HasFDerivAt (fun y : E => k+c*Real.cos (y i)) ((-c*Real.sin (x i)) • a i) x := by
        simpa only [a,Function.comp_def,ContinuousLinearMap.proj_apply,ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.one_apply,ContinuousLinearMap.id_comp] using hh.comp_hasFDerivAt x (a i).hasFDerivAt
      convert hs.smul_const (B i) using 1
      ext z v j
      simp [C,ContinuousLinearMap.smulRight_apply,mul_assoc]
    convert HasFDerivAt.sum (u := Finset.univ) (fun i _ => hi i) using 1
    ext y
    simp only [Finset.sum_apply]
  have h3 : fderiv ℝ (fderiv ℝ (fderiv ℝ (cosinePotential d k c)))=
      fun x => ∑ i,(-c*Real.sin (x i)) • C i := by
    rw [h2]
    funext x
    exact (hDD x).fderiv
  refine ⟨⟨∑ i,(|k|+|c|)*‖B i‖,by positivity⟩,⟨∑ i,|c| *‖C i‖,by positivity⟩,?_,?_⟩
  · intro x
    rw [h2]
    dsimp only
    refine (norm_sum_le Finset.univ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul,Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hb : |c*Real.cos (x i)|≤|c| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg c)).trans_eq (mul_one _)
    exact (abs_add_le _ _).trans (add_le_add le_rfl hb)
  · intro x
    rw [h3]
    dsimp only
    refine (norm_sum_le Finset.univ (fun i => (-c*Real.sin (x i)) • C i)).trans ?_
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_neg]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg c)).trans_eq (mul_one _)) (norm_nonneg _)

end Asakura.Chapter8
