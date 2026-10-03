import Chapter12FiniteVectorCoreRebasis

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable def VectorCylinderExpr.rawValue {Ω H E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) : VectorCylinderExpr H E → Ω → E
  | .term c v => fun w => c.value P W w • v
  | .sum n c => fun w => ∑ j,(c j).rawValue P W w
  | .smul a c => fun w => a • c.rawValue P W w

noncomputable def VectorCylinderExpr.finiteTerms {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    VectorCylinderExpr H E → List (SmoothCylinder H × E)
  | .term c v => [(c,v)]
  | .sum n c => (List.ofFn (fun j => (c j).finiteTerms)).flatten
  | .smul a c => c.finiteTerms.map (fun z => (z.1,a • z.2))

theorem VectorCylinderExpr.rawValue_finiteTerms {Ω H E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (c : VectorCylinderExpr H E) (w : Ω) :
    c.rawValue P W w=(c.finiteTerms.map (fun z => z.1.value P W w • z.2)).sum := by
  induction c with
  | term c v => simp [rawValue,finiteTerms]
  | sum n c ih =>
    simp only [rawValue,finiteTerms,List.map_flatten,List.sum_flatten,List.map_ofFn,List.sum_ofFn,ih,Function.comp_def]
  | smul a c ih =>
    simp only [rawValue,finiteTerms,ih,List.map_map,Function.comp_def]
    rw [List.smul_sum,List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro z _
    simp only [Function.comp_apply,smul_smul]
    rw [mul_comm]

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
  (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)

theorem VectorCylinderExpr.valueLp_coe {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : VectorCylinderExpr H E) :
    (c.valueLp P W S hS hcore p hp : Ω → E)=ᵐ[P] c.rawValue P W := by
  induction c with
  | term c v => exact vector_cylinder_value_coe H P W S hS hcore p hp c v
  | sum n c ih =>
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j => (c j).valueLp P W S hS hcore p hp),
      ae_all_iff.mpr ih] with w hw hj
    change (∑ j,(c j).valueLp P W S hS hcore p hp) w=_
    rw [hw]
    exact Finset.sum_congr rfl (fun j _ => hj j)
  | smul a c ih =>
    filter_upwards [Lp.coeFn_smul a (c.valueLp P W S hS hcore p hp),ih] with w hw hc
    change (a • c.valueLp P W S hS hcore p hp) w=_
    rw [hw,Pi.smul_apply,hc]
    rfl

theorem vector_expr_finite_sum (c : VectorCylinderExpr H H) :
    c.valueLp P W S hS hcore p hp=
      (finiteVectorCylinderExpr (fun j : Fin c.finiteTerms.length => (c.finiteTerms.get j).1)
        (fun j => (c.finiteTerms.get j).2)).valueLp P W S hS hcore p hp := by
  apply Lp.ext
  filter_upwards [c.valueLp_coe H P W S hS hcore p hp,
    finite_vector_expr_coe H P W S hS hcore (fun j : Fin c.finiteTerms.length => (c.finiteTerms.get j).1)
      (fun j => (c.finiteTerms.get j).2) p hp] with w hc hf
  rw [hc,hf,c.rawValue_finiteTerms]
  conv_lhs => rw [← List.ofFn_get c.finiteTerms,List.map_ofFn,List.sum_ofFn]
  rfl

end Asakura.Chapter12
