import Chapter12VectorCylinderExpressions

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

variable {Ω H E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
  (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)

noncomputable def vectorExprPair (c : VectorCylinderExpr H E) :
    Lp E p P × Lp (CompletedHilbertTensor H E) p P :=
  (c.valueLp P W S hS hcore p hp,c.gradientLp P W S hS hcore p hp)

theorem vector_core_span_range :
    (Submodule.span ℝ (range (fun z : SmoothCylinder H × E =>
      (vectorCylinderValue P W S hS hcore z.1 z.2 p hp,
       vectorCylinderDerivative P W S hS hcore z.1 z.2 p hp))) : Set _)=
      range (vectorExprPair (E:=E) P W S hS hcore p hp) := by
  let V := Submodule.span ℝ (range (fun z : SmoothCylinder H × E =>
      (vectorCylinderValue P W S hS hcore z.1 z.2 p hp,
       vectorCylinderDerivative P W S hS hcore z.1 z.2 p hp)))
  apply Set.Subset.antisymm
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z,rfl⟩ := hx
      exact ⟨.term z.1 z.2,rfl⟩
    | zero => exact ⟨.sum 0 Fin.elim0,by simp [vectorExprPair,VectorCylinderExpr.valueLp,VectorCylinderExpr.gradientLp]⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨c,rfl⟩ := ihx
      obtain ⟨d,rfl⟩ := ihy
      refine ⟨.sum 2 (Fin.cases c (fun _ => d)),?_⟩
      simp [vectorExprPair,VectorCylinderExpr.valueLp,VectorCylinderExpr.gradientLp,Fin.sum_univ_two]
      constructor <;> rfl
    | smul a x hx ih =>
      obtain ⟨c,rfl⟩ := ih
      exact ⟨.smul a c,rfl⟩
  · rintro x ⟨c,rfl⟩
    change vectorExprPair P W S hS hcore p hp c∈V
    induction c with
    | term c v => exact Submodule.subset_span (mem_range_self (c,v))
    | sum n c ih =>
      have hh := V.sum_mem (fun j (_ : j∈(Finset.univ : Finset (Fin n))) => ih j)
      simpa only [← prod_mk_sum,vectorExprPair,VectorCylinderExpr.valueLp,VectorCylinderExpr.gradientLp] using hh
    | smul a c ih => exact V.smul_mem a ih

end Asakura.Chapter12
