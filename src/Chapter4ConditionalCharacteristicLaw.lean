import Chapter4VectorLevyConstructed

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- A constant conditional characteristic function determines both the
law and independence, in a finite-dimensional space (and any separable
Banach space with the stated instances). -/
theorem independence_of_constant_conditional_characteristic
    {Ω E : Type*} {m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    (Z : Ω → E) (hZ : Measurable[m] Z) (K : StrongDual ℝ E → ℂ)
    (h : ∀ L,P[(fun w => Complex.exp ((L (Z w):ℂ)*Complex.I)) | G]=ᵐ[P] fun _ => K L) :
    charFunDual (@Measure.map Ω E m _ Z P)=K ∧ Indep (MeasurableSpace.comap Z inferInstance) G P := by
  letI : MeasurableSpace Ω := m
  have hi (L : StrongDual ℝ E) : Integrable (fun w => Complex.exp ((L (Z w):ℂ)*Complex.I)) P := by
    apply Integrable.of_bound (by fun_prop) 1
    apply ae_of_all
    intro w
    simp [Complex.norm_exp]
  have hk : charFunDual (P.map Z)=K := by
    funext L
    rw [charFunDual_apply,integral_map hZ.aemeasurable (by fun_prop)]
    rw [← integral_condExp hG,integral_congr_ae (h L)]
    simp
  refine ⟨hk,?_⟩
  apply (Asakura.FullAudit.independent_law_of_restricted_laws G P (P.map Z) hG Z hZ ?_).2
  intro A hA
  letI : IsFiniteMeasure (P A • P.map Z) := ⟨by simp [Measure.smul_apply,measure_lt_top]⟩
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply,integral_map hZ.aemeasurable (by fun_prop),charFunDual_apply,integral_smul_measure]
  rw [← setIntegral_condExp hG (hi L) hA,
    setIntegral_congr_ae (hG _ hA) ((h L).mono (fun w hw _ => hw))]
  have hkL := congrFun hk L
  rw [charFunDual_apply] at hkL
  rw [hkL]
  simp [Measure.real,Measure.restrict_apply_univ]

lemma dual_coordinate_expansion {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) (x : Fin d → ℝ) :
    L x=∑ i,L (Pi.single i 1)*x i := by
  classical
  have he : x=∑ i,x i • (Pi.single i (1:ℝ)) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [he]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul,smul_eq_mul,mul_comm]

end Asakura.Chapter4
