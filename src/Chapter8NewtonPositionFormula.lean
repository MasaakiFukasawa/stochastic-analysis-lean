import Chapter8NewtonPositionIdentity

open MeasureTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Position formula from the two Newton integral equations and the
constructed linear-noise solution. This also identifies all three remainder
terms without assuming a stochastic convolution representation of V. -/
theorem newton_position_formula {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (Γ : E ≃L[ℝ] E) (m : ℝ) (hm : m≠0)
    (Q V N W : ℝ → E) (g : E → E) (hg : Continuous g) (q v : E)
    (T : ℝ) (hT : 0≤T) (hQ : Continuous Q) (hV : Continuous V) (hN : Continuous N)
    (hQi : ∀ t∈Icc 0 T,Q t=q+∫ s in 0..t,V s)
    (hVi : ∀ t∈Icc 0 T,V t=v+(∫ s in 0..t,(-m⁻¹) • Γ (V s)+(-m⁻¹) • g (Q s))+m⁻¹ • W t)
    (hNi : ∀ t∈Icc 0 T,N t=(∫ s in 0..t,(-m⁻¹) • Γ (N s))+m⁻¹ • W t) :
    let A := -m⁻¹ • Γ.toContinuousLinearMap
    V T=NormedSpace.exp (T • A) v-m⁻¹ • (∫ s in 0..T,NormedSpace.exp ((T-s) • A) (g (Q s)))+N T ∧
    Q T=q-Γ.symm (∫ s in 0..T,g (Q s))+Γ.symm (W T)+
      (m • Γ.symm (v-NormedSpace.exp (T • A) v)+
        Γ.symm (∫ s in 0..T,NormedSpace.exp ((T-s) • A) (g (Q s)))-m • Γ.symm (N T)) := by
  let A := -m⁻¹ • Γ.toContinuousLinearMap
  have hc : Continuous (fun s => g (Q s)) := hg.comp hQ
  have hΓV : Continuous (fun s => Γ (V s)) := Γ.continuous.comp hV
  have hv := forced_linear_integral_solution A V N (fun t => m⁻¹ • W t)
    (fun s => (-m⁻¹) • g (Q s)) v T hT hV hN (hc.const_smul _) hVi hNi
  have hint : (∫ s in 0..T,NormedSpace.exp ((T-s) • A) ((-m⁻¹) • g (Q s)))=
      (-m⁻¹) • (∫ s in 0..T,NormedSpace.exp ((T-s) • A) (g (Q s))) := by
    simp_rw [map_smul]
    rw [intervalIntegral.integral_smul]
  rw [hint] at hv
  have hv' : V T=NormedSpace.exp (T • A) v-m⁻¹ • (∫ s in 0..T,NormedSpace.exp ((T-s) • A) (g (Q s)))+N T := by
    simpa only [neg_smul,sub_eq_add_neg] using hv
  dsimp only
  refine ⟨hv',?_⟩
  have hve : V T=v-m⁻¹ • Γ (∫ s in 0..T,V s)-m⁻¹ • (∫ s in 0..T,g (Q s))+m⁻¹ • W T := by
    have hh := hVi T ⟨hT,le_rfl⟩
    have hi1 : IntervalIntegrable (fun s => (-m⁻¹) • Γ (V s)) volume 0 T := (hΓV.const_smul _).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun s => (-m⁻¹) • g (Q s)) volume 0 T := (hc.const_smul _).intervalIntegrable _ _
    have hcomm : (∫ s in 0..T,Γ (V s))=Γ (∫ s in 0..T,V s) :=
      Γ.toContinuousLinearMap.intervalIntegral_comp_comm (hV.intervalIntegrable 0 T)
    rw [intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_smul,intervalIntegral.integral_smul,
      hcomm] at hh
    simpa only [neg_smul,sub_eq_add_neg,add_assoc,ContinuousLinearEquiv.coe_coe] using hh
  have hp := newton_position_identity Γ m hm q v (Q T) (V T) (∫ s in 0..T,g (Q s)) (W T)
    (∫ s in 0..T,V s) (hQi T ⟨hT,le_rfl⟩) hve
  have hr := newton_position_remainder Γ.symm.toContinuousLinearMap m hm v (V T) (NormedSpace.exp (T • A) v)
    (∫ s in 0..T,NormedSpace.exp ((T-s) • A) (g (Q s))) (N T) hv'
  rw [sub_eq_add_neg,←neg_smul] at hp
  simp only [ContinuousLinearEquiv.coe_coe] at hr
  rw [hr] at hp
  exact hp
end Asakura.Chapter8
