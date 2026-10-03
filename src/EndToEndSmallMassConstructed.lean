import EndToEndSmallMassSDE
import EndToEndRandomSDEExistence

open MeasureTheory Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

/-- The small-mass limit for actual SDE solutions. Both moment estimates and
the position formula are derived; no estimate uniform in the mass is input. -/
theorem small_mass_constructed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (Γ : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (α : ℝ) (hα : 0<α) (hΓ : ∀ x,α*‖x‖^2≤⟪x,Γ x⟫)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ≥0) (hg : LipschitzWith L g)
    (σ : Fin d → Fin n → ℝ) (ξ : Ω → Fin (d+d) → ℝ) (hξ : MemLp ξ 2 P) (hξm : Measurable[B.F ⊥] ξ) :
    ∃Y : ℝ → HalfClosedTime → Ω → Fin (d+d) → ℝ,
    ∃X : HalfClosedTime → Ω → Fin d → ℝ,
      (∀ m,VectorSDESolution P B.F B.W
      (Fin.addCases (fun i z => velocityProjection d z i)
        (fun i z => e.symm (-m⁻¹ • g (e (positionProjection d z))-(m⁻¹ • Γ.toContinuousLinearMap) (e (velocityProjection d z))) i))
      (Fin.addCases (fun _ _ _ => 0) (fun i j _ => m⁻¹*σ i j)) ξ (Y m)) ∧
      (VectorSDESolution P B.F B.W (fun i z => e.symm (-Γ.symm (g (e z))) i)
      (fun i j _ => e.symm (Γ.symm (e (fun k => σ k j))) i)
      (fun w => positionProjection d (ξ w)) X) ∧
      ∀T : ℝ,0≤T →
        Tendsto (fun m => sSup ((fun t => ∫w,‖e (positionProjection d (Y m (realTimeClamp t) w))-
          e (X (realTimeClamp t) w)‖^2 ∂P) '' Icc 0 T)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let b : ℝ → Fin (d+d) → (Fin (d+d) → ℝ) → ℝ := fun m => Fin.addCases (fun i z => velocityProjection d z i)
    (fun i z => e.symm (-m⁻¹ • g (e (positionProjection d z))-(m⁻¹ • Γ.toContinuousLinearMap) (e (velocityProjection d z))) i)
  let a : ℝ → Fin (d+d) → Fin n → (Fin (d+d) → ℝ) → ℝ := fun m => Fin.addCases (fun _ _ _ => (0:ℝ)) (fun i j _ => m⁻¹*σ i j)
  have hylip m : ∃K:ℝ,0≤K ∧ ∀ x y,(∑i,(b m i x-b m i y)^2)+
      (∑i,∑j,(a m i j x-a m i j y)^2)≤K*∑i,(x i-y i)^2 := by
    obtain ⟨K,hK,hk⟩ := newton_mass_lipschitz e Γ.toContinuousLinearMap g L hg m
    refine ⟨K,hK,?_⟩
    intro x y
    have he i j : a m i j x=a m i j y := by
      refine Fin.addCases ?_ ?_ i <;> intro k <;> simp only [a,Fin.addCases_left,Fin.addCases_right]
    simpa only [he,sub_self,zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero] using hk x y
  have hex m : ∃Y : HalfClosedTime → Ω → Fin (d+d) → ℝ,
      VectorSDESolution P B.F B.W (b m) (a m) ξ Y := by
    obtain ⟨K,hK,hk⟩ := hylip m
    exact random_sde_exists P B K hK (b m) (a m) hk ξ hξm hξ
  choose Y hY using hex
  obtain ⟨KX,hKX,hkx⟩ := overdamped_drift_lipschitz e Γ.symm.toContinuousLinearMap g L hg
  have hxlip x y : (∑i,(e.symm (-Γ.symm (g (e x))) i-e.symm (-Γ.symm (g (e y))) i)^2)+
      (∑i,∑j:Fin n,(e.symm (Γ.symm (e (fun k => σ k j))) i-e.symm (Γ.symm (e (fun k => σ k j))) i)^2)≤KX*∑i,(x i-y i)^2 := by
    simpa using hkx x y
  obtain ⟨X,hX⟩ := random_sde_exists P B KX hKX _ _ hxlip _
    ((positionProjection d).continuous.measurable.comp hξm) ((positionProjection d).comp_memLp' hξ)
  exact ⟨Y,X,hY,hX,fun T hT => small_mass_sde_limit P B e Γ α hα hΓ g L hg σ ξ hξ Y hY X hX T hT⟩

#print axioms small_mass_constructed
end Asakura.EndToEnd
