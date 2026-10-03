import Chapter8QuadraticNewtonSDETransport
import Chapter8CoordinateFlowMoment
import Chapter8SDERealPathData
import Chapter8NewtonPhysicalTransport

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
local instance : MeasurableSpace (WithLp 2 (E × E)) := borel _
local instance : BorelSpace (WithLp 2 (E × E)) := ⟨rfl⟩

/-- Combine actual Newton SDE contraction with an invariant P2 law.
No moment bound for the evolved law or transport contraction is assumed. -/
theorem quadratic_newton_sde_physical_convergence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E) (K : E →L[ℝ] E)
    (hs : K.toLinearMap.IsSymmetric) (hK : ∀ z≠0,0 < inner ℝ z (K z))
    (δ : ℝ) (hδ : 0<δ)
    (σ : Fin d → Fin n → ℝ)
    (Z : (Fin (d+d) → ℝ) → HalfClosedTime → Ω → Fin (d+d) → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W
      (Fin.addCases (fun i z => velocityProjection d z i)
        (fun i z => e.symm (-K (e (positionProjection d z))-δ • e (velocityProjection d z)) i))
      (Fin.addCases (fun _ _ _ => 0) (fun i j _ => σ i j)) (fun _ => x) (Z x))
    (L : ℝ) (hL : 0≤L)
    (hLip : ∀ x y,
      (∑ i,((Fin.addCases (fun j z => velocityProjection d z j)
        (fun j z => e.symm (-K (e (positionProjection d z))-δ • e (velocityProjection d z)) j) i x)-
        (Fin.addCases (fun j z => velocityProjection d z j)
        (fun j z => e.symm (-K (e (positionProjection d z))-δ • e (velocityProjection d z)) j) i y))^2)≤L*∑ i,(x i-y i)^2)
    (π : Measure (Fin (d+d) → ℝ)) [IsProbabilityMeasure π] (hπ : MemLp (fun z => z) 2 π) :
    ∃ (A : (Fin (d+d) → ℝ) ≃L[ℝ] WithLp 2
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
      (r : ℝ),0<r ∧
      let R := (phaseLinearEquiv e).trans (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm
      ∃ C : ℝ,0<C ∧ ∀ T≥0,∀ F : (Fin (d+d) → ℝ) → Ω → (Fin (d+d) → ℝ),
        Measurable (Function.uncurry F) → (∀ x,F x=ᵐ[P] Z x (realTimeClamp T)) →
        flowLaw π P F=π →
        (∀ (μ ν : Measure (Fin (d+d) → ℝ)),IsProbabilityMeasure μ → IsProbabilityMeasure ν →
          MemLp (fun z => z) 2 μ → MemLp (fun z => z) 2 ν →
          transportDistance ((flowLaw μ P F).map A) ((flowLaw ν P F).map A)≤
            Real.exp (-r*T)*transportDistance (μ.map A) (ν.map A)) ∧
        (∀ (μ : Measure (Fin (d+d) → ℝ)),IsProbabilityMeasure μ → MemLp (fun z => z) 2 μ →
          transportDistance ((flowLaw μ P F).map R) (π.map R)≤C*Real.exp (-r*T)*transportDistance (μ.map R) (π.map R)) ∧
        (0<T → ∀ (ν : Measure (Fin (d+d) → ℝ)),IsProbabilityMeasure ν → MemLp (fun z => z) 2 ν →
          flowLaw ν P F=ν → ν=π) := by
  obtain ⟨A,r,hr,hc⟩ := quadratic_newton_sde_transport P B e K hs hK δ hδ σ Z hZ
  let R := (phaseLinearEquiv e).trans (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm
  let c₁ := ‖(A.symm.trans R).toContinuousLinearMap‖+1
  let c₂ := ‖(R.symm.trans A).toContinuousLinearMap‖+1
  have hc₁ : 0<c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0<c₂ := by dsimp [c₂]; positivity
  let C := c₁*c₂
  refine ⟨A,r,hr,C,mul_pos hc₁ hc₂,?_⟩
  intro T hT F hFm hFe hinv
  obtain ⟨hpath,htransport⟩ := hc T hT F hFm hFe
  have hLip' : ∀ x y,
      (∑ i,((Fin.addCases (fun j z => velocityProjection d z j)
        (fun j z => e.symm (-K (e (positionProjection d z))-δ • e (velocityProjection d z)) j) i x)-
        (Fin.addCases (fun j z => velocityProjection d z j)
        (fun j z => e.symm (-K (e (positionProjection d z))-δ • e (velocityProjection d z)) j) i y))^2)+
      (∑ i : Fin (d+d),∑ j : Fin n,
        ((Fin.addCases (fun _ _ _ => 0) (fun k h _ => σ k h) i j x)-
        (Fin.addCases (fun _ _ _ => 0) (fun k h _ => σ k h) i j y))^2)≤L*∑ i,(x i-y i)^2 := by
    intro x y
    have he (i : Fin (d+d)) (j : Fin n) : (Fin.addCases (motive := fun _ : Fin (d+d) => Fin n → (Fin (d+d) → ℝ) → ℝ) (fun _ _ _ => (0:ℝ)) (fun k h _ => σ k h) i j x)=
        (Fin.addCases (motive := fun _ : Fin (d+d) => Fin n → (Fin (d+d) → ℝ) → ℝ) (fun _ _ _ => (0:ℝ)) (fun k h _ => σ k h) i j y) := by
      refine Fin.addCases ?_ ?_ i <;> intro k <;> simp only [Fin.addCases_left,Fin.addCases_right]
    simpa only [he,sub_self,zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero] using hLip x y
  have h0 : MemLp (F 0) 2 P := by
    have hh := (sde_real_path_data P B L hL _ _ hLip' (fun _ => 0) (memLp_const 0) (Z 0) (hZ 0)).2.2.1 T
    apply hh.ae_eq
    simpa only [max_eq_right hT] using (hFe 0).symm
  refine ⟨htransport,?_,?_⟩
  · intro μ hμp hμ
    letI := hμp
    have hFt := coordinate_flow_second_moment A P μ hμ F hFm h0 (Real.exp (-r*T)) (Real.exp_pos _).le hpath
    haveI : IsProbabilityMeasure (flowLaw μ P F) :=
      (Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).mpr inferInstance
    have hbound₁ z : ‖R z‖≤c₁*‖A z‖ := by
      have hh := (A.symm.trans R).toContinuousLinearMap.le_opNorm (A z)
      change ‖R (A.symm (A z))‖≤_ at hh
      rw [A.symm_apply_apply] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [c₁]; linarith) (norm_nonneg _))
    have hbound₂ z : ‖A z‖≤c₂*‖R z‖ := by
      have hh := (R.symm.trans A).toContinuousLinearMap.le_opNorm (R z)
      change ‖A (R.symm (R z))‖≤_ at hh
      rw [R.symm_apply_apply] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [c₂]; linarith) (norm_nonneg _))
    have hlow := transport_between_coordinate_norms A R (flowLaw μ P F) π hFt hπ c₁ hc₁ hbound₁
    have hupp := transport_between_coordinate_norms R A μ π hμ hπ c₂ hc₂ hbound₂
    have htr := htransport μ π hμp inferInstance hμ hπ
    rw [hinv] at htr
    have h₁ := hlow.trans (mul_le_mul_of_nonneg_left htr (by positivity))
    have h₂ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hupp (Real.exp_pos (-r*T)).le)
      hc₁.le
    exact (h₁.trans h₂).trans_eq (by dsimp [C]; ring)

  · intro hTpos ν hνp hν hνinv
    letI := hνp
    have hh := htransport ν π hνp inferInstance hν hπ
    rw [hνinv,hinv] at hh
    exact invariant_coordinate_unique A ν π hν hπ (Real.exp (-r*T))
      (Real.exp_lt_one_iff.mpr (by nlinarith)) hh

end Asakura.Chapter8
