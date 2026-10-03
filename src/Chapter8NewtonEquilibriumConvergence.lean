import Chapter8NewtonSDETransport
import Chapter8CoordinateFlowMoment
import Chapter8SDERealPathData

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance : MeasurableSpace (WithLp 2 (E × E)) := borel _
local instance : BorelSpace (WithLp 2 (E × E)) := ⟨rfl⟩

/-- Combine actual Newton SDE contraction with an invariant P2 law.
No moment bound for the evolved law or transport contraction is assumed. -/
theorem newton_sde_equilibrium_convergence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E) (g : E → E) (H : E → E →L[ℝ] E)
    (l u δ : ℝ) (hl : 0<l) (hlu : l≤u) (hδ : Real.sqrt u-Real.sqrt l<δ)
    (hd : ∀ x,HasFDerivAt g (H x) x) (hH : Continuous H)
    (hs : ∀ x,(H x).toLinearMap.IsSymmetric)
    (hb : ∀ x z,l*‖z‖^2≤ inner ℝ z (H x z) ∧ inner ℝ z (H x z)≤u*‖z‖^2)
    (σ : Fin d → Fin n → ℝ)
    (Z : (Fin (d+d) → ℝ) → HalfClosedTime → Ω → Fin (d+d) → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W
      (Fin.addCases (fun i z => velocityProjection d z i)
        (fun i z => e.symm (-g (e (positionProjection d z))-δ • e (velocityProjection d z)) i))
      (Fin.addCases (fun _ _ _ => 0) (fun i j _ => σ i j)) (fun _ => x) (Z x))
    (L : ℝ) (hL : 0≤L)
    (hLip : ∀ x y,
      (∑ i,((Fin.addCases (fun j z => velocityProjection d z j)
        (fun j z => e.symm (-g (e (positionProjection d z))-δ • e (velocityProjection d z)) j) i x)-
        (Fin.addCases (fun j z => velocityProjection d z j)
        (fun j z => e.symm (-g (e (positionProjection d z))-δ • e (velocityProjection d z)) j) i y))^2)≤L*∑ i,(x i-y i)^2)
    (π : Measure (Fin (d+d) → ℝ)) [IsProbabilityMeasure π] (hπ : MemLp (fun z => z) 2 π) :
    ∃ b r : ℝ,0<r ∧ ∃ hp : 0<b+δ^2/4,
      let A := (phaseLinearEquiv e).trans (newtonCoordinateEquiv δ b hp)
      ∃ C : ℝ,0<C ∧ ∀ T≥0,∀ F : (Fin (d+d) → ℝ) → Ω → (Fin (d+d) → ℝ),
        Measurable (Function.uncurry F) → (∀ x,F x=ᵐ[P] Z x (realTimeClamp T)) →
        flowLaw π P F=π →
        (∀ (μ : Measure (Fin (d+d) → ℝ)),IsProbabilityMeasure μ → MemLp (fun z => z) 2 μ →
          transportDistance (flowLaw μ P F) π≤C*Real.exp (-r*T)*transportDistance μ π) ∧
        (0<T → ∀ (ν : Measure (Fin (d+d) → ℝ)),IsProbabilityMeasure ν → MemLp (fun z => z) 2 ν →
          flowLaw ν P F=ν → ν=π) := by
  obtain ⟨b,r,hr,hp,hc⟩ := newton_sde_transport P B e g H l u δ hl hlu hδ hd hH hs hb σ Z hZ
  let A := (phaseLinearEquiv e).trans (newtonCoordinateEquiv δ b hp)
  let C := (‖A.symm.toContinuousLinearMap‖+1)*(‖A.toContinuousLinearMap‖+1)
  refine ⟨b,r,hr,hp,C,by dsimp [C]; positivity,?_⟩
  intro T hT F hFm hFe hinv
  obtain ⟨hpath,htransport⟩ := hc T hT F hFm hFe
  have hLip' : ∀ x y,
      (∑ i,((Fin.addCases (fun j z => velocityProjection d z j)
        (fun j z => e.symm (-g (e (positionProjection d z))-δ • e (velocityProjection d z)) j) i x)-
        (Fin.addCases (fun j z => velocityProjection d z j)
        (fun j z => e.symm (-g (e (positionProjection d z))-δ • e (velocityProjection d z)) j) i y))^2)+
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
  constructor
  · intro μ hμp hμ
    letI := hμp
    have hFt := coordinate_flow_second_moment A P μ hμ F hFm h0 (Real.exp (-r*T)) (Real.exp_pos _).le hpath
    exact invariant_coordinate_convergence A P μ π F hFm hμ hπ hFt hinv r T
      (htransport μ π hμp inferInstance hμ hπ)
  · intro hTpos ν hνp hν hνinv
    letI := hνp
    have hh := htransport ν π hνp inferInstance hν hπ
    rw [hνinv,hinv] at hh
    exact invariant_coordinate_unique A ν π hν hπ (Real.exp (-r*T))
      (Real.exp_lt_one_iff.mpr (by nlinarith)) hh

end Asakura.Chapter8
