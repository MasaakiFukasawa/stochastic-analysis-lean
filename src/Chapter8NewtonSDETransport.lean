import Chapter8NewtonSDECoordinates
import Chapter8PhaseLinearEquiv
import Chapter8NewtonCoordinates
import Chapter8ConjugateFlow

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

/-- Apply the energy proof to actual Newton SDE solutions, not to assumed
pathwise estimates. The quadratic norm and rate are uniform in time. -/
theorem newton_sde_transport {Ω : Type*} [MeasurableSpace Ω]
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
      (Fin.addCases (fun _ _ _ => 0) (fun i j _ => σ i j)) (fun _ => x) (Z x)) :
    ∃ b r : ℝ,0<r ∧ ∃ hp : 0<b+δ^2/4,
      let A := (phaseLinearEquiv e).trans (newtonCoordinateEquiv δ b hp)
      ∀ T≥0,∀ F : (Fin (d+d) → ℝ) → Ω → (Fin (d+d) → ℝ),
        Measurable (Function.uncurry F) →
        (∀ x,F x=ᵐ[P] Z x (realTimeClamp T)) →
        (∀ x y,∀ᵐ w ∂P,‖A (F x w)-A (F y w)‖≤Real.exp (-r*T)*‖A x-A y‖) ∧
        ∀ (μ ν : Measure (Fin (d+d) → ℝ)),IsProbabilityMeasure μ → IsProbabilityMeasure ν →
          MemLp (fun z => z) 2 μ → MemLp (fun z => z) 2 ν →
          transportDistance ((flowLaw μ P F).map A) ((flowLaw ν P F).map A)≤
            Real.exp (-r*T)*transportDistance (μ.map A) (ν.map A) := by
  obtain ⟨b,r,hr,hp,hpath⟩ := newton_integral_path_contraction (E := E) l u δ hl hlu hδ
  refine ⟨b,r,hr,hp,?_⟩
  dsimp only
  let A := (phaseLinearEquiv e).trans (newtonCoordinateEquiv δ b hp)
  intro T hT F hF hFe
  have hcon (x y : Fin (d+d) → ℝ) : ∀ᵐ w ∂P,
      ‖A (F x w)-A (F y w)‖≤Real.exp (-r*T)*‖A x-A y‖ := by
    have hg : Continuous g := continuous_iff_continuousAt.mpr (fun z => (hd z).continuousAt)
    have hx := newton_sde_coordinates P B e g hg δ σ x (Z x) (hZ x)
    have hy := newton_sde_coordinates P B e g hg δ σ y (Z y) (hZ y)
    filter_upwards [hx.2,hy.2,hFe x,hFe y] with w hwx hwy hfx hfy
    rw [hfx,hfy]
    let X := fun t => phaseLinearEquiv e (Z x (realTimeClamp t) w)
    let Y := fun t => phaseLinearEquiv e (Z y (realTimeClamp t) w)
    have hh := hpath g H hd hH hs hb (fun t => (X t).1) (fun t => (X t).2)
      (fun t => (Y t).1) (fun t => (Y t).2)
      (fun t => ∑ j,B.W j (realTimeClamp t) w • e (fun i => σ i j))
      (e (positionProjection d x)) (e (velocityProjection d x))
      (e (positionProjection d y)) (e (velocityProjection d y)) T hT
      (hx.1 w).fst (hx.1 w).snd (hy.1 w).fst (hy.1 w).snd
      (fun t ht => hwx.2.1 t ht.1) (fun t ht => hwy.2.1 t ht.1)
      (fun t ht => hwx.2.2 t ht.1) (fun t ht => hwy.2.2 t ht.1) T ⟨hT,le_rfl⟩
    change newtonVectorEnergy δ b ((X T).1-(Y T).1) ((X T).2-(Y T).2)≤
      Real.exp (-2*r*T)*newtonVectorEnergy δ b ((X 0).1-(Y 0).1) ((X 0).2-(Y 0).2) at hh
    have hn := newton_norm_contraction_of_energy δ b r T hp.le (X T-Y T) (X 0-Y 0) hh
    have hX0 : X 0=phaseLinearEquiv e x := hwx.1
    have hY0 : Y 0=phaseLinearEquiv e y := hwy.1
    rw [hX0,hY0] at hn
    change ‖newtonCoordinateEquiv δ b hp (X T)-newtonCoordinateEquiv δ b hp (Y T)‖≤
      Real.exp (-r*T)*‖newtonCoordinateEquiv δ b hp (phaseLinearEquiv e x)-newtonCoordinateEquiv δ b hp (phaseLinearEquiv e y)‖
    rw [←map_sub (newtonCoordinateEquiv δ b hp),←map_sub (newtonCoordinateEquiv δ b hp)]
    exact hn
  refine ⟨hcon,?_⟩
  intro μ ν hμp hνp hμ hν
  letI := hμp
  letI := hνp
  have hm (η : Measure (Fin (d+d) → ℝ)) (hη : MemLp (fun z => z) 2 η) :
      MemLp (fun z : WithLp 2 (E × E) => z) 2 (η.map A) := by
    apply A.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff.mpr
    exact A.toContinuousLinearMap.comp_memLp' hη
  exact conjugate_shared_noise_contraction A.toHomeomorph.toMeasurableEquiv μ ν P F hF
    (hm μ hμ) (hm ν hν) (Real.exp (-r*T)) (Real.exp_pos _) hcon

end Asakura.Chapter8
