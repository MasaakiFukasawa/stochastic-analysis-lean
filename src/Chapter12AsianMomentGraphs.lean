import Chapter12StockTimeMomentExplicit
import Chapter12IntegratedDirectionPairing

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def asianMoment (T : ℝ) (hT : 0 ≤ T) (x σ r : ℝ) (j : ℕ)
    (f : C(Icc (0:ℝ) T,ℝ)) : ℝ :=
  ∫ t : Icc (0:ℝ) T,t.val^j*stockPathValue x σ r T f t ∂compactTimeMeasure T hT

noncomputable def asianMomentGradient {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : ℝ) (hT : 0 ≤ T) (x σ r : ℝ) (j : ℕ) (h : Icc (0:ℝ) T → H)
    (f : C(Icc (0:ℝ) T,ℝ)) : H :=
  ∫ t : Icc (0:ℝ) T,(t.val^j*stockPathValue x σ r T f t) • (σ • h t) ∂compactTimeMeasure T hT

theorem asian_moment_pairing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : ℝ) (hT : 0 ≤ T) (x σ r : ℝ) (j : ℕ) (h : Icc (0:ℝ) T → H) (hh : Continuous h)
    (hTdir : H) (hp : ∀ t, inner ℝ (h t) hTdir = t.val) (f : C(Icc (0:ℝ) T,ℝ)) :
    inner ℝ (asianMomentGradient T hT x σ r j h f) hTdir = σ*asianMoment T hT x σ r (j+1) f := by
  have hc : Continuous (fun t : Icc (0:ℝ) T => t.val^j*stockPathValue x σ r T f t) := by
    unfold stockPathValue
    fun_prop
  unfold asianMomentGradient asianMoment
  rw [integrated_direction_pairing T hT h hh hTdir hp _ hc σ]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  rw [pow_succ]
  ring

theorem asian_moment_closed_graph {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp2 : 2 ≤ p)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp)))
    (T : ℝ) (hT : 0 ≤ T) (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (h : Icc (0:ℝ) T → H) (hh : Continuous h) (hb : ∀ t, ‖h t‖ ≤ Real.sqrt T)
    (hXW : ∀ t, (fun w => X w t) =ᵐ[P] (W (h t) : Ω → ℝ))
    (x σ r : ℝ) (j : ℕ) (G : Ω → ℝ) (hG : MemLp G p P)
    (hSb : ∀ t, ∀ᵐ w ∂P, ‖stockPathValue x σ r T (X w) t‖ ≤ ‖G w‖) :
    ∃ hi : MemLp (fun w => asianMoment T hT x σ r j (X w)) p P,
    ∃ hdi : MemLp (fun w => asianMomentGradient T hT x σ r j h (X w)) p P,
      (hi.toLp _,hdi.toLp _) ∈ D.graph :=
  stock_time_moment_graph_explicit P W S hS hcore p hp hp2 D hD hg T hT (compactTimeMeasure T hT)
    X hXm h hh hb hXW x σ r j G hG hSb

end Asakura.Chapter12
