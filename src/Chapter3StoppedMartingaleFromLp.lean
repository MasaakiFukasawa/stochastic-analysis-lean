import Chapter3StoppedPathLp
import Chapter3WrittenLimits

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The original definition of a continuous Lp martingale, before quotienting. -/
structure ContinuousMpWitness
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (p : ℝ≥0∞) (X : ClosedTime T → Ω → ℝ) : Prop where
  adapted : ∀ t, Measurable[F t] (X t)
  moment : ∀ t, MemLp (X t) p P
  path : ∀ ω, Continuous (fun t => X t ω)
  martingale : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s
  initial : X ⊥ =ᵐ[P] 0

/-- Apply dominated convergence to the localized test-set integrals,
with the actual Lp path norm as the common L1 dominator. -/
theorem stopped_martingale_of_path_memLp
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hτt : ∀ ω, τ ω < ⊤) (p : ℝ) (hp : 1 ≤ p)
    (hc : ∀ ω, Continuous (fun t => X (min (τ ω) t) ω))
    (hpath : MemLp (continuousPath (fun t ω => X (min (τ ω) t) ω) hc) (ENNReal.ofReal p) P) :
    ContinuousMpWitness P F (ENNReal.ofReal p) (fun t ω => X (min (τ ω) t) ω) := by
  let Y := fun t ω => X (min (τ ω) t) ω
  let B := fun ω => ‖continuousPath Y hc ω‖
  obtain ⟨hYa,_⟩ := hX.stopped_regular P F hF hle τ hτ hτt
  have hB : Integrable B P := hpath.norm.integrable (by simpa using (ENNReal.ofReal_le_ofReal hp))
  have hYm t : MemLp (Y t) (ENNReal.ofReal p) P := by
    apply hpath.norm.of_le ((hYa t).mono (hle t) le_rfl).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      have h := (continuousPath Y hc ω).norm_coe_le_norm t
      simpa only [continuousPath,ContinuousMap.coe_mk,norm_norm] using h)
  have hYi t : Integrable (Y t) P := (hYm t).integrable (by simpa using (ENNReal.ofReal_le_ofReal hp))
  obtain ⟨σ,hσ,hσm,hσt,hσco,hlocal⟩ := hX.localizers
  let Z := fun n t ω => X (min (σ n ω) (min (τ ω) t)) ω
  have hZ n : ContinuousM2Witness P F (Z n) :=
    continuous_m2_stopped P F hF hle _ (hlocal n).1 τ hτ
  have hZbound n t : ∀ᵐ ω ∂P, ‖Z n t ω‖ ≤ B ω := Filter.Eventually.of_forall (fun ω => by
    have h := (continuousPath Y hc ω).norm_coe_le_norm (min (σ n ω) t)
    simpa only [B,continuousPath,ContinuousMap.coe_mk,Y,Z,min_left_comm] using h)
  have hZconv t : ∀ᵐ ω ∂P, Tendsto (fun n => Z n t ω) atTop (𝓝 (Y t ω)) := by
    apply Filter.Eventually.of_forall
    intro ω
    obtain ⟨N,hN⟩ := hσco ω (τ ω) (hτt ω)
    apply tendsto_const_nhds.congr'
    apply eventually_atTop.mpr
    refine ⟨N,?_⟩
    intro n hn
    dsimp [Y,Z]
    rw [← min_assoc,min_eq_right (hN.le.trans (hσm ω hn))]
  refine ⟨hYa,hYm,hc,?_,?_⟩
  · intro s t hst
    apply Filter.EventuallyEq.symm
    apply ae_eq_condExp_of_forall_setIntegral_eq (hle s) (hYi t)
      (fun _ _ _ => (hYi s).integrableOn) _ (hYa s).stronglyMeasurable.aestronglyMeasurable
    intro E hE _
    have hEm := hle s _ hE
    have hlim r : Tendsto (fun n => ∫ ω in E, Z n r ω ∂P) atTop (𝓝 (∫ ω in E, Y r ω ∂P)) := by
      exact tendsto_integral_of_dominated_convergence B
        (fun n => ((hZ n).moment r).aestronglyMeasurable.restrict) hB.integrableOn
        (fun n => ae_restrict_of_ae (hZbound n r)) (ae_restrict_of_ae (hZconv r))
    have he n : (∫ ω in E, Z n s ω ∂P) = ∫ ω in E, Z n t ω ∂P := by
      calc
        _ = ∫ ω in E, P[Z n t|F s] ω ∂P :=
          setIntegral_congr_ae hEm (((hZ n).martingale s t hst).symm.mono (fun ω hω _ => hω))
        _ = _ := setIntegral_condExp (hle s) (((hZ n).moment t).integrable (by norm_num)) hE
    have hs := hlim s
    simp only [he] at hs
    exact tendsto_nhds_unique hs (hlim t)
  · simpa only [Y,min_bot_right] using hX.initial P F

/-- Chapter 3's final theorem: bracket p/2 integrability gives X^tau in M_p.
The BDG path bound and dominated localized martingale argument are both supplied. -/
theorem stopped_Mp_of_variation_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hτt : ∀ ω, τ ω < ⊤) (p : ℝ) (hp : 1 ≤ p)
    (hAi : Integrable (fun ω => A (τ ω) ω^(p/2)) P) :
    ContinuousMpWitness P F (ENNReal.ofReal p) (fun t ω => X (min (τ ω) t) ω) := by
  obtain ⟨hc,hpath⟩ := stopped_path_memLp_of_variation_moment P hT F hF hle hnull X A hX hA τ hτ hτt
    p (by linarith) hAi
  exact stopped_martingale_of_path_memLp P F hF hle X hX τ hτ hτt p hp hc hpath

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stopped_martingale_of_path_memLp
#print axioms Asakura.Chapter3Complete.stopped_Mp_of_variation_moment
