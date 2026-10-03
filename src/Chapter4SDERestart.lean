import Chapter4ShiftedBrownianIto
import Chapter4ClassicalSolutionData

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- The future of the given SDE is itself the same SDE with initial
value X_s, driven by W_{s+t}-W_s. Both the drift and Ito identities are
proved from the original equation. -/
theorem vector_sde_deterministic_restart
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {dim noise : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → HalfClosedTime → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → C j (realTimeClamp r) w=r)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j))
    (ξ : Ω → Fin dim → ℝ) (X : HalfClosedTime → Ω → Fin dim → ℝ)
    (hX : VectorSDESolution P F W μ σ ξ X) (s : ℝ) (hs : 0≤s) :
    let φ := deterministicTimeShift s hs
    VectorSDESolution P (fun t => F (φ t))
      (fun j t w => W j (φ t) w-W j (φ ⊥) w) μ σ (X (φ ⊥)) (fun t => X (φ t)) := by
  dsimp only
  let φ := deterministicTimeShift s hs
  let G := fun t => F (φ t)
  have hbelow t (ht : t<⊤) : φ t<⊤ := deterministic_shift_below_top s hs t ht
  refine ⟨hX.adapted _ (hbelow ⊥ (EReal.coe_lt_top 0)),
    fun t ht => hX.adapted _ (hbelow t ht),
    fun w t ht => (hX.path w _ (hbelow t ht)).comp (deterministic_shift_continuous s hs).continuousAt,?_⟩
  obtain ⟨N,hN,hNI,he⟩ := hX.integrals
  let V := fun i j t w => N i j (φ t) w-N i j (φ ⊥) w
  have hV i j : LocalMProcessWitness P G (V i j) := local_martingale_shifted_future P F hF hle _ (hN i j) s hs
  have hVI i j : ItoCovarianceFormula P G
      (fun t w => W j (φ t) w-W j (φ ⊥) w)
      (fun z => σ i j (X (φ (realTimeClamp z.2)) z.1)) (V i j) := by
    exact brownian_ito_shifted_future P F hF hle hnull (W j) (N i j) (C j)
      (fun t w => σ i j (X t w)) (hW j) (hN i j) (hC j) (hclock j)
      (fun t ht => (hσ i j).measurable.comp (hX.adapted t ht))
      (fun w t ht => (hσ i j).continuousAt.comp (hX.path w t ht)) (hNI i j) s hs
  refine ⟨V,hV,hVI,?_⟩
  filter_upwards [he] with w hw
  intro r hr _ i
  have hμreal : Continuous (fun a => μ i (X (realTimeClamp a) w)) :=
    half_line_integral_continuous _ (fun t ht => (hμ i).continuousAt.comp (hX.path w t ht))
  have hshift : (∫ a in 0..r,μ i (X (φ (realTimeClamp a)) w))=
      (∫ a in 0..(s+r),μ i (X (realTimeClamp a) w))-(∫ a in 0..s,μ i (X (realTimeClamp a) w)) := by
    rw [integral_primitive_shift _ hμreal]
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le hr] at ha
    dsimp only [φ]
    rw [deterministic_shift_real s hs a ha.1]
  dsimp only [V]
  rw [hshift]
  simp only [φ,deterministic_shift_real s hs r hr,deterministic_shift_bot s hs,Finset.sum_sub_distrib]
  rw [hw (s+r) (add_nonneg hs hr) (EReal.coe_lt_top _) i,hw s hs (EReal.coe_lt_top _) i]
  ring

end Asakura.Chapter4
