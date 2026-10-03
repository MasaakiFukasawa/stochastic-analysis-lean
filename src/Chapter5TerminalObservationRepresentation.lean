import Chapter5CommonPreterminalRepresentation
import Chapter5CylinderTerminalLimit
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- The Gaussian observation step reaches the actual terminal payoff,
by a common sequence of preterminal identities and path continuity. -/
theorem terminal_observation_representation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    {n k : ℕ} (W : Fin (n+1) → ClosedTime T → Ω → ℝ) (A : ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (hC : ∀ i j,LocalCovarianceWitness P F (W i) (W j) (fun t w => if i=j then A t w else 0))
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0≤c j) (hcm : Monotone c) (hcT : ∀ j,(c j:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    (index : Fin k → Fin (n+1)) (active : Fin k → Prop) [DecidablePred active]
    (σ : Fin k → ℝ) (hσ : ∀ i,0≤σ i) (hσT : ∀ i,(σ i:EReal)<T)
    (a S : ℝ) (ha : 0≤a) (haS : a<S) (hST : (S:EReal)<T)
    (hpast : ∀ i,¬active i → σ i≤a) (hcurrent : ∀ i,active i → σ i=S)
    (f : (Fin k → ℝ) → ℝ) (D : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (DD : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hdd : ∀ x,HasFDerivAt D (DD x) x)
    (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ≥0) (hD : ∀ x,‖D x‖≤C) (hDD : ∀ x,‖DD x‖≤K) :
    let ν := (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)).map (observationNoiseMap index active)
    let X : Fin k → ClosedTime T → Ω → ℝ := fun i t w => W (index i) (min (realTimeClamp (σ i)) t) w
    let H := fun i (z : Ω × ℝ) => ∫ y,D ((fun j => X j (realTimeClamp z.2) z.1)+
      Real.sqrt (S-(finitePrefixTime (T := T) S (ha.trans haS.le) (realTimeClamp z.2)).val) • y) (Pi.single i 1) ∂ν
    ∃ J : Fin k → ClosedTime T → Ω → ℝ,
      (∀ i,LocalMProcessWitness P F (J i)) ∧
      (∀ i,ItoCovarianceFormula P F (W (index i)) (H i) (J i)) ∧
      (∀ i z,|H i z|≤C) ∧
      (fun w => f (fun i => W (index i) (realTimeClamp (σ i)) w)) =ᵐ[P]
        fun w => (∫ z,f ((fun i => X i (realTimeClamp a) w)+Real.sqrt (S-a) • z) ∂ν)+
          ∑ j ∈ Finset.univ.filter active,(J j (realTimeClamp S) w-J j (realTimeClamp a) w) := by
  classical
  dsimp only
  let Q := observationNoiseMap index active
  let μ := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  let ν := μ.map Q
  have hi : Integrable (fun z : Fin k → ℝ => z) ν :=
    (linear_image_second_moment μ Q (Asakura.FullAudit.finite_gaussian_all_moments 2 (by norm_num))).integrable (by norm_num)
  obtain ⟨J,hJ,hJI,hbound,hrep⟩ := common_preterminal_observation_representation P hT F hF hle hnull W A hW hC hclock
    c hc hcm hcT hcc index active σ hσ hσT a S ha haS hST hpast hcurrent
    f D DD hd hdd hDc hDDc C K hD hDD
  refine ⟨J,hJ,hJI,hbound,?_⟩
  let b := fun j : ℕ => S-(S-a)/((j:ℝ)+1)
  have hb j : b j∈Ico a S := by
    have hd0 : 0<(j:ℝ)+1 := by positivity
    have hd1 : 1≤(j:ℝ)+1 := by have h := Nat.cast_nonneg (α := ℝ) j; linarith
    have hfrac : (S-a)/((j:ℝ)+1)≤S-a := div_le_self (sub_nonneg.mpr haS.le) hd1
    exact ⟨by dsimp only [b]; linarith,sub_lt_self S (div_pos (sub_pos.mpr haS) hd0)⟩
  have hbS : Tendsto b atTop (𝓝 S) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (S-a)
    convert (tendsto_const_nhds (x := S)).sub hh using 1 <;> simp [b,div_eq_mul_inv]
  have ht : Tendsto (fun j => S-b j) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := S)).sub hbS
  have hSt : realTimeClamp (T := T) S<⊤ := by
    change (realTimeClamp S:EReal)<T
    rw [real_time_clamp_eq S (ha.trans haS.le) hST.le]
    exact hST
  have hσS i : σ i≤S := by
    by_cases hiA : active i
    · exact (hcurrent i hiA).le
    · exact (hpast i hiA).trans haS.le
  have hl : LipschitzWith C f := lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hd x).differentiableAt) (fun x => by rw [(hd x).fderiv]; exact_mod_cast hD x)
  filter_upwards [ae_all_iff.mpr (fun j => hrep (b j) (hb j))] with w hw
  let X := fun r i => W (index i) (min (realTimeClamp (σ i)) (realTimeClamp r)) w
  have hx : Tendsto (fun j => X (b j)) atTop (𝓝 (X S)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hwc : ContinuousAt (fun t : ClosedTime T => W (index i) t w)
        (min (realTimeClamp (σ i)) (realTimeClamp S)) :=
      (hW (index i)).path P F w _ ((min_le_right _ _).trans_lt hSt)
    have htc : ContinuousAt (fun r : ℝ => min (realTimeClamp (T := T) (σ i)) (realTimeClamp r)) S :=
      (continuous_const.min real_time_clamp_continuous).continuousAt
    simpa only [X,Function.comp_def] using hwc.tendsto.comp (htc.tendsto.comp hbS)
  have hleft := vector_heat_endpoint_limit ν hi atTop f C hl (X S) (fun j => X (b j)) (fun j => S-b j) hx ht
  have hright := (tendsto_const_nhds (x := ∫ z,f (X a+Real.sqrt (S-a) • z) ∂ν)).add
    (tendsto_finsetSum (Finset.univ.filter active) (fun i _ =>
      ((((hJ i).path P F w _ hSt).comp real_time_clamp_continuous.continuousAt).tendsto.comp hbS).sub_const
        (J i (realTimeClamp a) w)))
  have heq := tendsto_nhds_unique hleft (hright.congr (fun j => (hw j).symm))
  have heX : X S=(fun i => W (index i) (realTimeClamp (σ i)) w) := by
    funext i
    exact congrArg (fun t => W (index i) t w) (min_eq_left (real_time_clamp_mono (hσS i)))
  rw [heX] at heq
  exact heq

end Asakura.Chapter5
