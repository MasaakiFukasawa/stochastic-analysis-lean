import Chapter4ConstructedExamples

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The two coordinates, initial values, adaptation, path continuity and
actual integral equations of the manuscript's circle example together. -/
theorem circle_sde_complete
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (a σ θ : ℝ)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c)
    (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hclock : ∀ n ω r, r ∈ Icc 0 (c n) → C (realTimeClamp r) ω = r) :
    let x := fun t ω => a*Real.cos (σ*X t ω+θ)
    let y := fun t ω => a*Real.sin (σ*X t ω+θ)
    (∀ t, t < ⊤ → Measurable[F t] (fun ω => (x t ω,y t ω))) ∧
    (∀ ω t, t < ⊤ → ContinuousAt (fun s => (x s ω,y s ω)) t) ∧
    (∀ t ω, (x t ω)^2+(y t ω)^2 = a^2) ∧
    ∃ Z₁ Z₂ : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Z₁ ∧ LocalMProcessWitness P F Z₂ ∧
      ItoCovarianceFormula P F X (fun z => -σ*y (realTimeClamp z.2) z.1) Z₁ ∧
      ItoCovarianceFormula P F X (fun z => σ*x (realTimeClamp z.2) z.1) Z₂ ∧
      ∀ᵐ ω ∂P, x ⊥ ω = a*Real.cos θ ∧ y ⊥ ω = a*Real.sin θ ∧
        ∀ d : ℝ, 0 ≤ d → (d:EReal) < T →
          x (realTimeClamp d) ω = a*Real.cos θ+Z₁ (realTimeClamp d) ω
            - σ^2/2*(∫ r in 0..d, x (realTimeClamp r) ω) ∧
          y (realTimeClamp d) ω = a*Real.sin θ+Z₂ (realTimeClamp d) ω
            - σ^2/2*(∫ r in 0..d, y (realTimeClamp r) ω) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · intro t ht
    have hm := hX.adapted P F t ht
    exact (measurable_const.mul ((measurable_const.mul hm).add measurable_const).cos).prodMk
      (measurable_const.mul ((measurable_const.mul hm).add measurable_const).sin)
  · intro ω t ht
    have hc := hX.path P F ω t ht
    have harg : ContinuousAt (fun s => σ*X s ω+θ) t :=
      (continuousAt_const.mul hc).add continuousAt_const
    exact (continuousAt_const.mul (Real.continuous_cos.continuousAt.comp harg)).prodMk
      (continuousAt_const.mul (Real.continuous_sin.continuousAt.comp harg))
  · intro t ω
    exact circle_constraint a (σ*X t ω+θ)
  · obtain ⟨Z₁,hZ₁,hI₁,hE₁⟩ := circle_cos_ito P hT F hF hle hnull X C hX hC a σ θ c hc hcm hcT hcc hclock
    obtain ⟨Z₂,hZ₂,hI₂,hE₂⟩ := circle_sin_ito P hT F hF hle hnull X C hX hC a σ θ c hc hcm hcT hcc hclock
    refine ⟨Z₁,Z₂,hZ₁,hZ₂,hI₁,hI₂,?_⟩
    filter_upwards [hE₁,hE₂,hX.initial P F] with ω hω₁ hω₂ h0
    refine ⟨by simp [h0],by simp [h0],?_⟩
    intro d hd hdT
    have he₁ := hω₁ d hd hdT
    have he₂ := hω₂ d hd hdT
    simp only [h0,Pi.zero_apply,mul_zero,zero_add,intervalIntegral.integral_const_mul] at he₁ he₂
    simp only [intervalIntegral.integral_const_mul]
    constructor <;> nlinarith [he₁,he₂]

/-- The two coordinates, initial values, adaptation, path continuity and
actual integral equations of the manuscript's hyperbolic example together. -/
theorem hyperbolic_sde_complete
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (a σ θ : ℝ)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c)
    (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hclock : ∀ n ω r, r ∈ Icc 0 (c n) → C (realTimeClamp r) ω = r) :
    let x := fun t ω => a*Real.cosh (σ*X t ω+θ)
    let y := fun t ω => a*Real.sinh (σ*X t ω+θ)
    (∀ t, t < ⊤ → Measurable[F t] (fun ω => (x t ω,y t ω))) ∧
    (∀ ω t, t < ⊤ → ContinuousAt (fun s => (x s ω,y s ω)) t) ∧
    (∀ t ω, (x t ω)^2-(y t ω)^2 = a^2) ∧
    ∃ Z₁ Z₂ : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Z₁ ∧ LocalMProcessWitness P F Z₂ ∧
      ItoCovarianceFormula P F X (fun z => σ*y (realTimeClamp z.2) z.1) Z₁ ∧
      ItoCovarianceFormula P F X (fun z => σ*x (realTimeClamp z.2) z.1) Z₂ ∧
      ∀ᵐ ω ∂P, x ⊥ ω = a*Real.cosh θ ∧ y ⊥ ω = a*Real.sinh θ ∧
        ∀ d : ℝ, 0 ≤ d → (d:EReal) < T →
          x (realTimeClamp d) ω = a*Real.cosh θ+Z₁ (realTimeClamp d) ω
            + σ^2/2*(∫ r in 0..d, x (realTimeClamp r) ω) ∧
          y (realTimeClamp d) ω = a*Real.sinh θ+Z₂ (realTimeClamp d) ω
            + σ^2/2*(∫ r in 0..d, y (realTimeClamp r) ω) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · intro t ht
    have hm := hX.adapted P F t ht
    exact (measurable_const.mul ((measurable_const.mul hm).add measurable_const).cosh).prodMk
      (measurable_const.mul ((measurable_const.mul hm).add measurable_const).sinh)
  · intro ω t ht
    have hc := hX.path P F ω t ht
    have harg : ContinuousAt (fun s => σ*X s ω+θ) t :=
      (continuousAt_const.mul hc).add continuousAt_const
    exact (continuousAt_const.mul (Real.continuous_cosh.continuousAt.comp harg)).prodMk
      (continuousAt_const.mul (Real.continuous_sinh.continuousAt.comp harg))
  · intro t ω
    exact hyperbolic_constraint a (σ*X t ω+θ)
  · obtain ⟨Z₁,hZ₁,hI₁,hE₁⟩ := hyperbolic_cosh_ito P hT F hF hle hnull X C hX hC a σ θ c hc hcm hcT hcc hclock
    obtain ⟨Z₂,hZ₂,hI₂,hE₂⟩ := hyperbolic_sinh_ito P hT F hF hle hnull X C hX hC a σ θ c hc hcm hcT hcc hclock
    refine ⟨Z₁,Z₂,hZ₁,hZ₂,hI₁,hI₂,?_⟩
    filter_upwards [hE₁,hE₂,hX.initial P F] with ω hω₁ hω₂ h0
    refine ⟨by simp [h0],by simp [h0],?_⟩
    intro d hd hdT
    have he₁ := hω₁ d hd hdT
    have he₂ := hω₂ d hd hdT
    simp only [h0,Pi.zero_apply,mul_zero,zero_add,intervalIntegral.integral_const_mul] at he₁ he₂
    simp only [intervalIntegral.integral_const_mul]
    constructor <;> nlinarith [he₁,he₂]


/-- The scalar hyperbolic SDE, including the sign for negative a.
For a = 0 both the solution and both coefficients vanish. -/
theorem hyperbolic_scalar_sde_complete
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (a σ θ : ℝ)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c)
    (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hclock : ∀ n ω r, r ∈ Icc 0 (c n) → C (realTimeClamp r) ω = r) :
    ∃ Z : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X
        (fun z => σ*SignType.sign a*Real.sqrt (a^2+|a*Real.sinh (σ*X (realTimeClamp z.2) z.1+θ)|^2)) Z ∧
      ∀ᵐ ω ∂P, ∀ d : ℝ, 0 ≤ d → (d:EReal) < T →
        a*Real.sinh (σ*X (realTimeClamp d) ω+θ) = a*Real.sinh θ+Z (realTimeClamp d) ω+
          σ^2/2*(∫ r in 0..d, a*Real.sinh (σ*X (realTimeClamp r) ω+θ)) := by
  obtain ⟨Z,hZ,hI,hE⟩ := hyperbolic_sinh_ito P hT F hF hle hnull X C hX hC a σ θ c hc hcm hcT hcc hclock
  have he : (fun z : Ω × ℝ => σ*SignType.sign a*Real.sqrt
      (a^2+|a*Real.sinh (σ*X (realTimeClamp z.2) z.1+θ)|^2)) =
      (fun z => σ*(a*Real.cosh (σ*X (realTimeClamp z.2) z.1+θ))) := by
    funext z
    rw [mul_assoc,hyperbolic_scalar_diffusion]
  refine ⟨Z,hZ,?_,?_⟩
  · rw [he]
    exact hI
  · filter_upwards [hE,hX.initial P F] with ω hω h0
    intro d hd hdT
    have h := hω d hd hdT
    simp only [h0,Pi.zero_apply,mul_zero,zero_add,intervalIntegral.integral_const_mul] at h
    simp only [intervalIntegral.integral_const_mul]
    nlinarith [h]

end Asakura.Chapter4
