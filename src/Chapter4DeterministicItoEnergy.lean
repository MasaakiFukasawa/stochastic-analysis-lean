import Chapter4DeterministicItoLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

lemma gaussian_law_square_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (a : ℝ) (v : ℝ≥0) (hX : HasLaw X (gaussianReal a v) P) :
    (∫ w,X w^2 ∂P)=a^2+v := by
  have hi := hX.integral_comp (f:=fun x : ℝ => x^2) (by fun_prop)
  simp only [Function.comp_def] at hi
  rw [hi]
  have hv := variance_eq_sub (memLp_id_gaussianReal (μ:=a) (v:=v) 2)
  simp only [variance_id_gaussianReal,integral_id_gaussianReal,Pi.pow_apply,id_eq] at hv
  linarith

/-- The second moment of an actual deterministic Brownian integral. -/
theorem deterministic_brownian_integral_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A N : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A) (hN : LocalMProcessWitness P F N)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hNI : ItoCovarianceFormula P F W (fun z => g z.2) N)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) :
    (∫ w,N (realTimeClamp R) w^2 ∂P)=∫ r in 0..R,g r^2 := by
  have hl := deterministic_brownian_integral_law P hT F hF hle hnull W A N hW hA hN
    hclock g hg hNI R hR hRT
  have hh := gaussian_law_square_integral P _ _ _ hl
  simpa only [zero_pow (by norm_num : (2:ℕ)≠0),zero_add,NNReal.coe_mk,Subtype.coe_mk,NNReal.toReal] using hh

/-- Linearity connects convergence of deterministic kernels to the
second moment of the difference of the actual stochastic integrals. -/
theorem deterministic_brownian_integral_difference_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A N K : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A) (hN : LocalMProcessWitness P F N)
    (hK : LocalMProcessWitness P F K)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (g f : ℝ → ℝ) (hg : Continuous g) (hf : Continuous f)
    (hNI : ItoCovarianceFormula P F W (fun z => g z.2) N)
    (hKI : ItoCovarianceFormula P F W (fun z => f z.2) K)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) :
    (∫ w,(N (realTimeClamp R) w-K (realTimeClamp R) w)^2 ∂P)=∫ r in 0..R,(g r-f r)^2 := by
  have hI : ItoCovarianceFormula P F W (fun z => g z.2+(-1)*f z.2)
      (fun t w => N t w+(-1)*K t w) := by
    convert hKI.add_smul P F hF hle W K N _ _ hNI (-1) using 1 <;> ext z w <;> ring
  have hh := deterministic_brownian_integral_energy P hT F hF hle hnull W A
    (fun t w => N t w+(-1)*K t w) hW hA (hN.add P F hF hle (hK.smul P F (-1))) hclock
    (fun r => g r+(-1)*f r) (hg.add (continuous_const.mul hf)) hI R hR hRT
  simpa only [neg_one_mul,← sub_eq_add_neg] using hh

end Asakura.Chapter4
