import Chapter3GradientCovariance
import Chapter3GradientCalculus
import Chapter3ItoVariationCovariance
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

theorem stratonovich_chain_rule_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M : Fin d → ClosedTime T → Ω → ℝ)
    (C : Fin d → Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i, SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hC : ∀ i j, LocalCovarianceWitness P F (M i) (M j) (C i j))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 3 f)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k)) :
    ∃ B L Z D : Fin d → ClosedTime T → Ω → ℝ,
      (∀ i, SemimartingaleDecomposition P F
        (fun t ω => fderiv ℝ f (fun k => X k t ω) (Pi.single i 1)) (B i) (L i)) ∧
      (∀ i, SemimartingaleIntegralFormula P F c hc (A i) (M i)
        (fun z => fderiv ℝ f (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (Z i)) ∧
      (∀ i, LocalCovarianceWitness P F (L i) (M i) (D i)) ∧
      ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
        f (fun i => X i t ω) = f (fun i => X i ⊥ ω)+∑ i, (Z i t ω+D i t ω/2) := by
  classical
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  obtain ⟨I,N,J,hIN,hI,hN,hJv,hJc,hJ⟩ := c2_ito_data_exists P hT F hF hle hnull X A M C hX hC
    f hf2 c hc hcm hcT hcc
  obtain ⟨B,L,D,hL,hD,heD⟩ := c3_gradient_covariance P hT F hF hle hnull X A M C J hX hC f hf
    c hc hcm hcT hcc hJc hJ
  let Z := fun i t ω => I i t ω+N i t ω
  have hZ i : SemimartingaleIntegralFormula P F c hc (A i) (M i)
      (fun z => fderiv ℝ f (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (Z i) :=
    ⟨I i,N i,hIN i,hI i,hN i⟩
  have hIto := multivariate_ito_formula P hT F hF hle hnull X A M Z C J hX hC f hf2 c hc hcT hcc hZ hJ
  refine ⟨B,L,Z,D,hL,hZ,hD,?_⟩
  filter_upwards [hIto,heD] with ω hω hDω
  intro t ht
  have heR : (∑ i, (Z i t ω+D i t ω/2)) = (∑ i, Z i t ω)+(∑ i, D i t ω)/2 := by
    calc
      _ = (∑ i, Z i t ω)+(∑ i, D i t ω/2) := Finset.sum_add_distrib
      _ = _ := by rw [Finset.sum_div]
  rw [hω t ht,heR]
  have he : (∑ i, D i t ω) = ∑ i, ∑ j, J i j t ω := by
    calc
      _ = ∑ i, ∑ j, J j i t ω := Finset.sum_congr rfl (fun i _ => hDω i t ht)
      _ = _ := Finset.sum_comm
  rw [he]
  ring

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stratonovich_chain_rule_constructed
