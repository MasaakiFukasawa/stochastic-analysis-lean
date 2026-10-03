import Chapter12MatrixEnergyAllocation
import Chapter12VolatilityRowNormalization
import Chapter12BrownianDirectionIntegral

open MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem basket_martingale_allocation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hA : A.det≠0)
    (φ : Fin (d+1) → progressiveEnergyIntegrands B.F canonicalClock (P.prod (volume.restrict (Ioi (0:ℝ)))))
    (N : Fin (d+1) → HalfClosedTime → Ω → ℝ)
    (hN : ∀ j,ContinuousM2Witness P B.F (N j))
    (hNI : ∀ j,ItoCovarianceFormula P B.F (B.W j) (φ j).val (N j)) :
    let σ := fun i => Real.sqrt (∑ j,A i j^2)
    let W := fun i => brownianUnitDirection P B (fun j => A i j/σ i)
      (volatility_row_normalization A hA i).2.2.1
    ∃ ψ : Fin (d+1) → progressiveEnergyIntegrands B.F canonicalClock (P.prod (volume.restrict (Ioi (0:ℝ)))),
    ∃ M : Fin (d+1) → HalfClosedTime → Ω → ℝ,
      (∀ i z,(ψ i).val z=∑ j,(A.transpose)⁻¹ i j*(φ j).val z) ∧
      (∀ i,ContinuousM2Witness P B.F (M i)) ∧
      (∀ i,ItoCovarianceFormula P B.F ((W i).W 0) (fun z => σ i*(ψ i).val z) (M i)) ∧
      ∀ᵐ w ∂P,∀ t,t<⊤ → (∑ i,M i t w)=(∑ j,N j t w) := by
  intro σ W
  obtain ⟨ψ,hψ,hmatch⟩ := matrix_energy_allocation P B A hA φ
  choose Q hQ hQI hM hMI using fun i => brownian_direction_integral P B
    (fun j => A i j/σ i) (volatility_row_normalization A hA i).2.2.1 (σ i • ψ i)
  have hQI' i j : ItoCovarianceFormula P B.F (B.W j)
      (fun z => A i j*(ψ i).val z) (Q i j) := by
    convert hQI i j using 1
    funext z
    change A i j*(ψ i).val z=(A i j/σ i)*(σ i*(ψ i).val z)
    have hz := (volatility_row_normalization A hA i).1.ne'
    field_simp [show σ i≠0 from hz]
  have hcols j : ∀ᵐ w ∂P,∀ t,t<⊤ → (∑ i,Q i j t w)=N j t w := by
    obtain ⟨hc,hcm,hct,hcut,hcc,hco⟩ := canonical_clock_properties
    have hs := finite_M2_ito_sum P (by simp) B.F B.mono B.le B.null (B.W j) (B.martingale j)
      (fun i z => A i j*(ψ i).val z) (fun i => Q i j) Finset.univ (fun i _ => hQ i j) (fun i _ => hQI' i j)
    have hi : ItoCovarianceFormula P B.F (B.W j) (φ j).val (fun t w => ∑ i,Q i j t w) := by
      simpa only [hmatch] using hs.2
    have hl := continuous_m2_is_local P B.F B.mono B.le
      (fun n => realTimeClamp (T:=⊤) (canonicalClock n)) hct.monotone hcut hcc
    exact hi.unique P (by simp) B.F B.mono B.le B.null (B.W j) _ (N j) (φ j).val
      (B.martingale j) (hl _ hs.1) (hl _ (hN j)) (hNI j)
  refine ⟨ψ,fun i t w => ∑ j,Q i j t w,hψ,hM,hMI,?_⟩
  filter_upwards [ae_all_iff.mpr hcols] with w hw
  intro t ht
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => hw j t ht)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.basket_martingale_allocation
