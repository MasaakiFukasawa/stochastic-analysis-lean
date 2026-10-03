import Chapter12BasketPortfolioAssembly
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem basket_restricted_holdings {Ω D ι : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
    [Fintype ι] [DecidableEq ι] (P : Measure Ω) (μ : Measure D) [SFinite P] [SFinite μ]
    (A : Matrix ι ι ℝ) (hA : A.det≠0)
    (φ : ι → Ω × D → ℝ) (hφ : ∀ i,MemLp (φ i) 2 (P.prod μ))
    (ψ : ι → Ω × D → ℝ) (hψ : ∀ i z,ψ i z=∑ j,(A.transpose)⁻¹ i j*φ j z)
    (S H : ι → D → Ω → ℝ) (hS : ∀ i t w,S i t w≠0)
    (he : ∀ᵐ t ∂μ,∀ᵐ w ∂P,∀ j, (∑ i,A i j*(S i t w*H i t w))=(hφ j).toLp (φ j) (w,t)) :
    ∀ᵐ t ∂μ,∀ᵐ w ∂P,∀ i,H i t w=ψ i (w,t)/S i t w := by
  have hc : ∀ i,∀ᵐ t ∂μ,∀ᵐ w ∂P,(hφ i).toLp (φ i) (w,t)=φ i (w,t) := by
    intro i
    exact Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ:=μ) (ν:=P)).quasiMeasurePreserving.ae (hφ i).coeFn_toLp)
  filter_upwards [he,ae_all_iff.mpr hc] with t ht hc
  filter_upwards [ht,ae_all_iff.mpr hc] with w hw hc
  have hh := basket_holding_identification A hA (fun i => S i t w) (fun i => φ i (w,t))
    (fun i => H i t w) (fun i => hS i t w) (fun j => (hw j).trans (hc j))
  intro i
  rw [hh i,hψ i (w,t)]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.basket_restricted_holdings
