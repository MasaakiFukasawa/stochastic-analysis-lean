import Chapter6AffineBrownianPaths
import Chapter6BoundedGirsanov
import Chapter6SupportedIntegral
import Chapter6WeakSDEAlgebra

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Girsanov's weak-solution construction with a bounded Borel drift and an
arbitrary F₀-measurable initial value. S and A are mutually inverse matrices;
only the needed identity S A = I enters the finite-sum calculation. -/
theorem bounded_borel_weak_sde
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {dim : ℕ} (B : BrownianSystem P dim) (S A : Fin dim → Fin dim → ℝ)
    (hSA : ∀ i k,∑ j,S i j*A j k = if i=k then 1 else 0)
    (ξ : Ω → Fin dim → ℝ) (hξ : Measurable[B.F ⊥] ξ)
    (μ : (Fin dim → ℝ) × ℝ → Fin dim → ℝ) (hμ : Measurable μ)
    (K : ℝ) (hK : 0 ≤ K) (hμK : ∀ z i,|μ z i| ≤ K)
    (R : ℝ) (hR : 0 ≤ R) (hμ0 : ∀ x t,R < t → μ (x,t) = 0) :
    let X := fun r w i => ξ w i+∑ j,S i j*B.W j (realTimeClamp (max 0 r)) w
    ∃ (Q : Measure Ω) (hQp : IsProbabilityMeasure Q),
      (∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w) ∧
      ∃ BQ : BrownianSystem Q dim,BQ.F = B.F ∧
        ∀ r,0 ≤ r → ∀ᵐ w ∂Q,∀ i,
          X r w i = ξ w i+(∫ s in 0..r,μ (X s w,s) i)+∑ j,S i j*BQ.W j (realTimeClamp r) w := by
  dsimp only
  let X := fun r w i => ξ w i+∑ j,S i j*B.W j (realTimeClamp (max 0 r)) w
  obtain ⟨hXm,hXc,hXa⟩ := affine_brownian_regular P B S ξ hξ
  let b := fun j z => ∑ k,A j k*μ z k
  have hbm j : Measurable (b j) :=
    Finset.measurable_sum _ fun k _ => measurable_const.mul ((measurable_pi_apply k).comp hμ)
  let H := fun j (z : Ω × ℝ) => b j (X z.2 z.1,z.2)
  have hp j := time_borel_coefficient_progressive B.F B.mono X hXm hXc hXa (b j) (hbm j)
  let L := (∑ k,∑ j,|A k j|)*K
  have hL : 0 ≤ L := mul_nonneg (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg _) hK
  have hHb j z : |H j z| ≤ L := finite_linear_coefficient_bound A _ K hK (hμK _) j
  obtain ⟨Q,hQp,hAE,BQ,hBQ,hBWe⟩ := bounded_progressive_girsanov P B H (fun j => (hp j).1)
    (fun j b hb => (hp j).2 b hb.le) L hL hHb R hR
  letI := hQp
  refine ⟨Q,hQp,hAE,BQ,hBQ,?_⟩
  intro r hr
  filter_upwards [ae_all_iff.mpr (fun j => hBWe j r hr)] with w hw
  have hi k : IntervalIntegrable (fun s => μ (X s w,s) k) volume 0 r := by
    apply bounded_time_integrable _ _ K (fun s => hμK _ k) r hr
    exact ((measurable_pi_apply k).comp hμ).comp ((hXc w).measurable.prodMk measurable_id)
  have hV j : BQ.W j (realTimeClamp r) w = B.W j (realTimeClamp r) w-∫ s in 0..r,∑ k,A j k*μ (X s w,s) k := by
    rw [hw j]
    congr 1
    apply supported_integral_min _ R r hR hr
    intro s hs
    simp only [H,b,hμ0 _ _ hs,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  intro i
  simpa only [X,max_eq_right hr] using weak_sde_matrix_algebra S A hSA
    (fun k s => μ (X s w,s) k) r hi (ξ w) (fun j => B.W j (realTimeClamp r) w)
    (fun j => BQ.W j (realTimeClamp r) w) hV i

end Asakura.Chapter6
