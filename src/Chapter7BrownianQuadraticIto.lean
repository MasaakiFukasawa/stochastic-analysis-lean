import Chapter7LocalProductIntegral
import Chapter7QuadraticProductAlgebra
import Chapter4FiniteItoSum
import Chapter4BrownianSystem

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The quadratic Ito identity with constructed coordinate integrals. -/
theorem brownian_quadratic_ito {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (K : Fin d → Fin d → ℝ) (hK : ∀ i j,K i j=K j i) :
    ∃ N : Fin d → HalfClosedTime → Ω → ℝ,
      (∀ i,LocalMProcessWitness P B.F (N i)) ∧
      (∀ i,ItoCovarianceFormula P B.F (B.W i)
        (fun z => ∑ j,K i j*B.W j (realTimeClamp z.2) z.1) (N i)) ∧
      (∀ᵐ w ∂P,∀ t : ℝ,0≤t →
        (∑ i,∑ j,K i j*B.W i (realTimeClamp t) w*B.W j (realTimeClamp t) w)-t*(∑ i,K i i)=
          2*(∑ i,N i (realTimeClamp t) w)) := by
  have hT : (0:EReal)<⊤ := by simp
  have hreg j := open_process_real_regularity B.F (B.W j)
    ((B.martingale j).adapted P B.F) ((B.martingale j).path P B.F)
  have hex i j := continuous_adapted_ito_exists P hT B.F B.mono B.le B.null (B.W i) (B.martingale i)
    (fun z => B.W j (realTimeClamp z.2) z.1) (hreg j).1 (hreg j).2
  choose I hI hIi using hex
  let N := fun i t w => ∑ j,K i j*I i j t w
  have hN i : LocalMProcessWitness P B.F (N i) := local_martingale_finset_sum P hT B.F B.mono B.le univ
    (fun j t w => K i j*I i j t w) (fun j _ => (hI i j).smul P B.F (K i j))
  have hNI i : ItoCovarianceFormula P B.F (B.W i)
      (fun z => ∑ j,K i j*B.W j (realTimeClamp z.2) z.1) (N i) := by
    apply finite_ito_sum P hT B.F B.mono B.le B.null (B.W i) (B.martingale i) univ
    intro j _
    have hc := (hIi i j).add_smul P B.F B.mono B.le (B.W i) (I i j) (I i j)
      (fun z => B.W j (realTimeClamp z.2) z.1) (fun z => B.W j (realTimeClamp z.2) z.1) (hIi i j) (K i j-1)
    convert hc using 1 <;> ext z w <;> ring
  have hp i j := local_product_integral_formula P hT B.F B.mono B.le B.null
    (B.W i) (B.W j) (B.C i j) (I i j) (I j i)
    (B.martingale i) (B.martingale j) (B.cov i j) (hI i j) (hI j i) (hIi i j) (hIi j i)
  have hpall : ∀ᵐ w ∂P,∀ i j,∀ t,t<⊤ → B.W i t w*B.W j t w=I i j t w+I j i t w+B.C i j t w :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hp i j
  refine ⟨N,hN,hNI,?_⟩
  filter_upwards [hpall] with w hw
  intro t ht
  exact quadratic_product_algebra K (fun i j => I i j (realTimeClamp t) w)
    (fun i => B.W i (realTimeClamp t) w) t hK (fun i j => by
      simpa only [B.clock i j w t ht] using hw i j (realTimeClamp t) (real_time_below t ht (EReal.coe_lt_top _)))

end Asakura.Chapter7
