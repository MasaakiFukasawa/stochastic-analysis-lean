import Chapter12ItoStepIsometry
import Chapter12FiniteConditionalRepresentation
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Ito isometry gives the other side of the Clark--Ocone increment test,
using the concrete chapter-5 integral and the proved step-increment identity. -/
theorem represented_integrands_at_finite_time {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (c : ℕ → ℝ)
    (I : Fin d → progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (L : PiLp 2 (fun _ : Fin d => progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ))))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hL : ∀ x,L x=∑ i,I i (x i))
    (hI : ∀ i,∀ H : progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : HalfClosedTime → Ω → ℝ,∃ hN : ContinuousM2Witness P B.F N,
        ItoCovarianceFormula P B.F (B.W i) H.val N ∧
        I i ⟨progressiveEnergyToLp B.F c _ H,LinearMap.mem_range_self _ H⟩ = (hN.moment ⊤).toLp (N ⊤))
    (Y : Lp ℝ 2 P) (m : ℝ)
    (ψ : PiLp 2 (fun _ : Fin d => progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ))))))
    (hrep : Y = (memLp_const m : MemLp (fun _ : Ω => m) 2 P).toLp _+L ψ)
    (τ : HalfClosedTime) (Y₀ : Ω → ℝ) (hY₀ : Measurable[B.F τ] Y₀)
    (hYeq : (Y : Ω → ℝ) =ᵐ[P] Y₀) :
    ∃ H : Fin d → progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))),
    ∃ N : Fin d → HalfClosedTime → Ω → ℝ,
      (∀ i,progressiveEnergyToLp B.F c _ (H i)=(ψ i).val) ∧
      (∀ i,ContinuousM2Witness P B.F (N i)) ∧
      (∀ i,ItoCovarianceFormula P B.F (B.W i) (H i).val (N i)) ∧
      Y₀ =ᵐ[P] fun w => m+∑ i,N i τ w := by
  classical
  choose H hH using fun i => (ψ i).property
  have hHe i : (⟨progressiveEnergyToLp B.F c _ (H i),LinearMap.mem_range_self _ (H i)⟩ :
      progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))) )=ψ i := Subtype.ext (hH i)
  choose N hN hNI hNE using fun i => hI i (H i)
  have hIe i : I i (ψ i)=(hN i |>.moment ⊤).toLp (N i ⊤) := by
    rw [← hHe i]
    exact hNE i
  have hLe : L ψ=∑ i,(hN i |>.moment ⊤).toLp (N i ⊤) := by rw [hL];simp only [hIe]
  have hNae : ∀ᵐ w ∂P,∀ i,((hN i |>.moment ⊤).toLp (N i ⊤)) w=N i ⊤ w :=
    ae_all_iff.mpr (fun i => (hN i |>.moment ⊤).coeFn_toLp)
  have hLae : (L ψ : Ω → ℝ) =ᵐ[P] (fun w => ∑ i,N i ⊤ w) := by
    rw [hLe]
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => (hN i |>.moment ⊤).toLp (N i ⊤)),hNae] with w hw hn
    simpa only [hn] using hw
  have hYa : (Y : Ω → ℝ) =ᵐ[P] (fun w => m+∑ i,N i ⊤ w) := by
    rw [hrep]
    filter_upwards [Lp.coeFn_add ((memLp_const m : MemLp (fun _ : Ω => m) 2 P).toLp _) (L ψ),
      (memLp_const m : MemLp (fun _ : Ω => m) 2 P).coeFn_toLp,hLae] with w hw hm hl
    rw [hw,Pi.add_apply,hm,hl]
  refine ⟨H,N,hH,hN,hNI,?_⟩
  exact represented_payoff_at_finite_time P B.F B.mono B.le N hN Y₀
    (MemLp.ae_eq hYeq (Lp.memLp Y)) m (hYeq.symm.trans hYa) τ hY₀

end Asakura.Chapter12
