import Chapter12ItoStepIsometry
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
theorem actual_ito_representation_increment_pairing {Ω : Type*} [MeasurableSpace Ω]
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
    (i : Fin d) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (G : Ω → ℝ) (hGm : Measurable[B.F (realTimeClamp a)] G) (hG : MemLp G ∞ P) :
    (∫ z,(ψ i : Lp ℝ 2 (P.prod (volume.restrict (Ioi (0:ℝ))))) z*
      (Ioc a b).indicator (fun _ => G z.1) z.2 ∂P.prod (volume.restrict (Ioi (0:ℝ)))) =
      ∫ w,Y w*G w*(B.W i (realTimeClamp b) w-B.W i (realTimeClamp a) w) ∂P := by
  classical
  let V := progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ))))
  letI : InnerProductSpace ℝ V := Submodule.innerProductSpace _
  letI : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin d => V)) := PiLp.innerProductSpace _
  let H := boundedStepEnergy P B.F B.mono B.le c a b G hGm hG
  let v : progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))) :=
    ⟨progressiveEnergyToLp B.F c _ H,LinearMap.mem_range_self _ H⟩
  obtain ⟨hv,hmean⟩ := actual_ito_step_isometry P B i c (I i) (hI i) a b ha hab G hGm hG
  change (I i v : Ω → ℝ) =ᵐ[P] _ at hv
  change (∫ w,I i v w ∂P)=0 at hmean
  have hsingle : L (PiLp.single 2 i v) = I i v := by
    rw [hL,Finset.sum_eq_single i]
    · simp only [PiLp.single_eq_same]
    · intro j _ hji
      simp only [PiLp.single_eq_of_ne _ hji,map_zero]
    · simp
  have hinner : inner ℝ (L ψ) (I i v) = inner ℝ (ψ i) v := by
    rw [← hsingle,L.inner_map_map,PiLp.inner_apply,Finset.sum_eq_single i]
    · simp only [PiLp.single_eq_same]
    · intro j _ hji
      simp only [PiLp.single_eq_of_ne _ hji,inner_zero_right]
    · simp
  have hconst : inner ℝ ((memLp_const m : MemLp (fun _ : Ω => m) 2 P).toLp _) (I i v) = 0 := by
    rw [L2.inner_def]
    calc
      _ = ∫ w,m*I i v w ∂P := by
        apply integral_congr_ae
        filter_upwards [(memLp_const m : MemLp (fun _ : Ω => m) 2 P).coeFn_toLp] with w hw
        rw [hw]
        change I i v w*m = _
        ring
      _ = 0 := by rw [integral_const_mul,hmean,mul_zero]
  have hYinner : inner ℝ Y (I i v) = inner ℝ (ψ i) v := by
    rw [hrep,inner_add_left,hconst,zero_add,hinner]
  have hleft : inner ℝ (ψ i) v = ∫ z,(ψ i : Lp ℝ 2 (P.prod (volume.restrict (Ioi (0:ℝ))))) z*
      (Ioc a b).indicator (fun _ => G z.1) z.2 ∂P.prod (volume.restrict (Ioi (0:ℝ))) := by
    change inner ℝ ((ψ i).val : Lp ℝ 2 (P.prod (volume.restrict (Ioi (0:ℝ))))) (v.val : Lp ℝ 2 (P.prod (volume.restrict (Ioi (0:ℝ))))) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [H.property.2.2.coeFn_toLp] with z hz
    change inner ℝ ((ψ i : Lp ℝ 2 (P.prod (volume.restrict (Ioi (0:ℝ))))) z) (H.property.2.2.toLp H.val z) = _
    rw [hz]
    change H.val z*((ψ i).val : Lp ℝ 2 (P.prod (volume.restrict (Ioi (0:ℝ))))) z = _
    change (Ioc a b).indicator (fun _ => G z.1) z.2*((ψ i).val : Lp ℝ 2 (P.prod (volume.restrict (Ioi (0:ℝ))))) z = _
    ring
  rw [← hleft,← hYinner,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv] with w hw
  rw [hw]
  change (G w*(B.W i (realTimeClamp b) w-B.W i (realTimeClamp a) w))*Y w = _
  ring

end Asakura.Chapter12
