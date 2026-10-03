import Chapter5ItoRepresentationConstructed
import Chapter12ItoIncrementPairing

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The representation used in chapter 12 is obtained from the checked
chapter-5 construction for the same Brownian system. -/
theorem brownian_system_representation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : StrictMono c)
    (hct : StrictMono (fun n => realTimeClamp (T := ⊤) (c n)))
    (hcut : ∀ n,realTimeClamp (T := ⊤) (c n)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (c n))
    (hco : ∀ r : ℝ,∃ n,r≤c n) :
    let V := progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ))))
    let K := Σ _ : Fin (d+1),{r : ℝ // 0≤r ∧ (r:EReal)<⊤}
    ∃ I : Fin (d+1) → V →ₗᵢ[ℝ] Lp ℝ 2 P,
    ∃ L : PiLp 2 (fun _ : Fin (d+1) => V) →ₗᵢ[ℝ] Lp ℝ 2 P,
      (∀ x,L x=∑ i,I i (x i)) ∧
      (∀ i,∀ H : progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))),
        ∃ N : HalfClosedTime → Ω → ℝ,∃ hN : ContinuousM2Witness P B.F N,
          ItoCovarianceFormula P B.F (B.W i) H.val N ∧
          I i ⟨progressiveEnergyToLp B.F c _ H,LinearMap.mem_range_self _ H⟩ = (hN.moment ⊤).toLp (N ⊤)) ∧
      ∀ Y : Lp ℝ 2 P,
        AEStronglyMeasurable[MeasurableSpace.comap
          (fun w (z : K) => B.W z.1 (realTimeClamp z.2.val) w) inferInstance] Y P →
        ∃ ψ, Y = (memLp_const (∫ w,Y w ∂P) : MemLp (fun _ : Ω => ∫ w,Y w ∂P) 2 P).toLp _+L ψ := by
  classical
  have hC i j : LocalCovarianceWitness P B.F (B.W i) (B.W j)
      (fun t w => if i=j then B.C 0 0 t w else 0) := by
    apply (B.cov i j).congr_values_before_terminal P B.F
    intro t ht
    obtain ⟨r,hr,_,he⟩ := finite_closed_time_real t ht
    rw [← he]
    funext w
    rw [B.clock i j w r hr,B.diagonal_clock 0 w r hr]
  obtain ⟨I,L,hL,hI,hrep⟩ := brownian_ito_representation_constructed P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null B.W (B.C 0 0) B.martingale hC
    (fun w r hr _ => B.diagonal_clock 0 w r hr) c hc hcm (fun _ => EReal.coe_lt_top _)
    hct hcut hcc hco
  refine ⟨I,L,hL,hI,?_⟩
  intro Y hY
  obtain ⟨ψ,hψ,_⟩ := hrep Y hY
  refine ⟨ψ,?_⟩
  have he : (L ψ : Ω → ℝ) =ᵐ[P] fun w => Y w-(∫ w,Y w ∂P) := by
    rw [hψ]
    exact centered_L2_is_subtract_expectation P Y
  apply Lp.ext
  filter_upwards [he,Lp.coeFn_add
    ((memLp_const (∫ w,Y w ∂P) : MemLp (fun _ : Ω => ∫ w,Y w ∂P) 2 P).toLp _) (L ψ),
    (memLp_const (∫ w,Y w ∂P) : MemLp (fun _ : Ω => ∫ w,Y w ∂P) 2 P).coeFn_toLp]
    with w hw ha hm
  rw [ha,Pi.add_apply,hm,hw]
  ring

end Asakura.Chapter12
