import Chapter12CompactItoElementary
import Chapter12LpIsometryTransport

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

theorem terminal_compact_ito_exists {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (c : ℕ → ℝ)
    (I : progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hI : ∀ H : progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : HalfClosedTime → Ω → ℝ,∃ hN : ContinuousM2Witness P B.F N,
        ItoCovarianceFormula P B.F (B.W i) H.val N ∧
        I ⟨progressiveEnergyToLp B.F c _ H,LinearMap.mem_range_self _ H⟩ = (hN.moment ⊤).toLp (N ⊤))
    (T : ℝ) (hT : 0<T) [Fact (0≤T)] :
    let Fc := fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val)
    let R := P.trim (B.le (realTimeClamp T))
    let hle := fun t : Icc (0:ℝ) T => B.mono (real_time_clamp_mono t.property.2)
    letI := probability_trim P _ (B.le (realTimeClamp T))
    letI : MeasurableSpace Ω := B.F (realTimeClamp T)
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace Fc
    ∃ J : Lp ℝ 2 ((R.prod (compactTimeMeasure T hT.le)).trim
        (progressive_space_le_product Fc hle)) →ₗᵢ[ℝ] Lp ℝ 2 R,
      ∀ (a b : Icc (0:ℝ) T),a≤b → ∀ (G : Ω → ℝ)
        (hG : Measurable[Fc a] G) (hg : MemLp G ∞ R),
        (J (timeElementaryLp R T hT Fc
          (B.mono.comp (real_time_clamp_mono.comp (Subtype.mono_coe _))) hle a b G hG hg) : Ω → ℝ)
          =ᵐ[R] (fun w => G w*(B.W i (realTimeClamp b.val) w-B.W i (realTimeClamp a.val) w)) := by
  let Fc := fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val)
  let mT := B.F (realTimeClamp T)
  let R := P.trim (B.le (realTimeClamp T))
  let hle := fun t : Icc (0:ℝ) T => B.mono (real_time_clamp_mono t.property.2)
  let hFc := B.mono.comp (real_time_clamp_mono.comp (Subtype.mono_coe (·∈Icc (0:ℝ) T)))
  letI : MeasurableSpace Ω := m
  letI := probability_trim P _ (B.le (realTimeClamp T))
  let QP := (@Measure.prod Ω (Icc (0:ℝ) T) m inferInstance P (compactTimeMeasure T hT.le)).trim (progressive_space_le_product Fc (fun _ => B.le _))
  let QR := (@Measure.prod Ω (Icc (0:ℝ) T) mT inferInstance R (compactTimeMeasure T hT.le)).trim
    (progressive_space_le_product Fc hle)
  have hQ : QR=QP := progressive_terminal_trim P T hT.le mT (B.le _) Fc hle
  obtain ⟨J,hJ⟩ := @lp_isometry_transport (Ω × Icc (0:ℝ) T) ℝ
    (Lp ℝ 2 R) (progressiveSpace Fc) _ _ _ _ QR QP hQ
    (compactItoIsometry P B i c I hI T hT.le)
  dsimp only
  refine ⟨J,?_⟩
  intro a b hab G hG hg
  have hgP : MemLp G ∞ P := memLp_of_memLp_trim (B.le _) hg
  have he := hJ (fun z => (Ico a b).indicator (fun _ => G z.1) z.2)
    (@time_elementary_memLp Ω mT R (probability_trim P _ (B.le _)) T hT inferInstance Fc hFc hle a b G hG hg)
    (time_elementary_memLp P T hT Fc hFc (fun _ => B.le _) a b G hG hgP)
  change (J ((@time_elementary_memLp Ω mT R (probability_trim P _ (B.le _)) T hT inferInstance Fc hFc hle a b G hG hg).toLp _) : Ω → ℝ)=ᵐ[R] _
  rw [he]
  exact compact_ito_elementary P B i c I hI T hT a b hab G hG hgP

end Asakura.Chapter12
