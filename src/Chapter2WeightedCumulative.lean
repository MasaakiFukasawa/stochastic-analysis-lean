import Chapter2WeightedEnergy
import Chapter2CumulativeM2Bound

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- Connect the actual progressive Hilbert space to the stochastic
cumulative integral estimate; no L2 bound on the cumulative process is assumed. -/
theorem weighted_progressive_cumulative_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ) (hab : a ≤ b) [Fact (a ≤ b)] (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hr : ∀ ω x, x ∈ Icc a b → ContinuousWithinAt (A ω) (Icc a b ∩ Ici x) x)
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ ω, A ω b-A ω a ≤ K)
    (F : Icc a b → MeasurableSpace Ω) (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (H : Ω × Icc a b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (hH2 : letI : MeasurableSpace (Ω × Icc a b) := progressiveSpace F
      MemLp H 2 ((weightedPathMeasure P a b hab A hA hr hm).trim
        (progressive_space_le_product F hle))) (t : ℝ) :
    MemLp (fun ω => ∫ r in Iic t, H (ω,projIcc a b hab r)
      ∂(intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure) 2 P ∧
    (∫ ω, (∫ r in Iic t, H (ω,projIcc a b hab r)
      ∂(intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure)^2 ∂P) ≤
      K * ∫ p, H p ^ 2 ∂(weightedPathMeasure P a b hab A hA hr hm).trim
        (progressive_space_le_product F hle) := by
  let κ := randomStieltjesKernel a b hab A hA hr hm
  letI : IsFiniteKernel κ := random_stieltjes_kernel_finite a b hab A hA hr hm K hK
  let μ := weightedPathMeasure P a b hab A hA hr hm
  have hprog := progressive_space_le_product F hle
  have hHp : Measurable H := hH.mono hprog le_rfl
  have hH2p : MemLp H 2 μ := memLp_of_memLp_trim hprog hH2
  let q : Ω × ℝ → Ω × Icc a b := fun p => (p.1,projIcc a b hab p.2)
  have hq : Measurable q := measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
  have hG2 : MemLp (H ∘ q) 2 (P ⊗ₘ κ) := hH2p.comp_of_map hq.aemeasurable
  have hmass (ω) : (κ ω).real univ ≤ K := by
    change ((intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure univ).toReal ≤ K
    rw [interval_stieltjes_total_mass a b hab A hA hr,
      ENNReal.toReal_ofReal (sub_nonneg.2 (hA ω (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab))]
    exact hK ω
  have hb := cumulative_kernel_memLp_two P κ K hK0 hmass (H ∘ q) (hHp.comp hq) hG2 t
  have he : (∫ p, (H ∘ q) p ^ 2 ∂(P ⊗ₘ κ)) = ∫ p, H p ^ 2 ∂μ.trim hprog := by
    rw [← integral_trim hprog (hH.pow_const 2).stronglyMeasurable]
    exact (integral_map hq.aemeasurable (hHp.pow_const 2).aestronglyMeasurable).symm
  rw [he] at hb
  exact hb

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.weighted_progressive_cumulative_memLp_two
