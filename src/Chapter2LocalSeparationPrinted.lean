import Chapter2LocalSeparation
import Chapter2LocalCovarianceIdentification
import FullAuditCovarianceBilinear

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false

/-- The printed zero-variation argument: bounded localization, the stopped
energy equality, terminal norm zero, then removal of the localizers. -/
theorem local_zero_variation_printed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (hz : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → C t ω = 0) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = 0 := by
  obtain ⟨τ,hs,hm,ht,hco,hτX⟩ := hX.localizers
  have hmatch := local_covariance_matches_bounded_localizers P F hF hle hnull
    X X C hC τ hs hm ht hco hτX hτX
  have hzero n : ∀ᵐ ω ∂P, ∀ t, X (min (τ n ω) t) ω = 0 := by
    let Z : boundedMProcess P F := ⟨_,hτX n⟩
    have hC0 : (fun ω => boundedCov P F hF hle hnull Z Z ⊤ ω) =ᵐ[P] 0 := by
      filter_upwards [hmatch,hz] with ω he hω
      have hh := he n ⊤
      simp only [min_top_right] at hh
      exact hh.symm.trans (hω _ (ht n ω))
    have hen := bounded_cov_mean P F hF hle hnull Z Z
    rw [integral_congr_ae hC0] at hen
    simp only [Z,min_top_right,← sq,Pi.zero_apply,integral_zero] at hen
    have hi := (memLp_two_iff_integrable_sq ((hτX n).1.moment ⊤).aestronglyMeasurable).mp ((hτX n).1.moment ⊤)
    simp only [min_top_right] at hi
    have hae := (integral_eq_zero_iff_of_nonneg_ae (.of_forall fun ω => sq_nonneg (X (τ n ω) ω)) hi).mp hen
    have he : (fun ω => X (min (τ n ω) ⊤) ω) =ᵐ[P] (fun _ => (0:ℝ)) := by
      filter_upwards [hae] with ω hω
      simpa only [min_top_right] using sq_eq_zero_iff.mp hω
    exact continuous_m2_terminal_injective P F hF hle _ _ (hτX n).1 (ContinuousM2Witness.zero P F) he
  filter_upwards [ae_all_iff.mpr hzero] with ω hω
  intro t ht0
  obtain ⟨n,hn⟩ := hco ω t ht0
  simpa only [min_eq_right hn.le] using hω n t

theorem local_covariance_separates_printed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X X' : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hX' : LocalMProcessWitness P F X')
    (hcov : ∀ Y, LocalMProcessWitness P F Y →
      ∃ C D, LocalCovarianceWitness P F X Y C ∧ LocalCovarianceWitness P F X' Y D ∧
        ∀ᵐ ω ∂P, ∀ t, t < ⊤ → C t ω = D t ω) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = X' t ω := by
  let Z := fun t ω => X t ω-X' t ω
  have hZ : LocalMProcessWitness P F Z := by
    have h := hX.add P F hF hle (hX'.smul P F (-1))
    convert h using 1
    funext t ω
    dsimp only [Z]
    ring
  obtain ⟨C,D,hC,hD,he⟩ := hcov Z hZ
  have hZZ : LocalCovarianceWitness P F Z Z (fun t ω => -D t ω+C t ω) := by
    have h := hD.bilinear P F hF hle hC (-1)
    convert h using 1 <;> funext t ω <;> (try dsimp only [Z]) <;> ring
  have hzC : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → -D t ω+C t ω = 0 := by
    filter_upwards [he] with ω hω
    intro t ht
    rw [hω t ht]
    ring
  have hz := local_zero_variation_printed P F hF hle hnull Z _ hZ hZZ hzC
  exact hz.mono fun ω hω t ht => sub_eq_zero.mp (hω t ht)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_covariance_separates_printed
