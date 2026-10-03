import Chapter12CompletedCompositionCauchy
import Chapter12CompletedScalarVectorCauchy
import Chapter12AllSobolevComposition

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)

def ScalarEvenJetCauchy (F : ℕ → Ω → ℝ) (k:ℕ) : Prop :=
  ∀ n:ℕ, 0<n → ∀hp1:1≤((2*n:ℕ):ℝ≥0∞),
    letI : Fact (1≤((2*n:ℕ):ℝ≥0∞)) := ⟨hp1⟩
    ∀x:ℕ → malliavinSobolevJetSpace H P W S hS hcore (2*n:ℕ) (ENNReal.natCast_ne_top _) k,
      (∀m,( (x m).val 0 : Ω → ℝ)=ᵐ[P] F m) →
      CauchySeq (fun m => WithLp.toLp 1 (fun j => (x m).val j))

def VectorEvenJetCauchy (F : ℕ → Ω → H) (k:ℕ) : Prop :=
  ∀ n:ℕ, 0<n → ∀hp1:1≤((2*n:ℕ):ℝ≥0∞),
    letI : Fact (1≤((2*n:ℕ):ℝ≥0∞)) := ⟨hp1⟩
    ∀x:ℕ → vectorSobolevJetSpace H P W S hS hcore (2*n:ℕ) (ENNReal.natCast_ne_top _) k,
      (∀m,((x m).val 0 : Ω → H)=ᵐ[P] F m) → CauchySeq (fun m => (x m).val)

theorem scalar_even_jet_cauchy_at (F:ℕ → Ω → ℝ) (k:ℕ)
    (hc:ScalarEvenJetCauchy H P W S hS hcore F k)
    (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤) (n:ℕ) (hn:0<n) (he:p=(2*n:ℕ))
    (x:ℕ → malliavinSobolevJetSpace H P W S hS hcore p hp k)
    (hx:∀m,((x m).val 0:Ω → ℝ)=ᵐ[P] F m) :
    CauchySeq (fun m => WithLp.toLp 1 (fun j => (x m).val j)) := by
  subst p
  exact hc n hn Fact.out x hx

theorem vector_even_jet_cauchy_at (F:ℕ → Ω → H) (k:ℕ)
    (hc:VectorEvenJetCauchy H P W S hS hcore F k)
    (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤) (n:ℕ) (hn:0<n) (he:p=(2*n:ℕ))
    (x:ℕ → vectorSobolevJetSpace H P W S hS hcore p hp k)
    (hx:∀m,((x m).val 0:Ω → H)=ᵐ[P] F m) : CauchySeq (fun m => (x m).val) := by
  subst p
  exact hc n hn Fact.out x hx

variable (hdense : ∀ (q : ℝ≥0∞) [Fact (1≤q)] (hq : q≠⊤),
      DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))

include hdense

theorem scalar_even_jet_cauchy_const (F:Ω → ℝ) (k:ℕ) :
    ScalarEvenJetCauchy H P W S hS hcore (fun _ => F) k := by
  intro n hn hp1 x hx
  letI : Fact (1≤((2*n:ℕ):ℝ≥0∞)) := ⟨hp1⟩
  let q := ENNReal.conjExponent ((2*n:ℕ):ℝ≥0∞)
  obtain ⟨hq1,hq⟩ := even_conjugate_properties n hn
  letI : Fact (1≤q) := ⟨hq1⟩
  have he : ∀m,x m=x 0 := fun m => completed_scalar_jet_value_injective H P W S hS hcore
    (2*n:ℕ) q (ENNReal.natCast_ne_top _) hq (hdense q hq) k (Lp.ext ((hx m).trans (hx 0).symm))
  simp_rw [he]
  exact cauchySeq_const _

theorem vector_even_jet_cauchy_const (F:Ω → H) (k:ℕ) :
    VectorEvenJetCauchy H P W S hS hcore (fun _ => F) k := by
  intro n hn hp1 x hx
  letI : Fact (1≤((2*n:ℕ):ℝ≥0∞)) := ⟨hp1⟩
  let q := ENNReal.conjExponent ((2*n:ℕ):ℝ≥0∞)
  obtain ⟨hq1,hq⟩ := even_conjugate_properties n hn
  letI : Fact (1≤q) := ⟨hq1⟩
  have he : ∀m,x m=x 0 := fun m => completed_vector_jet_value_injective H P W S hS hcore
    (2*n:ℕ) q (ENNReal.natCast_ne_top _) hq (hdense q hq) k (Lp.ext ((hx m).trans (hx 0).symm))
  simp_rw [he]
  exact cauchySeq_const _
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_even_jet_cauchy_const
#print axioms Asakura.Chapter12.vector_even_jet_cauchy_const
