import Chapter12SobolevSmoothComposition
import Chapter12AllSobolevFromEven
import Chapter12IBPTestMoments

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem all_sobolev_smooth_composition {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (hdense : ∀ (q : ℝ≥0∞) [Fact (1≤q)] (hq : q≠⊤),
      DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hB : ∀j:ℕ,∃C:ℝ,0≤C ∧ ∃a:ℕ,∀x,‖iteratedFDeriv ℝ j b x‖≤C*(1+‖x‖)^a)
    (F : Ω → ℝ) (hF : HasAllSobolevJets H P W S hS hcore F) :
    HasAllSobolevJets H P W S hS hcore (b ∘ F) := by
  apply all_sobolev_from_even H P W S hS hcore
  intro n hn k
  letI : Fact (1≤((2*n:ℕ):ℝ≥0∞)) := ⟨by exact_mod_cast (show 1≤2*n by omega)⟩
  obtain ⟨K,hK,a,hKB⟩ := finite_polynomial_envelope (fun j x => ‖iteratedFDeriv ℝ j b x‖) hB (k+1)
  let p : ℝ≥0∞ := (2*n:ℕ)
  let t : ℝ≥0∞ := 2*p
  let r : ℝ≥0∞ := t*(a+k+1:ℕ)
  have ht1 : 1≤t := one_le_mul (by norm_num : (1:ℝ≥0∞)≤2) (Fact.out : (1:ℝ≥0∞)≤p)
  letI : Fact (1≤t) := ⟨ht1⟩
  have htr : t≤r := le_mul_of_one_le_right (by positivity) (by exact_mod_cast (show 1≤a+k+1 by omega))
  letI : Fact (1≤r) := ⟨ht1.trans htr⟩
  have hr : r≠⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
    (ENNReal.natCast_ne_top _)) (ENNReal.natCast_ne_top _)
  let q := ENNReal.conjExponent p
  let s := ENNReal.conjExponent r
  obtain ⟨hq1,hq⟩ := even_conjugate_properties n hn
  have hrs : 1≤s ∧ s≠⊤ := by
    have hh := even_conjugate_properties (2*n*(a+k+1)) (by positivity)
    simpa only [s,r,t,p,Nat.cast_mul,Nat.cast_ofNat,mul_assoc] using hh
  letI : Fact (1≤q) := ⟨hq1⟩
  letI : Fact (1≤s) := ⟨hrs.1⟩
  letI : HolderTriple t t p := holder_double_exponent p
  obtain ⟨x,hx⟩ := hF r (Fact.out) hr k
  obtain ⟨y,hy⟩ := sobolev_smooth_composition H P W S hS hcore b hb hB k K
    (zero_le_one.trans hK) a hKB p q t s (ENNReal.natCast_ne_top _) hq hr hrs.2
    (hdense q hq) (hdense s hrs.2) x
  refine ⟨y,hy.trans ?_⟩
  exact hx.fun_comp b
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_sobolev_smooth_composition
