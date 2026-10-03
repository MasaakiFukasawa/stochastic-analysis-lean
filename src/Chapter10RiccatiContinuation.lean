import Chapter10ClippedRiccatiExistence
import Chapter10FirstExit

open Set Matrix
open scoped NNReal Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- A finite-horizon a priori bound really gives existence: construct a
truncated solution, use its first exit time, and prove truncation never acts. -/
theorem riccati_exists_from_apriori {d : ℕ}
    (A H Q : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (hA : Continuous A) (hH : Continuous H) (hQ : Continuous Q)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (T B : ℝ) (hT : 0≤T)
    (hB : 0≤B) (hS₀ : ‖S₀‖≤B)
    (hap : ∀ τ∈Icc 0 T,∀ S : ℝ → Matrix (Fin d) (Fin d) ℝ,
      Continuous S → S 0=S₀ →
      (∀ t∈Ico 0 τ,HasDerivWithinAt S (A t*S t+S t*(A t).transpose+Q t-S t*H t*S t) (Ici t) t) →
      ‖S τ‖≤B) :
    ∃ S : ℝ → Matrix (Fin d) (Fin d) ℝ,Continuous S ∧ S 0=S₀ ∧
      (∀ t∈Ico 0 T,HasDerivWithinAt S (A t*S t+S t*(A t).transpose+Q t-S t*H t*S t) (Ici t) t) ∧
      ∀ t∈Icc 0 T,‖S t‖≤B := by
  let R : ℝ≥0 := ⟨B+1,by linarith⟩
  obtain ⟨S,hSc,hSzero,_,hSd⟩ := clipped_riccati_exists A H Q hA hH hQ S₀ R T hT
  have hinside t (ht : t∈Icc 0 T) : ‖S t‖<(R:ℝ) := by
    by_contra hn
    have hend : (R:ℝ)≤‖S t‖ := le_of_not_gt hn
    have hstart : ‖S 0‖<(R:ℝ) := by
      rw [hSzero]
      change ‖S₀‖<B+1
      linarith
    obtain ⟨τ,hτ,hEq,hbefore⟩ := first_level_crossing (fun s => ‖S s‖) hSc.norm t R ht.1 hstart hend
    have hτT : τ∈Icc (0:ℝ) T := ⟨hτ.1.le,hτ.2.trans ht.2⟩
    have hd s (hs : s∈Ico (0:ℝ) τ) :
        HasDerivWithinAt S (A s*S s+S s*(A s).transpose+Q s-S s*H s*S s) (Ici s) s := by
      have hc := matrixClip_eq_self R (S s) (hbefore s ⟨hs.1,hs.2.le⟩)
      simpa only [hc] using hSd s ⟨hs.1,hs.2.trans_le hτT.2⟩
    have hb := hap τ hτT S hSc hSzero hd
    change ‖S τ‖=B+1 at hEq
    linarith
  have hd t (ht : t∈Ico (0:ℝ) T) :
      HasDerivWithinAt S (A t*S t+S t*(A t).transpose+Q t-S t*H t*S t) (Ici t) t := by
    simpa only [matrixClip_eq_self R (S t) (hinside t ⟨ht.1,ht.2.le⟩).le] using hSd t ht
  refine ⟨S,hSc,hSzero,hd,?_⟩
  intro t ht
  exact hap t ht S hSc hSzero (fun s hs => hd s ⟨hs.1,hs.2.trans_le ht.2⟩)

end Asakura.Chapter10
