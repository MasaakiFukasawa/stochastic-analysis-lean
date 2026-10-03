import Chapter4DiscountCalculus

open MeasureTheory Set
open scoped Topology
namespace Asakura.Chapter4
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The cancellation of the discount drift and source drift, retaining
the actual path integrals rather than replacing them by formal symbols. -/
theorem discounted_drift_cancellation (k b u n g : ℝ → ℝ)
    (hk : Continuous k) (hb : Continuous b) (hn : Continuous n) (hg : Continuous g)
    (a z R : ℝ) (hR : 0≤R)
    (hu : ∀ r∈Icc 0 R,u r=a+n r+∫ s in 0..r,b s)
    (hdriver : ∀ r∈Icc 0 R,b r=k r*u r-g r)
    (hp : n R*discountFactor k R=z-∫ r in 0..R,n r*discountFactor k r*k r) :
    u R*discountFactor k R+(∫ r in 0..R,g r*discountFactor k r)=a+z := by
  let B := fun r => a+∫ s in 0..r,b s
  have hBc : Continuous B := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact ((intervalIntegral.integral_hasDerivAt_right (hb.intervalIntegrable 0 r)
      hb.stronglyMeasurable.stronglyMeasurableAtFilter hb.continuousAt).const_add a).continuousAt
  have hD := discount_factor_continuous k hk
  have hdet := discount_primitive_product k b hk hb a R
  have hsum : (∫ r in 0..R,discountFactor k r*(b r-k r*B r))-
      (∫ r in 0..R,n r*discountFactor k r*k r)+
      (∫ r in 0..R,g r*discountFactor k r)=0 := by
    have hfi : IntervalIntegrable (fun r => discountFactor k r*(b r-k r*B r)) volume 0 R :=
      (hD.mul (hb.sub (hk.mul hBc))).intervalIntegrable 0 R
    have hni : IntervalIntegrable (fun r => n r*discountFactor k r*k r) volume 0 R :=
      (hn.mul hD |>.mul hk).intervalIntegrable 0 R
    have hgi : IntervalIntegrable (fun r => g r*discountFactor k r) volume 0 R :=
      (hg.mul hD).intervalIntegrable 0 R
    rw [← intervalIntegral.integral_sub hfi hni,
      ← intervalIntegral.integral_add (hfi.sub hni) hgi]
    calc
      _ = ∫ r in 0..R,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr' : r∈Icc 0 R := by simpa only [uIcc_of_le hR] using hr
        have hh := hu r hr'
        have hd := hdriver r hr'
        dsimp only [B]
        rw [hd,hh]
        ring
      _ = 0 := intervalIntegral.integral_zero
  have hur := hu R ⟨hR,le_rfl⟩
  dsimp only [B] at hsum
  have hur' := congrArg (fun q : ℝ => q*discountFactor k R) hur
  nlinarith only [hur',hp,hdet,hsum]

end Asakura.Chapter4
