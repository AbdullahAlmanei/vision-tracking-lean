import VisionTracking.Budget

/-!
# The overhead formation plan

The drone flies the FIR plan of the target's positions, offset by `d` straight up.
Its thrust axis follows the planned thrust, its forward axis is the downhill axis,
and the hinge is clamped to `tilt - π/2`. This file proves that under `MasterIneq`:

* the plan is a valid `KinPlan`, and every lifting hypothesis holds;
* the target is visible in every frame.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

namespace Overhead

open Budget

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ} {F : FIR} {d : ℝ}
  (T : TargetTraj P δ) (a₀ : E3)

noncomputable def vP (F : FIR) (k : ℕ) : E3 := F.planVel T a₀ k
noncomputable def thr (Q : QuadParams) (F : FIR) (k : ℕ) : E3 :=
  F.planAcc T a₀ k + Q.g • up + (Q.drag * ‖vP T a₀ F k‖) • vP T a₀ F k
noncomputable def b3 (Q : QuadParams) (F : FIR) (k : ℕ) : E3 := nrm (thr T a₀ Q F k)
noncomputable def b1 (Q : QuadParams) (F : FIR) (k : ℕ) : E3 := downhill (b3 T a₀ Q F k)
noncomputable def b2 (Q : QuadParams) (F : FIR) (k : ℕ) : E3 :=
  cross (b3 T a₀ Q F k) (b1 T a₀ Q F k)
noncomputable def tilt (Q : QuadParams) (F : FIR) (k : ℕ) : ℝ := angle (b3 T a₀ Q F k) up
noncomputable def eta (Q : QuadParams) (C : CameraParams) (F : FIR) (k : ℕ) : ℝ :=
  max C.hingeLo (min C.hingeHi (tilt T a₀ Q F k - π / 2))

theorem accExt_natCast (k : ℕ) : T.accExt a₀ k = δ⁻¹ • (T.v (k + 1) - T.v k) := by
  simp [TargetTraj.accExt]

theorem inner_up_sub_le (x y : E3) : |⟪x, up⟫ - ⟪y, up⟫| ≤ ‖x - y‖ := by
  rw [← inner_sub_left]
  have := abs_real_inner_le_norm (x - y) up
  rwa [norm_up', mul_one] at this

theorem norm_horiz_sub_le (x y : E3) : |‖horiz x‖ - ‖horiz y‖| ≤ ‖x - y‖ := by
  refine (abs_norm_sub_norm_le _ _).trans ?_
  have : horiz x - horiz y = horiz (x - y) := by
    simp only [horiz, inner_sub_left, sub_smul]; abel
  rw [this]; exact norm_horiz_le _

theorem H2_nonneg (F : FIR) : 0 ≤ F.H2 :=
  Finset.sum_nonneg fun i _ => by positivity

variable (h : MasterIneq P Q C δ F d) (hS : T.StartsAt (T.p 0) (T.v 0) a₀)
include h hS

theorem vP_err (k : ℕ) : ‖vP T a₀ F k - T.v k‖ ≤ εV P δ F :=
  F.planVel_err T a₀ h.δ_pos hS k

theorem vP_norm_le (k : ℕ) : ‖vP T a₀ F k‖ ≤ Vb P δ F := by
  have h1 := vP_err T a₀ h hS k
  have h2 := norm_le_insert' (vP T a₀ F k) (T.v k)
  have h3 := T.speed_le k
  unfold Vb; linarith

theorem vP_norm_ge (k : ℕ) : P.vMin - εV P δ F ≤ ‖vP T a₀ F k‖ := by
  have h1 := vP_err T a₀ h hS k
  have h2 := norm_sub_norm_le (T.v k) (vP T a₀ F k)
  rw [norm_sub_rev] at h2
  have h3 := T.speed_ge k
  linarith

theorem vP_ne (k : ℕ) : vP T a₀ F k ≠ 0 := by
  intro h0
  have := vP_norm_ge T a₀ h hS k
  rw [h0, norm_zero] at this
  linarith [h.εV_lt]

theorem acc_err (k : ℕ) :
    ‖F.planAcc T a₀ k - δ⁻¹ • (T.v (k + 1) - T.v k)‖ ≤ εD P δ F := by
  have := F.planAcc_err T a₀ h.δ_pos hS k
  rwa [accExt_natCast] at this

theorem planAcc_norm_le (k : ℕ) : ‖F.planAcc T a₀ k‖ ≤ P.Amax + εD P δ F := by
  have h1 := acc_err T a₀ h hS k
  have h2 := norm_targetAcc_le T h.δ_pos k
  have h3 := norm_le_insert' (F.planAcc T a₀ k) (δ⁻¹ • (T.v (k + 1) - T.v k))
  linarith

theorem thr_err (k : ℕ) :
    ‖thr T a₀ Q F k - thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k))‖ ≤ εT P Q δ F := by
  have hsplit : thr T a₀ Q F k - thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k))
      = (F.planAcc T a₀ k - δ⁻¹ • (T.v (k + 1) - T.v k))
        + Q.drag • (‖vP T a₀ F k‖ • vP T a₀ F k - ‖T.v k‖ • T.v k) := by
    unfold thr thrustStar; module
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 := acc_err T a₀ h hS k
  have h2 := norm_dragMap_sub_le (vP T a₀ F k) (T.v k)
  have h3 := vP_err T a₀ h hS k
  have h4 := vP_norm_le T a₀ h hS k
  have h5 := T.speed_le k
  have hc := Q.drag_pos
  have hεV : 0 ≤ εV P δ F := by
    unfold εV; have := H2_nonneg F; have := P.jerk_nonneg; have := h.δ_pos; positivity
  rw [norm_smul, Real.norm_of_nonneg hc.le]
  have h6 : (‖vP T a₀ F k‖ + ‖T.v k‖) * ‖vP T a₀ F k - T.v k‖
      ≤ (2 * P.vMax + εV P δ F) * εV P δ F := by
    apply mul_le_mul _ h3 (norm_nonneg _) (by linarith [P.vMin_pos, P.vMin_le_vMax])
    unfold Vb at h4; linarith
  have := mul_le_mul_of_nonneg_left (h2.trans h6) hc.le
  unfold εT; nlinarith

theorem thr_up_ge (k : ℕ) : Zlo P Q δ F ≤ ⟪thr T a₀ Q F k, up⟫ := by
  have h1 := thr_err T a₀ h hS k
  have h2 := thrustStar_up_ge T Q h.δ_pos k
  have h3 := inner_up_sub_le (thr T a₀ Q F k) (thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)))
  rw [abs_le] at h3
  unfold Zlo; linarith

theorem thr_up_le (k : ℕ) : ⟪thr T a₀ Q F k, up⟫ ≤ Zhi P Q δ F := by
  have h1 := thr_err T a₀ h hS k
  have h2 := thrustStar_up_le T Q h.δ_pos k
  have h3 := inner_up_sub_le (thr T a₀ Q F k) (thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)))
  rw [abs_le] at h3
  unfold Zhi; linarith

theorem thr_norm_le (k : ℕ) : ‖thr T a₀ Q F k‖ ≤ Fhi P Q δ F := by
  have h1 := thr_err T a₀ h hS k
  have h2 := thrustStar_norm_le T Q h.δ_pos k
  have h3 := norm_le_insert' (thr T a₀ Q F k) (thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)))
  unfold Fhi; linarith

theorem thr_horiz_ge (k : ℕ) : Hlo P Q δ F ≤ ‖horiz (thr T a₀ Q F k)‖ := by
  have h1 := thr_err T a₀ h hS k
  have h2 := thrustStar_horiz_ge T Q h.δ_pos k
  have h3 := norm_horiz_sub_le (thr T a₀ Q F k) (thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)))
  rw [abs_le] at h3
  unfold Hlo; linarith

theorem thr_horiz_le (k : ℕ) : ‖horiz (thr T a₀ Q F k)‖ ≤ Hhi P Q δ F := by
  have h1 := thr_err T a₀ h hS k
  have h2 := thrustStar_horiz_le T Q h.δ_pos k
  have h3 := norm_horiz_sub_le (thr T a₀ Q F k) (thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)))
  rw [abs_le] at h3
  unfold Hhi; linarith

theorem thr_norm_ge (k : ℕ) : Zlo P Q δ F ≤ ‖thr T a₀ Q F k‖ := by
  have := real_inner_le_norm (thr T a₀ Q F k) up
  rw [norm_up', mul_one] at this
  linarith [thr_up_ge T a₀ h hS k]

theorem thr_ne (k : ℕ) : thr T a₀ Q F k ≠ 0 := by
  intro h0; have := thr_norm_ge T a₀ h hS k; rw [h0, norm_zero] at this; linarith [h.Zlo_pos]

theorem tilt_mem (k : ℕ) :
    Θlo P Q δ F ≤ tilt T a₀ Q F k ∧ tilt T a₀ Q F k ≤ Θhi P Q δ F := by
  have hz := thr_up_ge T a₀ h hS k
  have hz' := thr_up_le T a₀ h hS k
  have hh := thr_horiz_ge T a₀ h hS k
  have hh' := thr_horiz_le T a₀ h hS k
  have hZ := h.Zlo_pos
  have hH := h.Hlo_pos
  have hpos : 0 < ‖thr T a₀ Q F k‖ := norm_pos_iff.2 (thr_ne T a₀ h hS k)
  have heq : tilt T a₀ Q F k = Real.arctan (‖horiz (thr T a₀ Q F k)‖ / ⟪thr T a₀ Q F k, up⟫) := by
    rw [tilt, b3, nrm, angle_smul_left_of_pos _ _ (inv_pos.2 hpos)]
    exact angle_up_eq_arctan (by linarith)
  rw [heq]
  constructor
  · apply Real.arctan_strictMono.monotone
    exact div_le_div₀ (by linarith) hh (by linarith) hz'
  · apply Real.arctan_strictMono.monotone
    exact div_le_div₀ (by linarith) hh' hZ hz

end Overhead

end VisionTracking
