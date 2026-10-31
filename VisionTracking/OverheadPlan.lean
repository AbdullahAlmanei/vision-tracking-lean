import VisionTracking.Budget
import VisionTracking.SteadyFormation

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

theorem H0_nonneg (F : FIR) : 0 ≤ F.H0 := Finset.sum_nonneg fun i _ => abs_nonneg _
theorem H1_nonneg (F : FIR) : 0 ≤ F.H1 := Finset.sum_nonneg fun i _ => by positivity
theorem TV_nonneg (F : FIR) : 0 ≤ F.TV :=
  add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _)

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


theorem vP_succ (k : ℕ) : vP T a₀ F (k + 1) = vP T a₀ F k + δ • F.planAcc T a₀ k :=
  F.planVel_succ T a₀ h.δ_pos.ne' k

theorem vP_step_le (k : ℕ) : ‖vP T a₀ F (k + 1) - vP T a₀ F k‖ ≤ δ * (P.Amax + εD P δ F) := by
  rw [vP_succ T a₀ h hS, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg h.δ_pos.le]
  exact mul_le_mul_of_nonneg_left (planAcc_norm_le T a₀ h hS k) h.δ_pos.le

theorem thr_step (k : ℕ) : ‖thr T a₀ Q F (k + 1) - thr T a₀ Q F k‖ ≤ dT P Q δ F := by
  have hsplit : thr T a₀ Q F (k + 1) - thr T a₀ Q F k
      = (F.planAcc T a₀ (k + 1) - F.planAcc T a₀ k)
        + Q.drag • (‖vP T a₀ F (k + 1)‖ • vP T a₀ F (k + 1) - ‖vP T a₀ F k‖ • vP T a₀ F k) := by
    unfold thr; module
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 := F.planAcc_step T a₀ h.δ_pos hS k
  have h2 := norm_dragMap_sub_le (vP T a₀ F (k + 1)) (vP T a₀ F k)
  have h3 := vP_step_le T a₀ h hS k
  have h4 := vP_norm_le T a₀ h hS (k + 1)
  have h5 := vP_norm_le T a₀ h hS k
  have hc := Q.drag_pos
  have hδ := h.δ_pos
  have hA : 0 ≤ P.Amax + εD P δ F := by
    unfold TargetParams.Amax εD
    have := P.aTan_nonneg; have := P.turnRadius_pos; have := H1_nonneg F; have := P.jerk_nonneg
    positivity
  rw [norm_smul, Real.norm_of_nonneg hc.le]
  have h6 : (‖vP T a₀ F (k + 1)‖ + ‖vP T a₀ F k‖) * ‖vP T a₀ F (k + 1) - vP T a₀ F k‖
      ≤ (2 * Vb P δ F) * (δ * (P.Amax + εD P δ F)) :=
    mul_le_mul (by linarith) h3 (norm_nonneg _) (by linarith [norm_nonneg (vP T a₀ F k)])
  have := mul_le_mul_of_nonneg_left (h2.trans h6) hc.le
  unfold dT; nlinarith

theorem thr_second (k : ℕ) :
    ‖thr T a₀ Q F (k + 2) - 2 • thr T a₀ Q F (k + 1) + thr T a₀ Q F k‖ ≤ d2T P Q δ F := by
  have hsplit : thr T a₀ Q F (k + 2) - 2 • thr T a₀ Q F (k + 1) + thr T a₀ Q F k
      = (F.planAcc T a₀ (k + 2) - 2 • F.planAcc T a₀ (k + 1) + F.planAcc T a₀ k)
        + Q.drag • (‖vP T a₀ F (k + 2)‖ • vP T a₀ F (k + 2)
          - 2 • (‖vP T a₀ F (k + 1)‖ • vP T a₀ F (k + 1)) + ‖vP T a₀ F k‖ • vP T a₀ F k) := by
    unfold thr; module
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 := F.planAcc_second T a₀ h.δ_pos hS k
  have h2 := norm_dragMap_second_le (a := vP T a₀ F k) (c := vP T a₀ F (k + 2))
    (vP_ne T a₀ h hS (k + 1))
  have hd2 : vP T a₀ F (k + 2) - 2 • vP T a₀ F (k + 1) + vP T a₀ F k
      = δ • (F.planAcc T a₀ (k + 1) - F.planAcc T a₀ k) := by
    rw [show k + 2 = (k + 1) + 1 from rfl, vP_succ T a₀ h hS (k + 1), vP_succ T a₀ h hS k]; module
  have h3 : ‖vP T a₀ F (k + 2) - 2 • vP T a₀ F (k + 1) + vP T a₀ F k‖ ≤ δ * (F.H0 * δ * P.jerk) := by
    rw [hd2, norm_smul, Real.norm_of_nonneg h.δ_pos.le]
    exact mul_le_mul_of_nonneg_left (F.planAcc_step T a₀ h.δ_pos hS k) h.δ_pos.le
  have h4 := vP_step_le T a₀ h hS (k + 1)
  have h5 := vP_step_le T a₀ h hS k
  have h6 := vP_norm_le T a₀ h hS (k + 1)
  have hc := Q.drag_pos
  have hδ := h.δ_pos
  have hA : 0 ≤ P.Amax + εD P δ F := by
    unfold TargetParams.Amax εD
    have := P.aTan_nonneg; have := P.turnRadius_pos; have := H1_nonneg F; have := P.jerk_nonneg
    positivity
  have h4' : ‖vP T a₀ F (k + 2) - vP T a₀ F (k + 1)‖ ^ 2 ≤ (δ * (P.Amax + εD P δ F)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h4 2
  have h5' : ‖vP T a₀ F (k + 1) - vP T a₀ F k‖ ^ 2 ≤ (δ * (P.Amax + εD P δ F)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h5 2
  have h7 : 2 * ‖vP T a₀ F (k + 1)‖ * ‖vP T a₀ F (k + 2) - 2 • vP T a₀ F (k + 1) + vP T a₀ F k‖
      ≤ 2 * Vb P δ F * (δ * (F.H0 * δ * P.jerk)) := by
    have := H0_nonneg F; have := P.jerk_nonneg
    apply mul_le_mul (by linarith) h3 (norm_nonneg _) (by linarith [norm_nonneg (vP T a₀ F (k+1))])
  rw [norm_smul, Real.norm_of_nonneg hc.le]
  have hb : ‖‖vP T a₀ F (k + 2)‖ • vP T a₀ F (k + 2) - 2 • (‖vP T a₀ F (k + 1)‖ • vP T a₀ F (k + 1))
      + ‖vP T a₀ F k‖ • vP T a₀ F k‖ ≤ 2 * Vb P δ F * F.H0 * δ ^ 2 * P.jerk
        + 4 * δ ^ 2 * (P.Amax + εD P δ F) ^ 2 := by
    refine h2.trans ?_
    nlinarith
  have := mul_le_mul_of_nonneg_left hb hc.le
  unfold d2T; nlinarith

theorem b3_unit (k : ℕ) : ‖b3 T a₀ Q F k‖ = 1 := by
  unfold b3 nrm; exact norm_smul_inv_norm (thr_ne T a₀ h hS k)

theorem b3_step (k : ℕ) : ‖b3 T a₀ Q F (k + 1) - b3 T a₀ Q F k‖ ≤ D3 P Q δ F := by
  have := norm_nrm_sub_le h.Zlo_pos (thr_norm_ge T a₀ h hS (k + 1)) (b := thr T a₀ Q F k)
  refine this.trans ?_
  unfold D3
  exact div_le_div_of_nonneg_right (by linarith [thr_step T a₀ h hS k]) h.Zlo_pos.le

theorem b3_second (k : ℕ) :
    ‖b3 T a₀ Q F (k + 2) - 2 • b3 T a₀ Q F (k + 1) + b3 T a₀ Q F k‖ ≤ D3' P Q δ F := by
  have := norm_nrm_second_le h.Zlo_pos (thr_norm_ge T a₀ h hS k) (thr_norm_ge T a₀ h hS (k + 1))
    (thr_norm_ge T a₀ h hS (k + 2))
  refine this.trans ?_
  have hZ := h.Zlo_pos
  have s1 := thr_step T a₀ h hS (k + 1)
  have s0 := thr_step T a₀ h hS k
  have s2 := thr_second T a₀ h hS k
  have e1 : ‖thr T a₀ Q F (k + 2) - thr T a₀ Q F (k + 1)‖ ^ 2 ≤ dT P Q δ F ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) s1 2
  have e0 : ‖thr T a₀ Q F (k + 1) - thr T a₀ Q F k‖ ^ 2 ≤ dT P Q δ F ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) s0 2
  unfold D3'
  have f1 : 2 * ‖thr T a₀ Q F (k + 2) - 2 • thr T a₀ Q F (k + 1) + thr T a₀ Q F k‖ / Zlo P Q δ F
      ≤ 2 * d2T P Q δ F / Zlo P Q δ F := div_le_div_of_nonneg_right (by linarith) hZ.le
  have f2 : 3 * (‖thr T a₀ Q F (k + 2) - thr T a₀ Q F (k + 1)‖ ^ 2
      + ‖thr T a₀ Q F (k + 1) - thr T a₀ Q F k‖ ^ 2) / Zlo P Q δ F ^ 2
      ≤ 6 * dT P Q δ F ^ 2 / Zlo P Q δ F ^ 2 := div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

theorem raw_norm_ge (k : ℕ) : mh P Q δ F ≤ ‖downhillRaw (b3 T a₀ Q F k)‖ := by
  have hpos : 0 < ‖thr T a₀ Q F k‖ := norm_pos_iff.2 (thr_ne T a₀ h hS k)
  have hsq := norm_downhillRaw_sq (b3_unit T a₀ h hS k)
  have hin : ⟪b3 T a₀ Q F k, up⟫ = ⟪thr T a₀ Q F k, up⟫ / ‖thr T a₀ Q F k‖ := by
    rw [b3, nrm, real_inner_smul_left]; field_simp
  have hh := norm_horiz_sq (thr T a₀ Q F k)
  have key : ‖downhillRaw (b3 T a₀ Q F k)‖ = ‖horiz (thr T a₀ Q F k)‖ / ‖thr T a₀ Q F k‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), hsq, hin, div_pow, div_pow, hh]
    field_simp
  rw [key, mh]
  exact div_le_div₀ (norm_nonneg _) (thr_horiz_ge T a₀ h hS k) hpos (thr_norm_le T a₀ h hS k)

theorem mh_pos : 0 < mh P Q δ F := by
  unfold mh
  have := h.Hlo_pos
  have : 0 < Fhi P Q δ F := by
    have := thr_norm_le T a₀ h hS 0
    have := thr_norm_ge T a₀ h hS 0
    linarith [h.Zlo_pos]
  positivity

theorem raw_ne (k : ℕ) : downhillRaw (b3 T a₀ Q F k) ≠ 0 := by
  intro h0; have := raw_norm_ge T a₀ h hS k; rw [h0, norm_zero] at this
  linarith [mh_pos T a₀ h hS]

theorem b1_unit (k : ℕ) : ‖b1 T a₀ Q F k‖ = 1 := downhill_unit (raw_ne T a₀ h hS k)

theorem b13_orth (k : ℕ) : ⟪b1 T a₀ Q F k, b3 T a₀ Q F k⟫ = 0 :=
  downhill_orth (b3_unit T a₀ h hS k)

theorem b1_step (k : ℕ) : ‖b1 T a₀ Q F (k + 1) - b1 T a₀ Q F k‖ ≤ D1b P Q δ F := by
  have := norm_nrm_sub_le (mh_pos T a₀ h hS) (raw_norm_ge T a₀ h hS (k + 1))
    (b := downhillRaw (b3 T a₀ Q F k))
  refine this.trans ?_
  have hr := norm_downhillRaw_sub_le (b3_unit T a₀ h hS k) (b3_unit T a₀ h hS (k + 1))
  have hs := b3_step T a₀ h hS k
  unfold D1b
  exact div_le_div_of_nonneg_right (by linarith) (mh_pos T a₀ h hS).le

theorem b1_second (k : ℕ) :
    ‖b1 T a₀ Q F (k + 2) - 2 • b1 T a₀ Q F (k + 1) + b1 T a₀ Q F k‖ ≤ D1b' P Q δ F := by
  have hm := mh_pos T a₀ h hS
  have := norm_nrm_second_le hm (raw_norm_ge T a₀ h hS k) (raw_norm_ge T a₀ h hS (k + 1))
    (raw_norm_ge T a₀ h hS (k + 2))
  refine this.trans ?_
  have r2 := norm_downhillRaw_second_le (a := b3 T a₀ Q F k) (b3_unit T a₀ h hS (k + 1))
    (b3_unit T a₀ h hS (k + 2))
  have r1 := norm_downhillRaw_sub_le (b3_unit T a₀ h hS (k + 1)) (b3_unit T a₀ h hS (k + 2))
  have r0 := norm_downhillRaw_sub_le (b3_unit T a₀ h hS k) (b3_unit T a₀ h hS (k + 1))
  have s1 := b3_step T a₀ h hS (k + 1)
  have s0 := b3_step T a₀ h hS k
  have s2 := b3_second T a₀ h hS k
  have hD3 : 0 ≤ D3 P Q δ F := (norm_nonneg _).trans s0
  rw [norm_sub_rev (b3 T a₀ Q F (k + 1))] at r2
  have q2 : ‖downhillRaw (b3 T a₀ Q F (k + 2)) - 2 • downhillRaw (b3 T a₀ Q F (k + 1))
      + downhillRaw (b3 T a₀ Q F k)‖ ≤ 2 * D3' P Q δ F + 2 * D3 P Q δ F ^ 2 := by
    refine r2.trans ?_
    have := mul_le_mul s0 (add_le_add s1 s0) (by positivity) hD3
    rw [norm_sub_rev] at this
    nlinarith
  have q1 : ‖downhillRaw (b3 T a₀ Q F (k + 2)) - downhillRaw (b3 T a₀ Q F (k + 1))‖ ^ 2
      ≤ (2 * D3 P Q δ F) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  have q0 : ‖downhillRaw (b3 T a₀ Q F (k + 1)) - downhillRaw (b3 T a₀ Q F k)‖ ^ 2
      ≤ (2 * D3 P Q δ F) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  unfold D1b'
  have f1 : 2 * ‖downhillRaw (b3 T a₀ Q F (k + 2)) - 2 • downhillRaw (b3 T a₀ Q F (k + 1))
      + downhillRaw (b3 T a₀ Q F k)‖ / mh P Q δ F
      ≤ (4 * D3' P Q δ F + 4 * D3 P Q δ F ^ 2) / mh P Q δ F :=
    div_le_div_of_nonneg_right (by linarith) hm.le
  have f2 : 3 * (‖downhillRaw (b3 T a₀ Q F (k + 2)) - downhillRaw (b3 T a₀ Q F (k + 1))‖ ^ 2
      + ‖downhillRaw (b3 T a₀ Q F (k + 1)) - downhillRaw (b3 T a₀ Q F k)‖ ^ 2) / mh P Q δ F ^ 2
      ≤ 24 * D3 P Q δ F ^ 2 / mh P Q δ F ^ 2 :=
    div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  linarith

theorem b2_unit (k : ℕ) : ‖b2 T a₀ Q F k‖ = 1 := by
  unfold b2
  exact norm_cross_of_orthonormal (b3_unit T a₀ h hS k) (b1_unit T a₀ h hS k)
    (by rw [real_inner_comm]; exact b13_orth T a₀ h hS k)

theorem b12_orth (k : ℕ) : ⟪b1 T a₀ Q F k, b2 T a₀ Q F k⟫ = 0 := inner_cross_right _ _

theorem cross_b12 (k : ℕ) : cross (b1 T a₀ Q F k) (b2 T a₀ Q F k) = b3 T a₀ Q F k :=
  cross_cross_self (b1_unit T a₀ h hS k) (b13_orth T a₀ h hS k)

theorem b2_step (k : ℕ) :
    ‖b2 T a₀ Q F (k + 1) - b2 T a₀ Q F k‖ ≤ D3 P Q δ F + D1b P Q δ F := by
  unfold b2
  rw [cross_sub_cross]
  refine (norm_add_le _ _).trans ?_
  have e1 := norm_cross_le (b3 T a₀ Q F (k + 1) - b3 T a₀ Q F k) (b1 T a₀ Q F (k + 1))
  have e2 := norm_cross_le (b3 T a₀ Q F k) (b1 T a₀ Q F (k + 1) - b1 T a₀ Q F k)
  rw [b1_unit T a₀ h hS] at e1; rw [b3_unit T a₀ h hS] at e2
  linarith [b3_step T a₀ h hS k, b1_step T a₀ h hS k]

theorem b2_second (k : ℕ) :
    ‖b2 T a₀ Q F (k + 2) - 2 • b2 T a₀ Q F (k + 1) + b2 T a₀ Q F k‖
      ≤ D3' P Q δ F + 2 * D3 P Q δ F * D1b P Q δ F + D1b' P Q δ F := by
  unfold b2
  rw [cross_second]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · have := norm_cross_le (b3 T a₀ Q F (k + 2) - 2 • b3 T a₀ Q F (k + 1) + b3 T a₀ Q F k)
      (b1 T a₀ Q F (k + 2))
    rw [b1_unit T a₀ h hS, mul_one] at this
    exact this.trans (b3_second T a₀ h hS k)
  · rw [two_smul]
    refine (norm_add_le _ _).trans ?_
    have := norm_cross_le (b3 T a₀ Q F (k + 1) - b3 T a₀ Q F k)
      (b1 T a₀ Q F (k + 2) - b1 T a₀ Q F (k + 1))
    have := mul_le_mul (b3_step T a₀ h hS k) (b1_step T a₀ h hS (k + 1)) (norm_nonneg _)
      ((norm_nonneg _).trans (b3_step T a₀ h hS k))
    linarith
  · have := norm_cross_le (b3 T a₀ Q F k)
      (b1 T a₀ Q F (k + 2) - 2 • b1 T a₀ Q F (k + 1) + b1 T a₀ Q F k)
    rw [b3_unit T a₀ h hS, one_mul] at this
    exact this.trans (b1_second T a₀ h hS k)

end Overhead

end VisionTracking
