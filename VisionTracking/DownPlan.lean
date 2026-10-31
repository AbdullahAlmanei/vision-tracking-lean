import VisionTracking.Budget2
import VisionTracking.OverheadPlan
import VisionTracking.RotPlan

/-!
# The yaw-free overhead formation (down-looking camera, transported frame)

The drone flies the filtered target path offset by `d` straight up. Its thrust axis
follows the planned thrust direction `n_k = T_k/‖T_k‖`, and its body frame is
parallel transported by the minimal rotations `minRot n_k n_{k+1}`, so it never yaws.
The camera is fixed straight down the thrust axis (`η = -π/2`).
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

theorem cross_anticomm' (a b : E3) : cross a b = -cross b a := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring

theorem cross_mid (a b c : E3) : cross b c - cross a b = cross b (c - 2 • b + a) := by
  ext i; fin_cases i <;> simp [cross, crossProduct, two_smul] <;> ring

theorem G_nonneg (F : FIR) : 0 ≤ F.G1 ∧ 0 ≤ F.G2 ∧ 0 ≤ F.G3 :=
  ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    Finset.sum_nonneg fun _ _ => abs_nonneg _⟩

/-- An explicit unit vector orthogonal to a unit `n` (Gram–Schmidt on `e₁`, else `e₂`). -/
noncomputable def orthUnit (n : E3) : E3 :=
  if ex - ⟪ex, n⟫ • n = 0 then nrm (ey - ⟪ey, n⟫ • n) else nrm (ex - ⟪ex, n⟫ • n)

theorem orthUnit_spec {n : E3} (hn : ‖n‖ = 1) : ‖orthUnit n‖ = 1 ∧ ⟪orthUnit n, n⟫ = 0 := by
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have orth : ∀ e : E3, ⟪e - ⟪e, n⟫ • n, n⟫ = 0 := fun e => by
    rw [inner_sub_left, real_inner_smul_left, hnn]; ring
  have hex : ‖ex‖ = 1 := by simp [ex]
  have hey : ‖ey‖ = 1 := by simp [ey]
  have hexy : ⟪ex, ey⟫ = 0 := by simp [inner_eq_coords, ex, ey]
  unfold orthUnit
  split_ifs with h1
  · by_cases h2 : ey - ⟪ey, n⟫ • n = 0
    · exfalso
      have e1 : ex = ⟪ex, n⟫ • n := sub_eq_zero.1 h1
      have e2 : ey = ⟪ey, n⟫ • n := sub_eq_zero.1 h2
      have a1 : |⟪ex, n⟫| = 1 := by
        have := congrArg norm e1; rwa [hex, norm_smul, hn, mul_one, Real.norm_eq_abs, eq_comm] at this
      have a2 : |⟪ey, n⟫| = 1 := by
        have := congrArg norm e2; rwa [hey, norm_smul, hn, mul_one, Real.norm_eq_abs, eq_comm] at this
      have : ⟪ex, ey⟫ = ⟪ex, n⟫ * ⟪ey, n⟫ := by
        rw [e1, e2, real_inner_smul_left, real_inner_smul_right, hnn]
        rw [← e1, ← e2]; ring
      have hp : ⟪ex, n⟫ * ⟪ey, n⟫ = 0 := by rw [← this, hexy]
      have := congrArg abs hp
      rw [abs_mul, a1, a2, abs_zero] at this
      norm_num at this
    · exact ⟨by unfold nrm; exact norm_smul_inv_norm h2,
        by unfold nrm; rw [real_inner_smul_left, orth, mul_zero]⟩
  · exact ⟨by unfold nrm; exact norm_smul_inv_norm h1,
      by unfold nrm; rw [real_inner_smul_left, orth, mul_zero]⟩

namespace Down

open Budget2 Overhead

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ} {F : FIR} {d : ℝ}
  (T : TargetTraj P δ) (a₀ : E3)

/-- Planned thrust direction. -/
noncomputable def n (Q : QuadParams) (F : FIR) (k : ℕ) : E3 := nrm (thr T a₀ Q F k)
/-- Transport rotation vector. -/
noncomputable def ω (Q : QuadParams) (F : FIR) (k : ℕ) : E3 :=
  minRot (n T a₀ Q F k) (n T a₀ Q F (k + 1))

variable (h : MasterIneq2 P Q C δ F d) (hS : T.StartsAt (T.p 0) (T.v 0) a₀)
include h hS

theorem vP_err (k : ℕ) : ‖vP T a₀ F k - T.v k‖ ≤ εV P δ F :=
  F.planVel_err_sharp T a₀ h.δ_pos hS k

theorem vP_norm_le (k : ℕ) : ‖vP T a₀ F k‖ ≤ Vb P δ F := by
  have h1 := vP_err T a₀ h hS k
  have h2 := norm_le_insert' (vP T a₀ F k) (T.v k)
  have h3 := T.speed_le k
  unfold Vb; linarith

theorem vP_ne (k : ℕ) : vP T a₀ F k ≠ 0 := by
  intro h0
  have h1 := vP_err T a₀ h hS k
  have h2 := norm_sub_norm_le (T.v k) (vP T a₀ F k)
  rw [norm_sub_rev, h0, norm_zero] at h2
  rw [h0, zero_sub, norm_neg] at h1
  have h3 := T.speed_ge k
  linarith [h.εV_lt]

theorem acc_err (k : ℕ) :
    ‖F.planAcc T a₀ k - δ⁻¹ • (T.v (k + 1) - T.v k)‖ ≤ εD P δ F := by
  have := F.planAcc_err_sharp T a₀ h.δ_pos hS k
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
    unfold εV; have := (G_nonneg F).2.1; have := P.jerk_nonneg; have := h.δ_pos; positivity
  rw [norm_smul, Real.norm_of_nonneg hc.le]
  have h6 : (‖vP T a₀ F k‖ + ‖T.v k‖) * ‖vP T a₀ F k - T.v k‖
      ≤ (2 * P.vMax + εV P δ F) * εV P δ F := by
    apply mul_le_mul _ h3 (norm_nonneg _) (by linarith [P.vMin_pos, P.vMin_le_vMax])
    unfold Vb at h4; linarith
  have := mul_le_mul_of_nonneg_left (h2.trans h6) hc.le
  unfold εT; nlinarith

theorem thr_up_ge (k : ℕ) : Zlo P Q δ F ≤ ⟪thr T a₀ Q F k, up⟫ := by
  have h1 := thr_err T a₀ h hS k
  have h2 := thrustStar_up_ge_v T Q h.δ_pos k
  have h3 := inner_up_sub_le (thr T a₀ Q F k) (thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)))
  rw [abs_le] at h3
  unfold Zlo; linarith

theorem thr_norm_le (k : ℕ) : ‖thr T a₀ Q F k‖ ≤ Fhi P Q δ F := by
  have h1 := thr_err T a₀ h hS k
  have h2 := thrustStar_norm_le T Q h.δ_pos k
  have h3 := norm_le_insert' (thr T a₀ Q F k) (thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)))
  unfold Fhi; linarith

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

theorem n_unit (k : ℕ) : ‖n T a₀ Q F k‖ = 1 := by
  unfold n nrm; exact norm_smul_inv_norm (thr_ne T a₀ h hS k)

theorem tilt_le (k : ℕ) : angle (n T a₀ Q F k) up ≤ Θhi P Q δ F := by
  have hz := thr_up_ge T a₀ h hS k
  have hh' := thr_horiz_le T a₀ h hS k
  have hZ := h.Zlo_pos
  have hpos : 0 < ‖thr T a₀ Q F k‖ := norm_pos_iff.2 (thr_ne T a₀ h hS k)
  rw [n, nrm, angle_smul_left_of_pos _ _ (inv_pos.2 hpos), angle_up_eq_arctan (by linarith)]
  apply Real.arctan_strictMono.monotone
  exact div_le_div₀ (by linarith [norm_nonneg (horiz (thr T a₀ Q F k))]) hh' hZ hz

theorem vP_step_le (k : ℕ) : ‖vP T a₀ F (k + 1) - vP T a₀ F k‖ ≤ δ * (P.Amax + εD P δ F) := by
  rw [show vP T a₀ F (k + 1) = vP T a₀ F k + δ • F.planAcc T a₀ k from
    F.planVel_succ T a₀ h.δ_pos.ne' k, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg h.δ_pos.le]
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
    have := P.aTan_nonneg; have := P.turnRadius_pos; have := (G_nonneg F).1; have := P.jerk_nonneg
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
  have hs1 : vP T a₀ F (k + 1) = vP T a₀ F k + δ • F.planAcc T a₀ k :=
    F.planVel_succ T a₀ h.δ_pos.ne' k
  have hs2 : vP T a₀ F (k + 2) = vP T a₀ F (k + 1) + δ • F.planAcc T a₀ (k + 1) :=
    F.planVel_succ T a₀ h.δ_pos.ne' (k + 1)
  have hd2 : vP T a₀ F (k + 2) - 2 • vP T a₀ F (k + 1) + vP T a₀ F k
      = δ • (F.planAcc T a₀ (k + 1) - F.planAcc T a₀ k) := by
    rw [hs2, hs1]; module
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
    have := P.aTan_nonneg; have := P.turnRadius_pos; have := (G_nonneg F).1; have := P.jerk_nonneg
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

theorem n_step (k : ℕ) : ‖n T a₀ Q F (k + 1) - n T a₀ Q F k‖ ≤ D3 P Q δ F := by
  refine (norm_nrm_sub_le_sharp h.Zlo_pos (thr_norm_ge T a₀ h hS (k + 1))
    (thr_norm_ge T a₀ h hS k)).trans ?_
  unfold D3
  exact div_le_div_of_nonneg_right (thr_step T a₀ h hS k) h.Zlo_pos.le

theorem n_inner_nonneg (k : ℕ) : 0 ≤ ⟪n T a₀ Q F k, n T a₀ Q F (k + 1)⟫ := by
  rw [inner_unit_eq (n_unit T a₀ h hS k) (n_unit T a₀ h hS (k + 1)), norm_sub_rev]
  have := n_step T a₀ h hS k
  have h1 := h.D3_lt
  have := pow_le_pow_left₀ (norm_nonneg _) this 2
  nlinarith [norm_nonneg (n T a₀ Q F (k + 1) - n T a₀ Q F k)]

theorem sigma_norm_le (k : ℕ) : ‖cross (n T a₀ Q F k) (n T a₀ Q F (k + 1))‖ ≤ D3 P Q δ F := by
  have e : cross (n T a₀ Q F k) (n T a₀ Q F (k + 1))
      = cross (n T a₀ Q F k) (n T a₀ Q F (k + 1) - n T a₀ Q F k) := by
    rw [show n T a₀ Q F (k + 1) - n T a₀ Q F k = n T a₀ Q F (k + 1) + (-1 : ℝ) • n T a₀ Q F k by
      module, cross_add_right', cross_smul_right', cross_self', smul_zero, add_zero]
  rw [e]
  refine (norm_cross_le _ _).trans ?_
  rw [n_unit T a₀ h hS, one_mul]; exact n_step T a₀ h hS k

theorem sigma_step_le (k : ℕ) :
    ‖cross (n T a₀ Q F (k + 1)) (n T a₀ Q F (k + 2)) - cross (n T a₀ Q F k) (n T a₀ Q F (k + 1))‖
      ≤ X P Q δ F := by
  rw [cross_mid]
  refine (norm_cross_nrm_second_le h.Zlo_pos (thr_norm_ge T a₀ h hS k)
    (thr_norm_ge T a₀ h hS (k + 1)) (thr_norm_ge T a₀ h hS (k + 2))).trans ?_
  have s0 := thr_step T a₀ h hS k
  have s1 := thr_step T a₀ h hS (k + 1)
  have s2 := thr_second T a₀ h hS k
  have hZ := h.Zlo_pos
  have e1 := pow_le_pow_left₀ (norm_nonneg _) s1 2
  have e0 := pow_le_pow_left₀ (norm_nonneg _) s0 2
  unfold X
  have f1 : ‖thr T a₀ Q F (k + 2) - 2 • thr T a₀ Q F (k + 1) + thr T a₀ Q F k‖ / Zlo P Q δ F
      ≤ d2T P Q δ F / Zlo P Q δ F := div_le_div_of_nonneg_right s2 hZ.le
  have f2 : (‖thr T a₀ Q F (k + 2) - thr T a₀ Q F (k + 1)‖ ^ 2
      + ‖thr T a₀ Q F (k + 1) - thr T a₀ Q F k‖ ^ 2) / Zlo P Q δ F ^ 2
      ≤ 2 * dT P Q δ F ^ 2 / Zlo P Q δ F ^ 2 := div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

theorem ω_norm_le (k : ℕ) : ‖ω T a₀ Q F k‖ ≤ θm P Q δ F := by
  have hσ := sigma_norm_le T a₀ h hS k
  have hD0 : 0 ≤ D3 P Q δ F := (norm_nonneg _).trans (n_step T a₀ h hS k)
  have hD := h.D3_lt
  have hs : 0 < √(1 - D3 P Q δ F ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  refine (norm_psiVec_le hσ h.D3_lt).trans ?_
  unfold θm; exact div_le_div_of_nonneg_right hσ hs.le

theorem ω_step_le (k : ℕ) : ‖ω T a₀ Q F (k + 1) - ω T a₀ Q F k‖ ≤ dω P Q δ F := by
  have hD0 : 0 ≤ D3 P Q δ F := (norm_nonneg _).trans (n_step T a₀ h hS k)
  have hD := h.D3_lt
  have hs : 0 < √(1 - D3 P Q δ F ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  refine (norm_psiVec_sub_le (sigma_norm_le T a₀ h hS (k + 1)) (sigma_norm_le T a₀ h hS k)
    h.D3_lt).trans ?_
  unfold dω
  apply div_le_div_of_nonneg_right _ hs.le
  linarith [sigma_step_le T a₀ h hS k]

omit h hS in
/-- The parallel-transported forward axis. -/
noncomputable def b1 (Q : QuadParams) (F : FIR) : ℕ → E3
  | 0 => orthUnit (n T a₀ Q F 0)
  | k + 1 => rotate (ω T a₀ Q F k) (b1 Q F k)

omit h hS in
noncomputable def b2 (Q : QuadParams) (F : FIR) (k : ℕ) : E3 := cross (n T a₀ Q F k) (b1 T a₀ Q F k)

theorem rotate_ω_n (k : ℕ) : rotate (ω T a₀ Q F k) (n T a₀ Q F k) = n T a₀ Q F (k + 1) :=
  rotate_minRot (n_unit T a₀ h hS k) (n_unit T a₀ h hS (k + 1)) (n_inner_nonneg T a₀ h hS k)

theorem b1_spec (k : ℕ) : ‖b1 T a₀ Q F k‖ = 1 ∧ ⟪b1 T a₀ Q F k, n T a₀ Q F k⟫ = 0 := by
  induction k with
  | zero => exact orthUnit_spec (n_unit T a₀ h hS 0)
  | succ k ih =>
    refine ⟨by rw [b1, norm_rotate]; exact ih.1, ?_⟩
    rw [b1, ← rotate_ω_n T a₀ h hS k, inner_rotate]; exact ih.2

theorem b2_unit (k : ℕ) : ‖b2 T a₀ Q F k‖ = 1 :=
  norm_cross_of_orthonormal (n_unit T a₀ h hS k) (b1_spec T a₀ h hS k).1
    (by rw [real_inner_comm]; exact (b1_spec T a₀ h hS k).2)

/-- The overhead formation with the transported frame, as a rotation plan. -/
noncomputable def rp : RotPlan Q C δ where
  x k := F.planPos T a₀ (d • up) k
  v k := vP T a₀ F k
  b₁ := b1 T a₀ Q F
  b₂ := b2 T a₀ Q F
  η _ := -(π / 2)
  ω := ω T a₀ Q F
  steps := F.planPos_succ T a₀ (d • up)
  b₁_unit k := (b1_spec T a₀ h hS k).1
  b₂_unit := b2_unit T a₀ h hS
  b₁₂_orth k := inner_cross_right _ _
  evolve k := ⟨rfl, by
    simp only [b2, b1]; rw [← rotate_ω_n T a₀ h hS k, rotate_cross]⟩

theorem rp_b₃ (k : ℕ) : (rp T a₀ h hS).b₃ k = n T a₀ Q F k :=
  cross_cross_self (b1_spec T a₀ h hS k).1 (b1_spec T a₀ h hS k).2

theorem rp_thrust (k : ℕ) : (rp T a₀ h hS).thrust k = thr T a₀ Q F k := by
  simp only [RotPlan.thrust, rp]
  rw [show vP T a₀ F (k + 1) = vP T a₀ F k + δ • F.planAcc T a₀ k from
    F.planVel_succ T a₀ h.δ_pos.ne' k, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ h.δ_pos.ne', one_smul]
  rfl

theorem rp_hdir (k : ℕ) :
    (rp T a₀ h hS).thrust k = ‖(rp T a₀ h hS).thrust k‖ • (rp T a₀ h hS).b₃ k := by
  rw [rp_thrust, rp_b₃, n, nrm, smul_smul, mul_inv_cancel₀
    (norm_ne_zero_iff.2 (thr_ne T a₀ h hS k)), one_smul]

theorem rp_rate_le (k : ℕ) : ‖(rp T a₀ h hS).rate k‖ ≤ Ωmax P Q δ F := by
  rw [RotPlan.norm_rate _ h.δ_pos]
  exact div_le_div_of_nonneg_right (ω_norm_le T a₀ h hS k) h.δ_pos.le

theorem rp_rate_sub_le (k : ℕ) :
    ‖(rp T a₀ h hS).rate (k + 1) - (rp T a₀ h hS).rate k‖ ≤ dΩ P Q δ F := by
  refine (RotPlan.norm_rate_sub_le _ h.δ_pos k).trans ?_
  apply div_le_div_of_nonneg_right _ h.δ_pos.le
  have a1 := ω_step_le T a₀ h hS k
  have a2 := ω_norm_le T a₀ h hS k
  have a3 := ω_norm_le T a₀ h hS (k + 1)
  have := mul_le_mul a2 a3 (norm_nonneg _) ((norm_nonneg _).trans a2)
  change ‖ω T a₀ Q F (k + 1) - ω T a₀ Q F k‖ + 3 * (‖ω T a₀ Q F k‖ * ‖ω T a₀ Q F (k + 1)‖)
    ≤ dω P Q δ F + 3 * θm P Q δ F ^ 2
  nlinarith

theorem rp_rate_yaw (k : ℕ) : ((rp T a₀ h hS).rate k).ofLp 2 = 0 := by
  rw [RotPlan.rate_yaw, rp_b₃]
  change δ⁻¹ * ⟪n T a₀ Q F k, ω T a₀ Q F k⟫ = 0
  rw [real_inner_comm, ω, inner_minRot_left, mul_zero]

theorem rp_torque_le (k : ℕ) : ‖(rp T a₀ h hS).torque k‖ ≤ τrp P Q δ F := by
  unfold RotPlan.torque τrp
  have hJ : 0 ≤ Budget.Jmax Q := le_trans Q.Jx_pos.le (le_max_left _ _)
  have hδ := h.δ_pos
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (inertia_norm_le Q _).trans ?_
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hδ.le, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hJ
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (rp_rate_sub_le T a₀ h hS k) hδ.le
  · refine (norm_cross_le _ _).trans ?_
    have h1 := rp_rate_le T a₀ h hS k
    have h2 := inertia_norm_le Q ((rp T a₀ h hS).rate k)
    have h0 := norm_nonneg ((rp T a₀ h hS).rate k)
    calc ‖(rp T a₀ h hS).rate k‖ * ‖Q.inertia ((rp T a₀ h hS).rate k)‖
        ≤ ‖(rp T a₀ h hS).rate k‖ * (Budget.Jmax Q * ‖(rp T a₀ h hS).rate k‖) :=
          mul_le_mul_of_nonneg_left h2 h0
      _ ≤ Budget.Jmax Q * Ωmax P Q δ F ^ 2 := by nlinarith [mul_le_mul h1 h1 h0 (h0.trans h1)]

theorem rp_torque_yaw_le (k : ℕ) : |((rp T a₀ h hS).torque k).ofLp 2| ≤ τyaw P Q δ F := by
  set Ω := (rp T a₀ h hS).rate k
  have hy0 := rp_rate_yaw T a₀ h hS k
  have hy1 := rp_rate_yaw T a₀ h hS (k + 1)
  have e : ((rp T a₀ h hS).torque k).ofLp 2 = (Q.Jy - Q.Jx) * (Ω.ofLp 0 * Ω.ofLp 1) := by
    simp only [RotPlan.torque, WithLp.ofLp_add, Pi.add_apply, cross_ofLp_two]
    simp [QuadParams.inertia, hy0, hy1, Ω]
    ring
  rw [e, abs_mul]
  have a0 := abs_coord_le Ω 0
  have a1 := abs_coord_le Ω 1
  have hr := rp_rate_le T a₀ h hS k
  have : |Ω.ofLp 0 * Ω.ofLp 1| ≤ Ωmax P Q δ F ^ 2 := by
    rw [abs_mul]
    have := mul_le_mul (a0.trans hr) (a1.trans hr) (abs_nonneg _) ((norm_nonneg _).trans hr)
    nlinarith
  unfold τyaw
  exact mul_le_mul_of_nonneg_left this (abs_nonneg _)

theorem rp_mix (k : ℕ) :
    MixerOK Q (Q.mass * ‖(rp T a₀ h hS).thrust k‖) ((rp T a₀ h hS).torque k) := by
  have hτ := rp_torque_le T a₀ h hS k
  have hy := rp_torque_yaw_le T a₀ h hS k
  have hm := Q.mass_pos
  have hL : 0 < 2 * Q.arm := by linarith [Q.arm_pos]
  have hk : 0 < 4 * Q.kYaw := by linarith [Q.kYaw_pos]
  have hT1 : Zlo P Q δ F ≤ ‖(rp T a₀ h hS).thrust k‖ := by
    rw [rp_thrust]; exact thr_norm_ge T a₀ h hS k
  have hT2 : ‖(rp T a₀ h hS).thrust k‖ ≤ Fhi P Q δ F := by
    rw [rp_thrust]; exact thr_norm_le T a₀ h hS k
  have b0 : |((rp T a₀ h hS).torque k).ofLp 0| / (2 * Q.arm) ≤ τrp P Q δ F / (2 * Q.arm) :=
    div_le_div_of_nonneg_right ((abs_coord_le _ 0).trans hτ) hL.le
  have b1' : |((rp T a₀ h hS).torque k).ofLp 1| / (2 * Q.arm) ≤ τrp P Q δ F / (2 * Q.arm) :=
    div_le_div_of_nonneg_right ((abs_coord_le _ 1).trans hτ) hL.le
  have b2' : |((rp T a₀ h hS).torque k).ofLp 2| / (4 * Q.kYaw) ≤ τyaw P Q δ F / (4 * Q.kYaw) :=
    div_le_div_of_nonneg_right hy hk.le
  have m1 : Q.mass * Zlo P Q δ F / 4 ≤ Q.mass * ‖(rp T a₀ h hS).thrust k‖ / 4 := by
    have := mul_le_mul_of_nonneg_left hT1 hm.le; linarith
  have m2 : Q.mass * ‖(rp T a₀ h hS).thrust k‖ / 4 ≤ Q.mass * Fhi P Q δ F / 4 := by
    have := mul_le_mul_of_nonneg_left hT2 hm.le; linarith
  have lo := h.mix_lo
  have hi := h.mix_hi
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **The yaw-free overhead trajectory**: a valid rigid-body quadrotor trajectory. -/
noncomputable def traj : QuadTraj Q C δ :=
  QuadTraj.ofRotPlan (rp T a₀ h hS) h.δ_pos.ne' (rp_hdir T a₀ h hS) (rp_mix T a₀ h hS)
    (fun k => by rw [rp_b₃]; exact (tilt_le T a₀ h hS k).trans h.tilt)
    (fun k => (rp_rate_le T a₀ h hS k).trans h.rate)
    (fun k => (vP_norm_le T a₀ h hS k).trans h.speed)
    (fun _ => by show C.hingeLo ≤ -(π / 2); rw [h.cam_down])
    (fun _ => by show -(π / 2) ≤ C.hingeHi; rw [← h.cam_down]; exact C.hingeLo_le)
    (fun _ => by
      show |-(π / 2) - -(π / 2)| ≤ δ * C.hingeRate
      simp only [sub_self, abs_zero]; exact mul_nonneg h.δ_pos.le C.hingeRate_nonneg)

theorem traj_cam (k : ℕ) : (traj T a₀ h hS).cam k = -n T a₀ Q F k := by
  simp only [QuadTraj.cam, traj, QuadTraj.ofRotPlan, frameCam]
  rw [rp_b₃]
  simp [rp, Real.cos_neg, Real.sin_neg]

/-- **Visibility in every frame.** -/
theorem traj_keeps : KeepsInView C P.size (traj T a₀ h hS) T := by
  intro k
  have hρ : ‖F.planPos T a₀ (d • up) k - (T.p k + d • up)‖ ≤ ρ P δ F :=
    F.planPos_err_sharp T a₀ (d • up) h.δ_pos hS k
  have hx : (traj T a₀ h hS).x k = F.planPos T a₀ (d • up) k := rfl
  refine ⟨?_, ?_⟩
  · rw [hx]
    have hsplit : T.p k - F.planPos T a₀ (d • up) k
        = -(F.planPos T a₀ (d • up) k - (T.p k + d • up)) - d • up := by module
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, norm_smul, norm_up', Real.norm_of_nonneg h.d_pos.le, mul_one]
    linarith [h.range]
  · rw [traj_cam]
    have t1 : angle (-n T a₀ Q F k) (-up) ≤ Θhi P Q δ F := by
      rw [angle_neg_neg]; exact tilt_le T a₀ h hS k
    have t2 : angle (-up) (T.p k - (traj T a₀ h hS).x k) ≤ μ P δ F d := by
      rw [hx]
      set e := F.planPos T a₀ (d • up) k - (T.p k + d • up) with he
      have hd := h.d_pos
      have hlos : T.p k - F.planPos T a₀ (d • up) k = d • (-up) + (-e) := by rw [he]; module
      rw [hlos, ← angle_smul_left_of_pos (-up) _ hd]
      have hxn : ‖d • (-up)‖ = d := by
        rw [norm_smul, norm_neg, norm_up', Real.norm_of_nonneg hd.le, mul_one]
      have hlt : ‖-e‖ < ‖d • (-up)‖ := by rw [norm_neg, hxn]; linarith [h.ρ_lt]
      refine (angle_add_le_arcsin hlt).trans ?_
      rw [norm_neg, hxn]
      exact Real.arcsin_le_arcsin (div_le_div_of_nonneg_right hρ hd.le)
    have := angle_le_angle_add_angle (-n T a₀ Q F k) (-up) (T.p k - (traj T a₀ h hS).x k)
    linarith [h.see]

end Down

end VisionTracking
