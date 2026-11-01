import VisionTracking.Budget3
import VisionTracking.TargetLocal

/-!
# The underneath formation: planned quantities at the current speed

The drone flies the filtered target path offset by `d` straight down. This file bounds the
planned thrust `thr`, its direction `n`, the planned heading `ĥ` and the lateral reference
`ℓ = up × ĥ` at a step `j` whose target speed lies in the window `[sLo s, sHi s]`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

namespace Under

open Budget3 Overhead

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ} {F : FIR} {d : ℝ}
  (T : TargetTraj P δ) (a₀ : E3)

/-- Planned thrust direction. -/
noncomputable def nP (Q : QuadParams) (F : FIR) (j : ℕ) : E3 := nrm (thr T a₀ Q F j)
/-- Planned horizontal heading. -/
noncomputable def hP (F : FIR) (j : ℕ) : E3 := nrm (horiz (vP T a₀ F j))
/-- Planned lateral reference. -/
noncomputable def lP (F : FIR) (j : ℕ) : E3 := cross up (hP T a₀ F j)

variable (h : MasterIneq3 P Q C δ F d) (hS : T.StartsSteady (T.p 0) (T.v 0) a₀)
include h hS

theorem vP_err (j : ℕ) : ‖vP T a₀ F j - T.v j‖ ≤ εV P δ F :=
  F.planVel_err_sharp T a₀ h.δ_pos hS.1 j

theorem acc_err (j : ℕ) :
    ‖F.planAcc T a₀ j - δ⁻¹ • (T.v (j + 1) - T.v j)‖ ≤ εD P δ F := by
  have := F.planAcc_err_sharp T a₀ h.δ_pos hS.1 j
  rwa [accExt_natCast] at this

theorem εV_nonneg : 0 ≤ εV P δ F := (norm_nonneg _).trans (vP_err T a₀ h hS 0)
theorem εD_nonneg : 0 ≤ εD P δ F := (norm_nonneg _).trans (acc_err T a₀ h hS 0)

variable {s : ℝ} {j : ℕ} (hw : ‖T.v j‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s))
include hw

omit hS in
theorem acc_le : ‖δ⁻¹ • (T.v (j + 1) - T.v j)‖ ≤ A P δ s := by
  refine (norm_targetAcc_le_loc T h.δ_pos j).trans ?_
  unfold A
  have hn := norm_nonneg (T.v j)
  have : ‖T.v j‖ ^ 2 ≤ sHi P δ s ^ 2 := pow_le_pow_left₀ hn hw.2 2
  have hR := P.turnRadius_pos
  have := div_le_div_of_nonneg_right this hR.le
  linarith

theorem planAcc_le : ‖F.planAcc T a₀ j‖ ≤ A P δ s + εD P δ F := by
  have h1 := acc_err T a₀ h hS j
  have h2 := acc_le T h hw
  have := norm_le_insert' (F.planAcc T a₀ j) (δ⁻¹ • (T.v (j + 1) - T.v j))
  linarith

theorem vP_le : ‖vP T a₀ F j‖ ≤ sHi P δ s + εV P δ F := by
  have h1 := vP_err T a₀ h hS j
  have := norm_le_insert' (vP T a₀ F j) (T.v j)
  linarith [hw.2]


theorem thr_err :
    ‖thr T a₀ Q F j - thrustStar Q (T.v j) (δ⁻¹ • (T.v (j + 1) - T.v j))‖ ≤ εT P Q δ F s := by
  have hsplit : thr T a₀ Q F j - thrustStar Q (T.v j) (δ⁻¹ • (T.v (j + 1) - T.v j))
      = (F.planAcc T a₀ j - δ⁻¹ • (T.v (j + 1) - T.v j))
        + Q.drag • (‖vP T a₀ F j‖ • vP T a₀ F j - ‖T.v j‖ • T.v j) := by
    unfold thr thrustStar; module
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 := acc_err T a₀ h hS j
  have h2 := norm_dragMap_sub_le (vP T a₀ F j) (T.v j)
  have h3 := vP_err T a₀ h hS j
  have h4 := vP_le T a₀ h hS hw
  have hc := Q.drag_pos
  have hεV := εV_nonneg T a₀ h hS
  rw [norm_smul, Real.norm_of_nonneg hc.le]
  have h6 : (‖vP T a₀ F j‖ + ‖T.v j‖) * ‖vP T a₀ F j - T.v j‖
      ≤ (2 * sHi P δ s + εV P δ F) * εV P δ F := by
    apply mul_le_mul _ h3 (norm_nonneg _) (by linarith [norm_nonneg (T.v j), hw.1, hw.2])
    linarith [hw.2]
  have := mul_le_mul_of_nonneg_left (h2.trans h6) hc.le
  unfold εT; nlinarith

theorem thr_up :
    Zlo P Q δ F s ≤ ⟪thr T a₀ Q F j, up⟫ ∧ ⟪thr T a₀ Q F j, up⟫ ≤ Zhi P Q δ F s := by
  have h1 := thr_err T a₀ h hS hw
  obtain ⟨h2, h2'⟩ := thrustStar_up_loc T Q h.δ_pos j
  have h3 := inner_up_sub_le (thr T a₀ Q F j) (thrustStar Q (T.v j) (δ⁻¹ • (T.v (j + 1) - T.v j)))
  rw [abs_le] at h3
  have hv : ‖T.v j‖ ^ 2 ≤ sHi P δ s ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw.2 2
  have hs := sin_climb_nonneg P
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv hs) Q.drag_pos.le
  unfold Zlo Zhi
  constructor <;> nlinarith

theorem thr_norm_le : ‖thr T a₀ Q F j‖ ≤ Thi P Q δ F s ∧
    ‖horiz (thr T a₀ Q F j)‖ ≤ Hhi P Q δ F s := by
  have h1 := thr_err T a₀ h hS hw
  obtain ⟨h2, h2'⟩ := thrustStar_norm_horiz_le T Q j
  have ha := acc_le T h hw
  have hv : ‖T.v j‖ ^ 2 ≤ sHi P δ s ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw.2 2
  have := mul_le_mul_of_nonneg_left hv Q.drag_pos.le
  have h3 := norm_le_insert' (thr T a₀ Q F j) (thrustStar Q (T.v j) (δ⁻¹ • (T.v (j + 1) - T.v j)))
  have h4 := norm_horiz_sub_le (thr T a₀ Q F j) (thrustStar Q (T.v j) (δ⁻¹ • (T.v (j + 1) - T.v j)))
  rw [abs_le] at h4
  unfold Thi Hhi
  constructor <;> linarith

theorem thr_norm_ge : Tlo P Q δ F s ≤ ‖thr T a₀ Q F j‖ := by
  apply max_le
  · have := real_inner_le_norm (thr T a₀ Q F j) up
    rw [norm_up', mul_one] at this
    linarith [(thr_up T a₀ h hS hw).1]
  · -- along the target velocity
    have hvpos : 0 < ‖T.v j‖ := P.vMin_pos.trans_le (T.speed_ge j)
    have h1 := thrustStar_along_v_ge T Q h.δ_pos j
    have h2 := thr_err T a₀ h hS hw
    set Ts := thrustStar Q (T.v j) (δ⁻¹ • (T.v (j + 1) - T.v j))
    have h3 : ⟪thr T a₀ Q F j, T.v j⟫ ≤ ‖thr T a₀ Q F j‖ * ‖T.v j‖ := real_inner_le_norm _ _
    have h4 : ⟪Ts, T.v j⟫ - ⟪thr T a₀ Q F j, T.v j⟫ ≤ εT P Q δ F s * ‖T.v j‖ := by
      rw [← inner_sub_left]
      refine (real_inner_le_norm _ _).trans ?_
      rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have hv : sLo P δ s ^ 2 ≤ ‖T.v j‖ ^ 2 := by
      have : 0 ≤ sLo P δ s := le_trans P.vMin_pos.le (le_max_left _ _)
      exact pow_le_pow_left₀ this hw.1 2
    have hc := Q.drag_pos
    have key : (Fw P Q δ F s) * ‖T.v j‖ ≤ ‖thr T a₀ Q F j‖ * ‖T.v j‖ := by
      unfold Fw
      have := mul_le_mul_of_nonneg_left hv hc.le
      nlinarith
    exact le_of_mul_le_mul_right key hvpos

/-! ### Heading and lateral reference -/

theorem horiz_vP_ge : vh P δ F s ≤ ‖horiz (vP T a₀ F j)‖ := by
  have h1 := norm_horiz_v_ge T j
  have h2 := norm_horiz_sub_le (vP T a₀ F j) (T.v j)
  have h3 := vP_err T a₀ h hS j
  have hcos : 0 ≤ Real.cos P.climbMax :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [P.climbMax_nonneg, Real.pi_pos], P.climbMax_lt.le⟩
  have := mul_le_mul_of_nonneg_right hw.1 hcos
  rw [abs_le] at h2
  unfold vh; linarith

omit h hS hw in
theorem horiz_sub (x y : E3) : horiz x - horiz y = horiz (x - y) := by
  simp only [horiz, inner_sub_left, sub_smul]; abel

omit h hS hw in
theorem inner_up_nrm_horiz (x : E3) : ⟪up, nrm (horiz x)⟫ = 0 := by
  rw [nrm, inner_smul_right, real_inner_comm, horiz_up_inner, mul_zero]

omit h hS hw in
theorem norm_nrm_horiz {x : E3} (hx : horiz x ≠ 0) : ‖nrm (horiz x)‖ = 1 := by
  unfold nrm; exact norm_smul_inv_norm hx

omit h hS hw in
theorem norm_cross_up_nrm_horiz {x : E3} (hx : horiz x ≠ 0) : ‖cross up (nrm (horiz x))‖ = 1 :=
  norm_cross_of_orthonormal norm_up' (norm_nrm_horiz hx) (inner_up_nrm_horiz x)

omit h hS hw in
theorem inner_cross_up_nrm_horiz_self (x : E3) : ⟪cross up (nrm (horiz x)), x⟫ = 0 := by
  have hx : x = (‖horiz x‖ • nrm (horiz x)) + ⟪x, up⟫ • up := by
    by_cases h0 : horiz x = 0
    · have : x = ⟪x, up⟫ • up := by
        have := h0; simp only [horiz, sub_eq_zero] at this; exact this
      rw [h0, norm_zero, zero_smul, zero_add]; exact this
    · rw [nrm, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]
      simp [horiz]
  set y := nrm (horiz x)
  have e : ⟪cross up y, x⟫ = ⟪cross up y, ‖horiz x‖ • y + ⟪x, up⟫ • up⟫ := by rw [← hx]
  rw [e, inner_add_right, inner_smul_right, inner_smul_right]
  have o1 : ⟪cross up y, y⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_right _ _
  have o2 : ⟪cross up y, up⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_left _ _
  rw [o1, o2]; ring

theorem heading_err (hs : s ∈ Set.Icc P.vMin P.vMax) :
    ‖hP T a₀ F j - nrm (horiz (T.v j))‖ ≤ εV P δ F / vh P δ F s := by
  have hvh := h.vh_pos s hs
  have h1 := horiz_vP_ge T a₀ h hS hw
  have h2 : vh P δ F s ≤ ‖horiz (T.v j)‖ := by
    have := norm_horiz_v_ge T j
    have hcos : 0 ≤ Real.cos P.climbMax :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [P.climbMax_nonneg, Real.pi_pos], P.climbMax_lt.le⟩
    have := mul_le_mul_of_nonneg_right hw.1 hcos
    have := εV_nonneg T a₀ h hS
    unfold vh; linarith
  refine (norm_nrm_sub_le_sharp hvh h1 h2).trans ?_
  apply div_le_div_of_nonneg_right _ hvh.le
  rw [horiz_sub]
  exact (norm_horiz_le _).trans (vP_err T a₀ h hS j)

theorem horiz_vP_ne (hs : s ∈ Set.Icc P.vMin P.vMax) : horiz (vP T a₀ F j) ≠ 0 := by
  intro h0
  have := horiz_vP_ge T a₀ h hS hw
  rw [h0, norm_zero] at this
  linarith [h.vh_pos s hs]

theorem lateral_le (hs : s ∈ Set.Icc P.vMin P.vMax) :
    |⟪lP T a₀ F j, thr T a₀ Q F j⟫| ≤ Lat P δ F s := by
  have hvh := h.vh_pos s hs
  have hT0 : horiz (T.v j) ≠ 0 := by
    intro h0
    have := norm_horiz_v_ge T j
    rw [h0, norm_zero] at this
    have hcos : 0 < Real.cos P.climbMax :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [P.climbMax_nonneg, Real.pi_pos], P.climbMax_lt⟩
    have hv := P.vMin_pos.trans_le (T.speed_ge j)
    nlinarith
  set lT := cross up (nrm (horiz (T.v j)))
  have hl : ‖lP T a₀ F j‖ = 1 := norm_cross_up_nrm_horiz (horiz_vP_ne T a₀ h hS hw hs)
  have hlT : ‖lT‖ = 1 := norm_cross_up_nrm_horiz hT0
  have e1 : ⟪lP T a₀ F j, thr T a₀ Q F j⟫ = ⟪lP T a₀ F j, F.planAcc T a₀ j⟫ := by
    have o1 : ⟪lP T a₀ F j, up⟫ = 0 := by rw [lP, real_inner_comm]; exact inner_cross_left _ _
    have o2 : ⟪lP T a₀ F j, vP T a₀ F j⟫ = 0 := inner_cross_up_nrm_horiz_self _
    rw [thr, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, o1, o2]; ring
  rw [e1]
  set a := δ⁻¹ • (T.v (j + 1) - T.v j)
  have e2 : ⟪lP T a₀ F j, F.planAcc T a₀ j⟫ = ⟪lT, a⟫ + ⟪lP T a₀ F j - lT, a⟫
      + ⟪lP T a₀ F j, F.planAcc T a₀ j - a⟫ := by
    rw [inner_sub_left, inner_sub_right]; ring
  rw [e2]
  have t1 : |⟪lT, a⟫| ≤ sHi P δ s ^ 2 / P.turnRadius := by
    refine (abs_inner_targetAcc_perp_le T j hlT (inner_cross_up_nrm_horiz_self _) h.δ_pos).trans ?_
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw.2 2)
      P.turnRadius_pos.le
  have t2 : |⟪lP T a₀ F j - lT, a⟫| ≤ A P δ s * (εV P δ F / vh P δ F s) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have : ‖lP T a₀ F j - lT‖ ≤ εV P δ F / vh P δ F s := by
      have e : lP T a₀ F j - lT = cross up (hP T a₀ F j - nrm (horiz (T.v j))) := by
        rw [lP, show lT = cross up (nrm (horiz (T.v j))) from rfl, sub_eq_add_neg,
          sub_eq_add_neg, cross_add_right', ← neg_one_smul ℝ (nrm (horiz (T.v j))),
          cross_smul_right', neg_one_smul]
      rw [e]
      refine (norm_cross_le _ _).trans ?_
      rw [norm_up', one_mul]; exact heading_err T a₀ h hS hw hs
    calc ‖lP T a₀ F j - lT‖ * ‖a‖ ≤ εV P δ F / vh P δ F s * A P δ s :=
          mul_le_mul this (acc_le T h hw) (norm_nonneg _) (by
            have := εV_nonneg T a₀ h hS; positivity)
      _ = A P δ s * (εV P δ F / vh P δ F s) := by ring
  have t3 : |⟪lP T a₀ F j, F.planAcc T a₀ j - a⟫| ≤ εD P δ F := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hl, one_mul]; exact acc_err T a₀ h hS j
  unfold Lat
  have := abs_add_le (⟪lT, a⟫ + ⟪lP T a₀ F j - lT, a⟫) ⟪lP T a₀ F j, F.planAcc T a₀ j - a⟫
  have := abs_add_le ⟪lT, a⟫ ⟪lP T a₀ F j - lT, a⟫
  linarith

theorem forward_ge (hs : s ∈ Set.Icc P.vMin P.vMax) :
    Nlo P Q δ F s ≤ ⟪thr T a₀ Q F j, hP T a₀ F j⟫ := by
  have hvh := h.vh_pos s hs
  set Ts := thrustStar Q (T.v j) (δ⁻¹ • (T.v (j + 1) - T.v j))
  set hT := nrm (horiz (T.v j))
  have hl : ‖hP T a₀ F j‖ = 1 := norm_nrm_horiz (horiz_vP_ne T a₀ h hS hw hs)
  have e : ⟪thr T a₀ Q F j, hP T a₀ F j⟫ = ⟪Ts, hT⟫ + ⟪Ts, hP T a₀ F j - hT⟫
      + ⟪thr T a₀ Q F j - Ts, hP T a₀ F j⟫ := by
    rw [inner_sub_right, inner_sub_left]; ring
  rw [e]
  have t1 := thrustStar_along_heading_ge T Q j
  have ha := acc_le T h hw
  have hv : sLo P δ s ^ 2 ≤ ‖T.v j‖ ^ 2 := by
    have : 0 ≤ sLo P δ s := le_trans P.vMin_pos.le (le_max_left _ _)
    exact pow_le_pow_left₀ this hw.1 2
  have hcos : 0 ≤ Real.cos P.climbMax :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [P.climbMax_nonneg, Real.pi_pos], P.climbMax_lt.le⟩
  have hc := Q.drag_pos
  have t1' : Q.drag * sLo P δ s ^ 2 * Real.cos P.climbMax - A P δ s ≤ ⟪Ts, hT⟫ := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hc.le) hcos
    linarith
  have hTs : ‖Ts‖ ≤ Thi P Q δ F s := by
    obtain ⟨n1, -⟩ := thrustStar_norm_horiz_le T Q j
    have hv2 : ‖T.v j‖ ^ 2 ≤ sHi P δ s ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw.2 2
    have := mul_le_mul_of_nonneg_left hv2 hc.le
    have hεT : 0 ≤ εT P Q δ F s := (norm_nonneg _).trans (thr_err T a₀ h hS hw)
    unfold Thi; linarith
  have t2 : -(Thi P Q δ F s * (εV P δ F / vh P δ F s)) ≤ ⟪Ts, hP T a₀ F j - hT⟫ := by
    have := abs_real_inner_le_norm Ts (hP T a₀ F j - hT)
    have := mul_le_mul hTs (heading_err T a₀ h hS hw hs) (norm_nonneg _)
      ((norm_nonneg _).trans hTs)
    linarith [(abs_le.1 ‹|⟪Ts, hP T a₀ F j - hT⟫| ≤ _›).1]
  have t3 : -(εT P Q δ F s) ≤ ⟪thr T a₀ Q F j - Ts, hP T a₀ F j⟫ := by
    have := abs_real_inner_le_norm (thr T a₀ Q F j - Ts) (hP T a₀ F j)
    rw [hl, mul_one] at this
    linarith [(abs_le.1 this).1, thr_err T a₀ h hS hw]
  unfold Nlo; linarith

theorem lateral_n_le (hs : s ∈ Set.Icc P.vMin P.vMax) :
    |⟪lP T a₀ F j, nP T a₀ Q F j⟫| ≤ sb P Q δ F s := by
  have hT := thr_norm_ge T a₀ h hS hw
  have hZ : 0 < Tlo P Q δ F s := lt_of_lt_of_le (h.zlo_pos s hs) (le_max_left _ _)
  have hpos : 0 < ‖thr T a₀ Q F j‖ := hZ.trans_le hT
  rw [nP, nrm, inner_smul_right, abs_mul, abs_inv, abs_norm, inv_mul_eq_div, sb]
  calc |⟪lP T a₀ F j, thr T a₀ Q F j⟫| / ‖thr T a₀ Q F j‖
      ≤ Lat P δ F s / ‖thr T a₀ Q F j‖ :=
        div_le_div_of_nonneg_right (lateral_le T a₀ h hS hw hs) hpos.le
    _ ≤ Lat P δ F s / Tlo P Q δ F s :=
        div_le_div_of_nonneg_left ((abs_nonneg _).trans (lateral_le T a₀ h hS hw hs)) hZ hT

theorem nP_unit (hs : s ∈ Set.Icc P.vMin P.vMax) : ‖nP T a₀ Q F j‖ = 1 := by
  have hZ : 0 < Tlo P Q δ F s := lt_of_lt_of_le (h.zlo_pos s hs) (le_max_left _ _)
  have := hZ.trans_le (thr_norm_ge T a₀ h hS hw)
  unfold nP nrm; exact norm_smul_inv_norm (norm_pos_iff.1 this)

theorem vP_ne (hs : s ∈ Set.Icc P.vMin P.vMax) : vP T a₀ F j ≠ 0 := by
  intro h0
  have := horiz_vP_ne T a₀ h hS hw hs
  apply this; rw [h0]; simp [horiz]

end Under

/-! ## Steps over the window -/

namespace Under

open Budget3 Overhead

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ} {F : FIR} {d : ℝ}
  (T : TargetTraj P δ) (a₀ : E3) (h : MasterIneq3 P Q C δ F d)
  (hS : T.StartsSteady (T.p 0) (T.v 0) a₀) {s : ℝ} (hs : s ∈ Set.Icc P.vMin P.vMax) {j : ℕ}
include h hS hs

omit hs in
theorem vP_step (hw : ‖T.v j‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s)) :
    ‖vP T a₀ F (j + 1) - vP T a₀ F j‖ ≤ δ * (A P δ s + εD P δ F) := by
  rw [show vP T a₀ F (j + 1) = vP T a₀ F j + δ • F.planAcc T a₀ j from
    F.planVel_succ T a₀ h.δ_pos.ne' j, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg h.δ_pos.le]
  exact mul_le_mul_of_nonneg_left (planAcc_le T a₀ h hS hw) h.δ_pos.le

omit hs in
theorem thr_step (hw : ‖T.v j‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s))
    (hw' : ‖T.v (j + 1)‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s)) :
    ‖thr T a₀ Q F (j + 1) - thr T a₀ Q F j‖ ≤ dT P Q δ F s := by
  have hsplit : thr T a₀ Q F (j + 1) - thr T a₀ Q F j
      = (F.planAcc T a₀ (j + 1) - F.planAcc T a₀ j)
        + Q.drag • (‖vP T a₀ F (j + 1)‖ • vP T a₀ F (j + 1) - ‖vP T a₀ F j‖ • vP T a₀ F j) := by
    unfold thr; module
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 := F.planAcc_step T a₀ h.δ_pos hS.1 j
  have h2 := norm_dragMap_sub_le (vP T a₀ F (j + 1)) (vP T a₀ F j)
  have h3 := vP_step T a₀ h hS hw
  have h4 := vP_le T a₀ h hS hw'
  have h5 := vP_le T a₀ h hS hw
  have hc := Q.drag_pos
  have hδ := h.δ_pos
  have hA : 0 ≤ A P δ s + εD P δ F :=
    (norm_nonneg _).trans (planAcc_le T a₀ h hS hw)
  rw [norm_smul, Real.norm_of_nonneg hc.le]
  have h6 : (‖vP T a₀ F (j + 1)‖ + ‖vP T a₀ F j‖) * ‖vP T a₀ F (j + 1) - vP T a₀ F j‖
      ≤ (2 * (sHi P δ s + εV P δ F)) * (δ * (A P δ s + εD P δ F)) :=
    mul_le_mul (by linarith) h3 (norm_nonneg _) (by linarith [norm_nonneg (vP T a₀ F j)])
  have := mul_le_mul_of_nonneg_left (h2.trans h6) hc.le
  unfold dT; nlinarith

theorem thr_second (hw : ‖T.v j‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s))
    (hw' : ‖T.v (j + 1)‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s)) :
    ‖thr T a₀ Q F (j + 2) - 2 • thr T a₀ Q F (j + 1) + thr T a₀ Q F j‖ ≤ d2T P Q δ F s := by
  have hsplit : thr T a₀ Q F (j + 2) - 2 • thr T a₀ Q F (j + 1) + thr T a₀ Q F j
      = (F.planAcc T a₀ (j + 2) - 2 • F.planAcc T a₀ (j + 1) + F.planAcc T a₀ j)
        + Q.drag • (‖vP T a₀ F (j + 2)‖ • vP T a₀ F (j + 2)
          - 2 • (‖vP T a₀ F (j + 1)‖ • vP T a₀ F (j + 1)) + ‖vP T a₀ F j‖ • vP T a₀ F j) := by
    unfold thr; module
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 := F.planAcc_second_snap T a₀ h.δ_pos hS j
  have h2 := norm_dragMap_second_le (a := vP T a₀ F j) (c := vP T a₀ F (j + 2))
    (vP_ne T a₀ h hS hw' hs)
  have hs1 : vP T a₀ F (j + 1) = vP T a₀ F j + δ • F.planAcc T a₀ j :=
    F.planVel_succ T a₀ h.δ_pos.ne' j
  have hs2 : vP T a₀ F (j + 2) = vP T a₀ F (j + 1) + δ • F.planAcc T a₀ (j + 1) :=
    F.planVel_succ T a₀ h.δ_pos.ne' (j + 1)
  have hd2 : vP T a₀ F (j + 2) - 2 • vP T a₀ F (j + 1) + vP T a₀ F j
      = δ • (F.planAcc T a₀ (j + 1) - F.planAcc T a₀ j) := by
    rw [hs2, hs1]; module
  have h3 : ‖vP T a₀ F (j + 2) - 2 • vP T a₀ F (j + 1) + vP T a₀ F j‖
      ≤ δ * (F.H0 * δ * P.jerk) := by
    rw [hd2, norm_smul, Real.norm_of_nonneg h.δ_pos.le]
    exact mul_le_mul_of_nonneg_left (F.planAcc_step T a₀ h.δ_pos hS.1 j) h.δ_pos.le
  have h4 := vP_step T a₀ h hS hw'
  have h5 := vP_step T a₀ h hS hw
  have h6 := vP_le T a₀ h hS hw'
  have hc := Q.drag_pos
  have hδ := h.δ_pos
  have hA : 0 ≤ A P δ s + εD P δ F := (norm_nonneg _).trans (planAcc_le T a₀ h hS hw)
  have h4' : ‖vP T a₀ F (j + 2) - vP T a₀ F (j + 1)‖ ^ 2 ≤ (δ * (A P δ s + εD P δ F)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h4 2
  have h5' : ‖vP T a₀ F (j + 1) - vP T a₀ F j‖ ^ 2 ≤ (δ * (A P δ s + εD P δ F)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h5 2
  have h7 : 2 * ‖vP T a₀ F (j + 1)‖ * ‖vP T a₀ F (j + 2) - 2 • vP T a₀ F (j + 1) + vP T a₀ F j‖
      ≤ 2 * (sHi P δ s + εV P δ F) * (δ * (F.H0 * δ * P.jerk)) := by
    have := H0_nonneg F; have := P.jerk_nonneg
    apply mul_le_mul (by linarith) h3 (norm_nonneg _)
      (by linarith [norm_nonneg (vP T a₀ F (j + 1))])
  rw [norm_smul, Real.norm_of_nonneg hc.le]
  have hb : ‖‖vP T a₀ F (j + 2)‖ • vP T a₀ F (j + 2) - 2 • (‖vP T a₀ F (j + 1)‖ • vP T a₀ F (j + 1))
      + ‖vP T a₀ F j‖ • vP T a₀ F j‖ ≤ 2 * (sHi P δ s + εV P δ F) * F.H0 * δ ^ 2 * P.jerk
        + 4 * δ ^ 2 * (A P δ s + εD P δ F) ^ 2 := by
    refine h2.trans ?_
    nlinarith
  have := mul_le_mul_of_nonneg_left hb hc.le
  unfold d2T; nlinarith


variable (hw₀ : ‖T.v j‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s))
  (hw₁ : ‖T.v (j + 1)‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s))
include hw₀ hw₁

omit hS hw₀ hw₁ in
theorem Tlo_pos : 0 < Tlo P Q δ F s := lt_of_lt_of_le (h.zlo_pos s hs) (le_max_left _ _)

theorem n_step : ‖nP T a₀ Q F (j + 1) - nP T a₀ Q F j‖ ≤ dn P Q δ F s := by
  refine (norm_nrm_sub_le_sharp (Tlo_pos h hs) (thr_norm_ge T a₀ h hS hw₁)
    (thr_norm_ge T a₀ h hS hw₀)).trans ?_
  exact div_le_div_of_nonneg_right (thr_step T a₀ h hS hw₀ hw₁)
    (Tlo_pos h hs).le

theorem h_step : ‖hP T a₀ F (j + 1) - hP T a₀ F j‖ ≤ dl P δ F s := by
  have hvh := h.vh_pos s hs
  refine (norm_nrm_sub_le_sharp hvh (horiz_vP_ge T a₀ h hS hw₁)
    (horiz_vP_ge T a₀ h hS hw₀)).trans ?_
  unfold dl
  apply div_le_div_of_nonneg_right _ hvh.le
  rw [horiz_sub]
  exact (norm_horiz_le _).trans (vP_step T a₀ h hS hw₀)

theorem l_step : ‖lP T a₀ F (j + 1) - lP T a₀ F j‖ ≤ dl P δ F s := by
  have e : lP T a₀ F (j + 1) - lP T a₀ F j = cross up (hP T a₀ F (j + 1) - hP T a₀ F j) := by
    rw [lP, lP, sub_eq_add_neg, sub_eq_add_neg, cross_add_right',
      ← neg_one_smul ℝ (hP T a₀ F j), cross_smul_right', neg_one_smul]
  rw [e]
  refine (norm_cross_le _ _).trans ?_
  rw [norm_up', one_mul]; exact h_step T a₀ h hS hs hw₀ hw₁

variable (hw₂ : ‖T.v (j + 2)‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s))
include hw₂

theorem n_cross_second :
    ‖cross (nP T a₀ Q F (j + 1))
      (nP T a₀ Q F (j + 2) - 2 • nP T a₀ Q F (j + 1) + nP T a₀ Q F j)‖ ≤ xn P Q δ F s := by
  have hT := Tlo_pos h hs
  refine (norm_cross_nrm_second_le hT (thr_norm_ge T a₀ h hS hw₀) (thr_norm_ge T a₀ h hS hw₁)
    (thr_norm_ge T a₀ h hS hw₂)).trans ?_
  have s0 := thr_step T a₀ h hS hw₀ hw₁
  have s1 := thr_step T a₀ h hS hw₁ hw₂
  have s2 := thr_second T a₀ h hS hs hw₀ hw₁
  have e1 := pow_le_pow_left₀ (norm_nonneg _) s1 2
  have e0 := pow_le_pow_left₀ (norm_nonneg _) s0 2
  unfold xn
  have f1 := div_le_div_of_nonneg_right s2 hT.le
  have f2 : (‖thr T a₀ Q F (j + 2) - thr T a₀ Q F (j + 1)‖ ^ 2
      + ‖thr T a₀ Q F (j + 1) - thr T a₀ Q F j‖ ^ 2) / Tlo P Q δ F s ^ 2
      ≤ 2 * dT P Q δ F s ^ 2 / Tlo P Q δ F s ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

theorem n_second :
    ‖nP T a₀ Q F (j + 2) - 2 • nP T a₀ Q F (j + 1) + nP T a₀ Q F j‖ ≤ d2n P Q δ F s := by
  have hT := Tlo_pos h hs
  refine (norm_nrm_second_le hT (thr_norm_ge T a₀ h hS hw₀) (thr_norm_ge T a₀ h hS hw₁)
    (thr_norm_ge T a₀ h hS hw₂)).trans ?_
  have s0 := thr_step T a₀ h hS hw₀ hw₁
  have s1 := thr_step T a₀ h hS hw₁ hw₂
  have s2 := thr_second T a₀ h hS hs hw₀ hw₁
  have e1 := pow_le_pow_left₀ (norm_nonneg _) s1 2
  have e0 := pow_le_pow_left₀ (norm_nonneg _) s0 2
  unfold d2n
  have f1 : 2 * ‖thr T a₀ Q F (j + 2) - 2 • thr T a₀ Q F (j + 1) + thr T a₀ Q F j‖
      / Tlo P Q δ F s ≤ 2 * d2T P Q δ F s / Tlo P Q δ F s :=
    div_le_div_of_nonneg_right (by linarith) hT.le
  have f2 : 3 * (‖thr T a₀ Q F (j + 2) - thr T a₀ Q F (j + 1)‖ ^ 2
      + ‖thr T a₀ Q F (j + 1) - thr T a₀ Q F j‖ ^ 2) / Tlo P Q δ F s ^ 2
      ≤ 6 * dT P Q δ F s ^ 2 / Tlo P Q δ F s ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

theorem h_second :
    ‖hP T a₀ F (j + 2) - 2 • hP T a₀ F (j + 1) + hP T a₀ F j‖ ≤ d2l P δ F s := by
  have hvh := h.vh_pos s hs
  refine (norm_nrm_second_le hvh (horiz_vP_ge T a₀ h hS hw₀) (horiz_vP_ge T a₀ h hS hw₁)
    (horiz_vP_ge T a₀ h hS hw₂)).trans ?_
  have hs1 : vP T a₀ F (j + 1) = vP T a₀ F j + δ • F.planAcc T a₀ j :=
    F.planVel_succ T a₀ h.δ_pos.ne' j
  have hs2 : vP T a₀ F (j + 2) = vP T a₀ F (j + 1) + δ • F.planAcc T a₀ (j + 1) :=
    F.planVel_succ T a₀ h.δ_pos.ne' (j + 1)
  have hd2 : horiz (vP T a₀ F (j + 2)) - 2 • horiz (vP T a₀ F (j + 1)) + horiz (vP T a₀ F j)
      = horiz (δ • (F.planAcc T a₀ (j + 1) - F.planAcc T a₀ j)) := by
    rw [hs2, hs1]; simp only [horiz, inner_add_left, inner_sub_left, inner_smul_left,
      two_smul, RCLike.conj_to_real]; module
  have b2 : ‖horiz (vP T a₀ F (j + 2)) - 2 • horiz (vP T a₀ F (j + 1)) + horiz (vP T a₀ F j)‖
      ≤ δ ^ 2 * F.H0 * P.jerk := by
    rw [hd2]
    refine (norm_horiz_le _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg h.δ_pos.le]
    have := mul_le_mul_of_nonneg_left (F.planAcc_step T a₀ h.δ_pos hS.1 j) h.δ_pos.le
    nlinarith
  have b1 : ‖horiz (vP T a₀ F (j + 2)) - horiz (vP T a₀ F (j + 1))‖ ≤ dl P δ F s * vh P δ F s := by
    rw [horiz_sub]; refine (norm_horiz_le _).trans ?_
    have := vP_step T a₀ h hS hw₁
    unfold dl; rw [div_mul_cancel₀ _ hvh.ne']; exact this
  have b0 : ‖horiz (vP T a₀ F (j + 1)) - horiz (vP T a₀ F j)‖ ≤ dl P δ F s * vh P δ F s := by
    rw [horiz_sub]; refine (norm_horiz_le _).trans ?_
    have := vP_step T a₀ h hS hw₀
    unfold dl; rw [div_mul_cancel₀ _ hvh.ne']; exact this
  have e1 := pow_le_pow_left₀ (norm_nonneg _) b1 2
  have e0 := pow_le_pow_left₀ (norm_nonneg _) b0 2
  unfold d2l
  have f1 : 2 * ‖horiz (vP T a₀ F (j + 2)) - 2 • horiz (vP T a₀ F (j + 1))
      + horiz (vP T a₀ F j)‖ / vh P δ F s ≤ 2 * (δ ^ 2 * F.H0 * P.jerk) / vh P δ F s :=
    div_le_div_of_nonneg_right (by linarith) hvh.le
  have f2 : 3 * (‖horiz (vP T a₀ F (j + 2)) - horiz (vP T a₀ F (j + 1))‖ ^ 2
      + ‖horiz (vP T a₀ F (j + 1)) - horiz (vP T a₀ F j)‖ ^ 2) / vh P δ F s ^ 2
      ≤ 6 * dl P δ F s ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

theorem l_second :
    ‖lP T a₀ F (j + 2) - 2 • lP T a₀ F (j + 1) + lP T a₀ F j‖ ≤ d2l P δ F s := by
  have e : lP T a₀ F (j + 2) - 2 • lP T a₀ F (j + 1) + lP T a₀ F j
      = cross up (hP T a₀ F (j + 2) - 2 • hP T a₀ F (j + 1) + hP T a₀ F j) := by
    simp only [lP]
    ext i; fin_cases i <;> simp [cross, crossProduct, two_smul] <;> ring
  rw [e]
  refine (norm_cross_le _ _).trans ?_
  rw [norm_up', one_mul]; exact h_second T a₀ h hS hs hw₀ hw₁ hw₂

end Under

end VisionTracking
