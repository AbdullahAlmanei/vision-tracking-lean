import VisionTracking.UnderPlan
import VisionTracking.Master2
import VisionTracking.LookDown
import VisionTracking.Hinge

/-!
# The underneath formation as a rigid-body trajectory

Frames, hinge and lifting for the version-3 design: the frame is lateral-locked
(`b₁ = lat1 ℓ n`, `b₂ = lat2 ℓ n`, `b₃ = n`), and the hinge points the camera straight up in
the plane `span(b₁, n)`, clamped to the hinge range.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

namespace Under

open Budget3 Overhead

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ} {F : FIR} {d : ℝ}
  (T : TargetTraj P δ) (a₀ : E3)

noncomputable def B1 (Q : QuadParams) (F : FIR) (j : ℕ) : E3 := lat1 (lP T a₀ F j) (nP T a₀ Q F j)
noncomputable def B2 (Q : QuadParams) (F : FIR) (j : ℕ) : E3 := lat2 (lP T a₀ F j) (nP T a₀ Q F j)
/-- In-plane pitch of the thrust axis. -/
noncomputable def phi (Q : QuadParams) (F : FIR) (j : ℕ) : ℝ :=
  Real.arctan (⟪B1 T a₀ Q F j, up⟫ / ⟪nP T a₀ Q F j, up⟫)
/-- Hinge: point straight up within `span(b₁, n)`, clamped. -/
noncomputable def eta (Q : QuadParams) (C : CameraParams) (F : FIR) (j : ℕ) : ℝ :=
  max C.hingeLo (min C.hingeHi (π / 2 - phi T a₀ Q F j))

omit T a₀ in
theorem TargetParams.Amax_nonneg (P : TargetParams) : 0 ≤ P.Amax := by
  unfold TargetParams.Amax
  have := P.aTan_nonneg; have := P.turnRadius_pos; positivity

/-- **Speed window**: the speeds of three consecutive steps lie in the window of the first. -/
theorem window (hδ : 0 < δ) (k i : ℕ) (hi : i ≤ 2) :
    ‖T.v (k + i)‖ ∈ Set.Icc (sLo P δ ‖T.v k‖) (sHi P δ ‖T.v k‖) := by
  have hA := TargetParams.Amax_nonneg P
  have step : ∀ m, |‖T.v (k + m)‖ - ‖T.v k‖| ≤ m * (δ * P.Amax) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have := abs_speed_step_le T hδ (k + m)
      have e : ‖T.v (k + (m + 1))‖ - ‖T.v k‖
          = (‖T.v (k + m + 1)‖ - ‖T.v (k + m)‖) + (‖T.v (k + m)‖ - ‖T.v k‖) := by
        rw [show k + (m + 1) = k + m + 1 by ring]; ring
      rw [e]; push_cast
      refine (abs_add_le _ _).trans ?_
      linarith
  have hm := step i
  have hi' : (i : ℝ) ≤ 2 := by exact_mod_cast hi
  have hb : (i : ℝ) * (δ * P.Amax) ≤ 2 * δ * P.Amax := by
    have := mul_le_mul_of_nonneg_right hi' (mul_nonneg hδ.le hA); linarith
  rw [abs_le] at hm
  refine ⟨max_le (T.speed_ge _) (by linarith), le_min (T.speed_le _) (by linarith)⟩

theorem speed_mem (k : ℕ) : ‖T.v k‖ ∈ Set.Icc P.vMin P.vMax := ⟨T.speed_ge k, T.speed_le k⟩

variable (h : MasterIneq3 P Q C δ F d) (hS : T.StartsSteady (T.p 0) (T.v 0) a₀)
include h hS

/-- Frame facts at a step `j` in the window of speed `s`. -/
theorem frame_facts {s : ℝ} (hs : s ∈ Set.Icc P.vMin P.vMax) {j : ℕ}
    (hw : ‖T.v j‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s)) :
    ‖lP T a₀ F j‖ = 1 ∧ ‖nP T a₀ Q F j‖ = 1 ∧ |⟪lP T a₀ F j, nP T a₀ Q F j⟫| ≤ sb P Q δ F s := by
  refine ⟨norm_cross_up_nrm_horiz (horiz_vP_ne T a₀ h hS hw hs), nP_unit T a₀ h hS hw hs,
    lateral_n_le T a₀ h hS hw hs⟩

theorem B_facts (j : ℕ) : ‖B1 T a₀ Q F j‖ = 1 ∧ ‖B2 T a₀ Q F j‖ = 1 ∧
    ⟪B1 T a₀ Q F j, B2 T a₀ Q F j⟫ = 0 ∧ cross (B1 T a₀ Q F j) (B2 T a₀ Q F j) = nP T a₀ Q F j := by
  have hs := speed_mem T j
  obtain ⟨hl, hn, hf⟩ := frame_facts T a₀ h hS hs (by simpa using window T h.δ_pos j 0 (by omega))
  have hf' := hf.trans_lt (h.sb_lt _ hs)
  exact ⟨lat1_unit hn hl hf', lat2_unit hn hl hf', inner_lat1_lat2, cross_lat1_lat2 hn hl hf'⟩

/-- Consecutive frames are close. -/
theorem B_near (k : ℕ) :
    1 ≤ frameTrace (B1 T a₀ Q F k) (B2 T a₀ Q F k) (B1 T a₀ Q F (k + 1)) (B2 T a₀ Q F (k + 1)) := by
  set s := ‖T.v k‖
  have hs := speed_mem T k
  have w0 : ‖T.v k‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s) := by
    simpa using window T h.δ_pos k 0 (by omega)
  have w1 : ‖T.v (k + 1)‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s) := window T h.δ_pos k 1 (by omega)
  obtain ⟨hl0, hn0, hf0⟩ := frame_facts T a₀ h hS hs w0
  obtain ⟨hl1, hn1, hf1⟩ := frame_facts T a₀ h hS hs w1
  have hdn := n_step T a₀ h hS hs w0 w1
  have hdl := l_step T a₀ h hS hs w0 w1
  obtain ⟨c2, c1⟩ := lat_steps_crude hn0 hn1 hl0 hl1 hf0 hf1 (h.sb_lt s hs) hdn hdl
  obtain ⟨u1, u2, u12, x1⟩ := B_facts T a₀ h hS k
  obtain ⟨v1, v2, v12, x2⟩ := B_facts T a₀ h hS (k + 1)
  have hD := h.near s hs
  have hM : 0 ≤ (2 * dl P δ F s + 2 * dn P Q δ F s) / M P Q δ F s :=
    div_nonneg (by linarith [(norm_nonneg _).trans hdn, (norm_nonneg _).trans hdl])
      (Real.sqrt_nonneg _)
  have e1 : ‖B1 T a₀ Q F k - B1 T a₀ Q F (k + 1)‖ ≤ dbc P Q δ F s := by
    rw [norm_sub_rev]; exact c1
  have e2 : ‖B2 T a₀ Q F k - B2 T a₀ Q F (k + 1)‖ ≤ dbc P Q δ F s := by
    rw [norm_sub_rev]; refine c2.trans ?_; unfold dbc M; linarith [(norm_nonneg _).trans hdn]
  have e3 : ‖cross (B1 T a₀ Q F k) (B2 T a₀ Q F k) - cross (B1 T a₀ Q F (k + 1)) (B2 T a₀ Q F (k + 1))‖
      ≤ dbc P Q δ F s := by
    rw [x1, x2, norm_sub_rev]; unfold dbc; linarith
  have := frameTrace_ge_of_step u1 u2 u12 v1 v2 v12 e1 e2 e3
  have h0 : 0 ≤ dbc P Q δ F s := (norm_nonneg _).trans e1
  nlinarith

/-- The underneath formation as a kinematic plan. -/
noncomputable def kp : KinPlan Q C δ where
  x k := F.planPos T a₀ ((-d) • up) k
  v k := vP T a₀ F k
  b₁ := B1 T a₀ Q F
  b₂ := B2 T a₀ Q F
  η := eta T a₀ Q C F
  steps := F.planPos_succ T a₀ ((-d) • up)
  b₁_unit k := (B_facts T a₀ h hS k).1
  b₂_unit k := (B_facts T a₀ h hS k).2.1
  b₁₂_orth k := (B_facts T a₀ h hS k).2.2.1
  near := B_near T a₀ h hS

theorem kp_b₃ (k : ℕ) : (kp T a₀ h hS).b₃ k = nP T a₀ Q F k := (B_facts T a₀ h hS k).2.2.2

theorem kp_thrust (k : ℕ) : (kp T a₀ h hS).thrust k = thr T a₀ Q F k := by
  simp only [KinPlan.thrust, kp]
  rw [show vP T a₀ F (k + 1) = vP T a₀ F k + δ • F.planAcc T a₀ k from
    F.planVel_succ T a₀ h.δ_pos.ne' k, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ h.δ_pos.ne', one_smul]
  rfl

theorem kp_hdir (k : ℕ) :
    (kp T a₀ h hS).thrust k = ‖(kp T a₀ h hS).thrust k‖ • (kp T a₀ h hS).b₃ k := by
  have hs := speed_mem T k
  have hw : ‖T.v k‖ ∈ Set.Icc (sLo P δ ‖T.v k‖) (sHi P δ ‖T.v k‖) := by
    simpa using window T h.δ_pos k 0 (by omega)
  have hZ : 0 < Tlo P Q δ F ‖T.v k‖ := lt_of_lt_of_le (h.zlo_pos _ hs) (le_max_left _ _)
  have hpos := hZ.trans_le (thr_norm_ge T a₀ h hS hw)
  rw [kp_thrust, kp_b₃, nP, nrm, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

/-- The body-rate vector of step `j`. -/
noncomputable def av (j : ℕ) : E3 :=
  aVec (B1 T a₀ Q F j) (B2 T a₀ Q F j) (B1 T a₀ Q F (j + 1)) (B2 T a₀ Q F (j + 1))

theorem kp_rate (j : ℕ) : (kp T a₀ h hS).rate j = δ⁻¹ • psiVec (av T a₀ (Q := Q) (F := F) j) :=
  (kp T a₀ h hS).rate_eq_aVec j

theorem av_le {s : ℝ} (hs : s ∈ Set.Icc P.vMin P.vMax) {j : ℕ}
    (hw₀ : ‖T.v j‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s))
    (hw₁ : ‖T.v (j + 1)‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s)) :
    ‖av T a₀ (Q := Q) (F := F) j‖ ≤ θa P Q δ F s := by
  obtain ⟨hl0, hn0, hf0⟩ := frame_facts T a₀ h hS hs hw₀
  obtain ⟨hl1, hn1, hf1⟩ := frame_facts T a₀ h hS hs hw₁
  have hsb := h.sb_lt s hs
  have r := lat_aVec_rp hn0 hn1 hl0 hl1 hf0 hf1 hsb
  have y := lat_aVec_yaw hn0 hn1 hl0 hl1 hf0 hf1 hsb
  have hdn := n_step T a₀ h hS hs hw₀ hw₁
  have hdl := l_step T a₀ h hS hs hw₀ hw₁
  have hsb0 : 0 ≤ sb P Q δ F s := (abs_nonneg _).trans hf0
  have hM : 0 < M P Q δ F s := Real.sqrt_pos.2 (by nlinarith)
  have y' : |(av T a₀ (Q := Q) (F := F) j).ofLp 2|
      ≤ (dl P δ F s + sb P Q δ F s * dn P Q δ F s) / M P Q δ F s := by
    refine y.trans (div_le_div_of_nonneg_right ?_ hM.le)
    have := mul_le_mul_of_nonneg_left hdn hsb0
    linarith
  have r' : (av T a₀ (Q := Q) (F := F) j).ofLp 0 ^ 2 + (av T a₀ (Q := Q) (F := F) j).ofLp 1 ^ 2
      ≤ dn P Q δ F s ^ 2 :=
    r.trans (pow_le_pow_left₀ (norm_nonneg _) hdn 2)
  unfold θa
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_coords]
  apply Real.sqrt_le_sqrt
  have := pow_le_pow_left₀ (abs_nonneg _) y' 2
  rw [sq_abs] at this
  linarith

theorem rate_le_Ωb (j : ℕ) {s : ℝ} (hs : s ∈ Set.Icc P.vMin P.vMax)
    (hw₀ : ‖T.v j‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s))
    (hw₁ : ‖T.v (j + 1)‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s)) :
    ‖psiVec (av T a₀ (Q := Q) (F := F) j)‖ ≤ Gψ P Q δ F s * θa P Q δ F s := by
  have ha := av_le T a₀ h hS hs hw₀ hw₁
  have hθ := h.θ_lt s hs
  refine (norm_psiVec_le ha hθ).trans ?_
  unfold Gψ
  rw [div_eq_mul_one_div, mul_comm]
  exact mul_le_mul_of_nonneg_left ha (by positivity)

/-- **Sharp frame steps**: each frame vector moves by at most the rotation angle. -/
theorem B_step_le (j : ℕ) {s : ℝ} (hs : s ∈ Set.Icc P.vMin P.vMax)
    (hw₀ : ‖T.v j‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s))
    (hw₁ : ‖T.v (j + 1)‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s)) :
    ‖B1 T a₀ Q F (j + 1) - B1 T a₀ Q F j‖ ≤ db P Q δ F s ∧
      ‖B2 T a₀ Q F (j + 1) - B2 T a₀ Q F j‖ ≤ db P Q δ F s := by
  set p := kp T a₀ h hS
  obtain ⟨-, r1, r2, -⟩ := p.rotVec_spec j
  have hrot : ‖p.rotVec j‖ = ‖psiVec (av T a₀ (Q := Q) (F := F) j)‖ := by
    have e : toF (p.b₁ j) (p.b₂ j) (p.rotVec j) = psiVec (av T a₀ (Q := Q) (F := F) j) := by
      have := p.rate_eq_aVec j
      simp only [KinPlan.rate] at this
      have hδ := h.δ_pos.ne'
      have := congrArg (fun x => δ • x) this
      simp only [smul_smul, mul_inv_cancel₀ hδ, one_smul] at this
      exact this
    rw [← e, norm_toF (p.b₁_unit j) (p.b₂_unit j) (p.b₁₂_orth j)]
  have hω : ‖p.rotVec j‖ ≤ db P Q δ F s := by
    rw [hrot]; exact rate_le_Ωb T a₀ h hS j hs hw₀ hw₁
  constructor
  · have := norm_rotate_sub_le (p.rotVec j) (p.b₁ j)
    rw [r1, p.b₁_unit j, mul_one] at this
    exact this.trans hω
  · have := norm_rotate_sub_le (p.rotVec j) (p.b₂ j)
    rw [r2, p.b₂_unit j, mul_one] at this
    exact this.trans hω

omit T a₀ h hS in
theorem da_aux {A1 A0 : E3} {R Y : ℝ}
    (rp : (A1.ofLp 0 - A0.ofLp 0) ^ 2 + (A1.ofLp 1 - A0.ofLp 1) ^ 2 ≤ R ^ 2)
    (yw : |A1.ofLp 2 - A0.ofLp 2| ≤ Y) : ‖A1 - A0‖ ≤ √(R ^ 2 + Y ^ 2) := by
  have hy2 := pow_le_pow_left₀ (abs_nonneg _) yw 2
  rw [sq_abs] at hy2
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_coords]
  apply Real.sqrt_le_sqrt
  simp only [WithLp.ofLp_sub, Pi.sub_apply]
  linarith

section Torque

variable (k : ℕ)

omit hS in
/-- The window facts at step `k`. -/
theorem windows : ‖T.v k‖ ∈ Set.Icc P.vMin P.vMax ∧
    ‖T.v k‖ ∈ Set.Icc (sLo P δ ‖T.v k‖) (sHi P δ ‖T.v k‖) ∧
    ‖T.v (k + 1)‖ ∈ Set.Icc (sLo P δ ‖T.v k‖) (sHi P δ ‖T.v k‖) ∧
    ‖T.v (k + 2)‖ ∈ Set.Icc (sLo P δ ‖T.v k‖) (sHi P δ ‖T.v k‖) :=
  ⟨speed_mem T k, by simpa using window T h.δ_pos k 0 (by omega),
    window T h.δ_pos k 1 (by omega), window T h.δ_pos k 2 (by omega)⟩

/-- The change of the body-rate vector over two steps. -/
theorem dav_le : ‖av T a₀ (Q := Q) (F := F) (k + 1) - av T a₀ (Q := Q) (F := F) k‖
      ≤ da P Q δ F ‖T.v k‖ ∧
    |(av T a₀ (Q := Q) (F := F) (k + 1)).ofLp 2 - (av T a₀ (Q := Q) (F := F) k).ofLp 2|
      ≤ yaw2 P Q δ F ‖T.v k‖ := by
  obtain ⟨hs, w0, w1, w2⟩ := windows T h k
  set s := ‖T.v k‖
  obtain ⟨hl0, hn0, hf0⟩ := frame_facts T a₀ h hS hs w0
  obtain ⟨hl1, hn1, hf1⟩ := frame_facts T a₀ h hS hs w1
  obtain ⟨hl2, hn2, hf2⟩ := frame_facts T a₀ h hS hs w2
  have hsb := h.sb_lt s hs
  have dn0 := n_step T a₀ h hS hs w0 w1
  have e2 : k + 1 + 1 = k + 2 := rfl
  have dn1 := n_step T a₀ h hS hs w1 w2
  have dl0 := l_step T a₀ h hS hs w0 w1
  have dl1 := l_step T a₀ h hS hs w1 w2
  rw [e2] at dn1 dl1
  have d2n := n_second T a₀ h hS hs w0 w1 w2
  have xn := n_cross_second T a₀ h hS hs w0 w1 w2
  have d2l := l_second T a₀ h hS hs w0 w1 w2
  obtain ⟨s10, s20⟩ := B_step_le T a₀ h hS k hs w0 w1
  obtain ⟨s11, s21⟩ := B_step_le T a₀ h hS (k + 1) hs w1 w2
  rw [e2] at s11 s21
  simp only [B1, B2] at s10 s11 s20 s21
  have hdb := And.intro s10 (And.intro s11 (And.intro s20 s21))
  have rp := lat_aVec_rp_second hn0 hn1 hn2 hl0 hl1 hl2 hf0 hf1 hf2 hsb dn0 d2n xn hdb
  have yw := lat_aVec_yaw_second hn0 hn1 hn2 hl0 hl1 hl2 hf0 hf1 hf2 hsb dn0 dn1 dl0 dl1 d2n xn
    d2l hdb
  simp only [av, B1, B2]
  rw [e2]
  refine ⟨?_, yw⟩
  unfold da
  exact da_aux (R := rp2 P Q δ F s) rp yw

theorem drate_le : ‖(kp T a₀ h hS).rate (k + 1) - (kp T a₀ h hS).rate k‖ ≤ dΩ P Q δ F ‖T.v k‖ ∧
    |((kp T a₀ h hS).rate (k + 1) - (kp T a₀ h hS).rate k).ofLp 2| ≤ dΩz P Q δ F ‖T.v k‖ := by
  obtain ⟨hs, w0, w1, w2⟩ := windows T h k
  have a0 := av_le T a₀ h hS hs w0 w1
  have a1 : ‖av T a₀ (Q := Q) (F := F) (k + 1)‖ ≤ θa P Q δ F ‖T.v k‖ := av_le T a₀ h hS hs w1 w2
  obtain ⟨P1, P2⟩ := psiVec_sub_le a0 a1 (h.θ_lt _ hs)
  obtain ⟨D1, D2⟩ := dav_le T a₀ h hS k
  have hδ := h.δ_pos
  rw [kp_rate, kp_rate, ← smul_sub]
  have hG : 1 / √(1 - θa P Q δ F ‖T.v k‖ ^ 2) = Gψ P Q δ F ‖T.v k‖ := rfl
  have hGpos : 0 ≤ Gψ P Q δ F ‖T.v k‖ := by unfold Gψ; positivity
  constructor
  · rw [norm_smul, norm_inv, Real.norm_of_nonneg hδ.le, inv_mul_eq_div]
    apply div_le_div_of_nonneg_right _ hδ.le
    refine P1.trans ?_
    rw [div_eq_mul_one_div, hG, mul_comm]
    have := mul_le_mul_of_nonneg_left D1 hGpos
    linarith
  · simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
    rw [abs_div, abs_of_pos hδ]
    apply div_le_div_of_nonneg_right _ hδ.le
    refine (P2 2).trans ?_
    rw [div_eq_mul_one_div, hG, mul_comm]
    have := mul_le_mul_of_nonneg_left D2 hGpos
    unfold dΩz at *
    linarith

theorem kp_rate_le : ‖(kp T a₀ h hS).rate k‖ ≤ Ωb P Q δ F ‖T.v k‖ := by
  obtain ⟨hs, w0, w1, -⟩ := windows T h k
  rw [kp_rate, norm_smul, norm_inv, Real.norm_of_nonneg h.δ_pos.le, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (rate_le_Ωb T a₀ h hS k hs w0 w1) h.δ_pos.le

theorem kp_torque_le : ‖(kp T a₀ h hS).torque k‖ ≤ τrp P Q δ F ‖T.v k‖ := by
  unfold KinPlan.torque τrp
  have hJ : 0 ≤ Budget.Jmax Q := le_trans Q.Jx_pos.le (le_max_left _ _)
  have hδ := h.δ_pos
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (inertia_norm_le Q _).trans ?_
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hδ.le, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hJ
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (drate_le T a₀ h hS k).1 hδ.le
  · refine (norm_cross_le _ _).trans ?_
    have h1 := kp_rate_le T a₀ h hS k
    have h2 := inertia_norm_le Q ((kp T a₀ h hS).rate k)
    have h0 := norm_nonneg ((kp T a₀ h hS).rate k)
    calc ‖(kp T a₀ h hS).rate k‖ * ‖Q.inertia ((kp T a₀ h hS).rate k)‖
        ≤ ‖(kp T a₀ h hS).rate k‖ * (Budget.Jmax Q * ‖(kp T a₀ h hS).rate k‖) :=
          mul_le_mul_of_nonneg_left h2 h0
      _ ≤ Budget.Jmax Q * Ωb P Q δ F ‖T.v k‖ ^ 2 := by
          nlinarith [mul_le_mul h1 h1 h0 (h0.trans h1)]

theorem kp_torque_yaw_le : |((kp T a₀ h hS).torque k).ofLp 2| ≤ τyaw P Q δ F ‖T.v k‖ := by
  set Ω := (kp T a₀ h hS).rate k
  have hδ := h.δ_pos
  have e : ((kp T a₀ h hS).torque k).ofLp 2
      = Q.Jz * (δ⁻¹ * ((kp T a₀ h hS).rate (k + 1) - Ω).ofLp 2)
        + (Q.Jy - Q.Jx) * (Ω.ofLp 0 * Ω.ofLp 1) := by
    simp only [KinPlan.torque, WithLp.ofLp_add, Pi.add_apply, QuadParams.inertia, cross,
      crossProduct]
    simp [Ω]
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos Q.Jz_pos, abs_mul, abs_inv, abs_of_pos hδ, mul_div_assoc,
      inv_mul_eq_div]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (drate_le T a₀ h hS k).2 hδ.le) Q.Jz_pos.le
  · rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have a0 := abs_coord_le Ω 0
    have a1 := abs_coord_le Ω 1
    have hr := kp_rate_le T a₀ h hS k
    rw [abs_mul]
    have := mul_le_mul (a0.trans hr) (a1.trans hr) (abs_nonneg _) ((norm_nonneg _).trans hr)
    nlinarith

theorem kp_mix : MixerOK Q (Q.mass * ‖(kp T a₀ h hS).thrust k‖) ((kp T a₀ h hS).torque k) := by
  obtain ⟨hs, w0, -, -⟩ := windows T h k
  have hτ := kp_torque_le T a₀ h hS k
  have hy := kp_torque_yaw_le T a₀ h hS k
  have hm := Q.mass_pos
  have hL : 0 < 2 * Q.arm := by linarith [Q.arm_pos]
  have hk : 0 < 4 * Q.kYaw := by linarith [Q.kYaw_pos]
  have hT1 : Tlo P Q δ F ‖T.v k‖ ≤ ‖(kp T a₀ h hS).thrust k‖ := by
    rw [kp_thrust]; exact thr_norm_ge T a₀ h hS w0
  have hT2 : ‖(kp T a₀ h hS).thrust k‖ ≤ Thi P Q δ F ‖T.v k‖ := by
    rw [kp_thrust]; exact (thr_norm_le T a₀ h hS w0).1
  have b0 : |((kp T a₀ h hS).torque k).ofLp 0| / (2 * Q.arm) ≤ τrp P Q δ F ‖T.v k‖ / (2 * Q.arm) :=
    div_le_div_of_nonneg_right ((abs_coord_le _ 0).trans hτ) hL.le
  have b1 : |((kp T a₀ h hS).torque k).ofLp 1| / (2 * Q.arm) ≤ τrp P Q δ F ‖T.v k‖ / (2 * Q.arm) :=
    div_le_div_of_nonneg_right ((abs_coord_le _ 1).trans hτ) hL.le
  have b2 : |((kp T a₀ h hS).torque k).ofLp 2| / (4 * Q.kYaw) ≤ τyaw P Q δ F ‖T.v k‖ / (4 * Q.kYaw) :=
    div_le_div_of_nonneg_right hy hk.le
  have m1 : Q.mass * Tlo P Q δ F ‖T.v k‖ / 4 ≤ Q.mass * ‖(kp T a₀ h hS).thrust k‖ / 4 := by
    have := mul_le_mul_of_nonneg_left hT1 hm.le; linarith
  have m2 : Q.mass * ‖(kp T a₀ h hS).thrust k‖ / 4 ≤ Q.mass * Thi P Q δ F ‖T.v k‖ / 4 := by
    have := mul_le_mul_of_nonneg_left hT2 hm.le; linarith
  have lo := h.mix_lo _ hs
  have hi := h.mix_hi _ hs
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end Torque

section Geometry

variable {s : ℝ} (hs : s ∈ Set.Icc P.vMin P.vMax) {j : ℕ}
  (hw : ‖T.v j‖ ∈ Set.Icc (sLo P δ s) (sHi P δ s))
include hs hw

theorem hP_facts : ‖hP T a₀ F j‖ = 1 ∧ ⟪hP T a₀ F j, up⟫ = 0 := by
  refine ⟨norm_nrm_horiz (horiz_vP_ne T a₀ h hS hw hs), ?_⟩
  rw [real_inner_comm]; exact inner_up_nrm_horiz _

theorem thr_pos : 0 < ‖thr T a₀ Q F j‖ :=
  (Tlo_pos h hs).trans_le (thr_norm_ge T a₀ h hS hw)

omit h hS hs hw in
theorem u3_eq : ⟪nP T a₀ Q F j, up⟫ = ⟪thr T a₀ Q F j, up⟫ / ‖thr T a₀ Q F j‖ := by
  rw [nP, nrm, real_inner_smul_left, inv_mul_eq_div]

theorem u3_pos : 0 < ⟪nP T a₀ Q F j, up⟫ := by
  rw [u3_eq T a₀]
  exact div_pos ((h.zlo_pos s hs).trans_le (thr_up T a₀ h hS hw).1) (thr_pos T a₀ h hS hs hw)

/-- The pitch ratio `u₁/u₃` in terms of the planned thrust. -/
theorem ratio_eq : ⟪B1 T a₀ Q F j, up⟫ / ⟪nP T a₀ Q F j, up⟫
    = ‖latRaw (lP T a₀ F j) (nP T a₀ Q F j)‖⁻¹ * ⟪hP T a₀ F j, thr T a₀ Q F j⟫
      / ⟪thr T a₀ Q F j, up⟫ := by
  obtain ⟨-, hhu⟩ := hP_facts T a₀ h hS hs hw
  have e := (lat_up_coords (n := nP T a₀ Q F j) hhu).1
  have hT := thr_pos T a₀ h hS hs hw
  rw [B1, show lP T a₀ F j = cross up (hP T a₀ F j) from rfl, e, u3_eq T a₀]
  rw [show nP T a₀ Q F j = ‖thr T a₀ Q F j‖⁻¹ • thr T a₀ Q F j from rfl, real_inner_smul_right]
  field_simp

theorem r_bounds : 1 ≤ ‖latRaw (lP T a₀ F j) (nP T a₀ Q F j)‖⁻¹ ∧
    ‖latRaw (lP T a₀ F j) (nP T a₀ Q F j)‖⁻¹ ≤ 1 / M P Q δ F s := by
  obtain ⟨hl, hn, hf⟩ := frame_facts T a₀ h hS hs hw
  have hsb := h.sb_lt s hs
  refine ⟨?_, inv_norm_latRaw_le hn hl hf hsb⟩
  have h1 := norm_latRaw_le_one hn hl
  have h0 : 0 < ‖latRaw (lP T a₀ F j) (nP T a₀ Q F j)‖ :=
    norm_pos_iff.2 (latRaw_ne hn hl (hf.trans_lt hsb))
  rw [one_le_inv₀ h0]; exact h1

theorem M_pos : 0 < M P Q δ F s := by
  have hsb := h.sb_lt s hs
  obtain ⟨-, -, hf⟩ := frame_facts T a₀ h hS hs hw
  have hsb0 : 0 ≤ sb P Q δ F s := (abs_nonneg _).trans hf
  exact Real.sqrt_pos.2 (by nlinarith)

theorem phi_mem : φlo P Q δ F s ≤ phi T a₀ Q F j ∧ phi T a₀ Q F j ≤ φhi P Q δ F s := by
  have hZ := h.zlo_pos s hs
  obtain ⟨zl, zh⟩ := thr_up T a₀ h hS hw
  have hY : 0 < ⟪thr T a₀ Q F j, up⟫ := hZ.trans_le zl
  obtain ⟨r1, rM⟩ := r_bounds T a₀ h hS hs hw
  have hM := M_pos T a₀ h hS hs hw
  set r := ‖latRaw (lP T a₀ F j) (nP T a₀ Q F j)‖⁻¹
  set X := ⟪hP T a₀ F j, thr T a₀ Q F j⟫
  set Y := ⟪thr T a₀ Q F j, up⟫
  have hX : Nlo P Q δ F s ≤ X := by
    rw [show X = ⟪thr T a₀ Q F j, hP T a₀ F j⟫ from real_inner_comm _ _]
    exact forward_ge T a₀ h hS hw hs
  have hXabs : |X| ≤ Hhi P Q δ F s := by
    obtain ⟨hh1, hhu⟩ := hP_facts T a₀ h hS hs hw
    have e : X = ⟪hP T a₀ F j, horiz (thr T a₀ Q F j)⟫ := by
      rw [horiz, inner_sub_right, real_inner_smul_right, hhu, mul_zero, sub_zero]
    rw [e]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hh1, one_mul]; exact (thr_norm_le T a₀ h hS hw).2
  unfold phi
  rw [ratio_eq T a₀ h hS hs hw]
  constructor
  · unfold φlo
    apply Real.arctan_strictMono.monotone
    split_ifs with hN
    · -- nonnegative forward thrust
      have hZh : 0 < Zhi P Q δ F s := hY.trans_le zh
      rw [div_le_div_iff₀ hZh hY]
      have k1 : Nlo P Q δ F s ≤ r * X := by nlinarith
      have k2 := mul_le_mul_of_nonneg_left zh hN
      have k3 := mul_le_mul_of_nonneg_right k1 hZh.le
      linarith
    · have hN' : Nlo P Q δ F s < 0 := not_le.1 hN
      have hZM : 0 < Zlo P Q δ F s * M P Q δ F s := mul_pos hZ hM
      rw [div_le_div_iff₀ hZM hY]
      have k3 : Nlo P Q δ F s * Y ≤ Nlo P Q δ F s * Zlo P Q δ F s :=
        mul_le_mul_of_nonpos_left zl hN'.le
      rcases le_or_gt 0 X with hX0 | hX0
      · have : 0 ≤ r * X * (Zlo P Q δ F s * M P Q δ F s) :=
          mul_nonneg (mul_nonneg (zero_le_one.trans r1) hX0) hZM.le
        nlinarith
      · have h1 : X / M P Q δ F s ≤ r * X := by
          rw [div_le_iff₀ hM]
          have : r * M P Q δ F s ≤ 1 := by
            have := mul_le_mul_of_nonneg_right rM hM.le
            rwa [div_mul_cancel₀ _ hM.ne'] at this
          nlinarith
        have h2 : Nlo P Q δ F s / M P Q δ F s ≤ X / M P Q δ F s :=
          div_le_div_of_nonneg_right hX hM.le
        have k1 : Nlo P Q δ F s / M P Q δ F s ≤ r * X := h2.trans h1
        have k2 := mul_le_mul_of_nonneg_right k1 hZM.le
        have e : Nlo P Q δ F s / M P Q δ F s * (Zlo P Q δ F s * M P Q δ F s)
            = Nlo P Q δ F s * Zlo P Q δ F s := by field_simp
        linarith
  · unfold φhi
    apply Real.arctan_strictMono.monotone
    have hZM : 0 < Zlo P Q δ F s * M P Q δ F s := mul_pos hZ hM
    rw [div_le_div_iff₀ hY hZM]
    have hHnn : 0 ≤ Hhi P Q δ F s := (abs_nonneg X).trans hXabs
    have h1 : r * X ≤ Hhi P Q δ F s / M P Q δ F s := by
      calc r * X ≤ r * |X| := mul_le_mul_of_nonneg_left (le_abs_self X) (zero_le_one.trans r1)
        _ ≤ 1 / M P Q δ F s * Hhi P Q δ F s :=
            mul_le_mul rM hXabs (abs_nonneg _) (by positivity)
        _ = Hhi P Q δ F s / M P Q δ F s := by ring
    have h2 := mul_le_mul_of_nonneg_right h1 hZM.le
    have h3 : Hhi P Q δ F s / M P Q δ F s * (Zlo P Q δ F s * M P Q δ F s)
        = Hhi P Q δ F s * Zlo P Q δ F s := by field_simp
    have h4 := mul_le_mul_of_nonneg_left zl hHnn
    linarith

/-- The in-plane radius of `e₃` in the frame. -/
theorem rho_ge : M P Q δ F s ≤ √(⟪nP T a₀ Q F j, up⟫ ^ 2 + ⟪B1 T a₀ Q F j, up⟫ ^ 2) := by
  obtain ⟨hl, hn, hf⟩ := frame_facts T a₀ h hS hs hw
  obtain ⟨u1, u2, u12, x⟩ := B_facts T a₀ h hS j
  obtain ⟨hh1, hhu⟩ := hP_facts T a₀ h hS hs hw
  have B := bessel_pair u1 u2 u12 up
  rw [x, norm_up'] at B
  -- |u₂| ≤ sb
  have e2 := (lat_up_coords (n := nP T a₀ Q F j) hhu).2
  have hlu : ⟪lP T a₀ F j, up⟫ = 0 := by rw [lP, real_inner_comm]; exact inner_cross_left _ _
  have hb := bessel_pair hl norm_up' (by rw [lP]; exact hlu) (nP T a₀ Q F j)
  rw [hn] at hb
  set f := ⟪lP T a₀ F j, nP T a₀ Q F j⟫
  have hm2 : ‖latRaw (lP T a₀ F j) (nP T a₀ Q F j)‖ ^ 2 = 1 - f ^ 2 := norm_latRaw_sq hn hl
  have hm0 : 0 < ‖latRaw (lP T a₀ F j) (nP T a₀ Q F j)‖ :=
    norm_pos_iff.2 (latRaw_ne hn hl (hf.trans_lt (h.sb_lt s hs)))
  have hu2 : ⟪B2 T a₀ Q F j, up⟫ ^ 2 ≤ sb P Q δ F s ^ 2 := by
    rw [B2, show lP T a₀ F j = cross up (hP T a₀ F j) from rfl, e2]
    rw [show cross up (hP T a₀ F j) = lP T a₀ F j from rfl]
    have hnz : ⟪nP T a₀ Q F j, up⟫ ^ 2 ≤ 1 - f ^ 2 := by
      rw [real_inner_comm (nP T a₀ Q F j) up] at hb
      nlinarith [sq_nonneg ⟪cross (lP T a₀ F j) up, nP T a₀ Q F j⟫]
    have hf2 : f ^ 2 ≤ sb P Q δ F s ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hf 2
    rw [mul_pow, mul_pow, inv_pow, hm2]
    have h1m : 0 < 1 - f ^ 2 := by rw [← hm2]; positivity
    rw [inv_mul_le_iff₀ h1m]
    have := mul_le_mul_of_nonneg_left hnz (sq_nonneg f)
    have := mul_le_mul_of_nonneg_right hf2 h1m.le
    linarith
  unfold M
  apply Real.sqrt_le_sqrt
  linarith

end Geometry

end Under

end VisionTracking
