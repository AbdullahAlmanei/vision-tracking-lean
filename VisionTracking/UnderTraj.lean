import VisionTracking.UnderPlan
import VisionTracking.Master2
import VisionTracking.LookDown

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

end Under

end VisionTracking
