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
      ≤ yaw2 P Q δ F ‖T.v k‖ ∧
    ((av T a₀ (Q := Q) (F := F) (k + 1)).ofLp 0 - (av T a₀ (Q := Q) (F := F) k).ofLp 0) ^ 2
      + ((av T a₀ (Q := Q) (F := F) (k + 1)).ofLp 1 - (av T a₀ (Q := Q) (F := F) k).ofLp 1) ^ 2
      ≤ rp2 P Q δ F ‖T.v k‖ ^ 2 := by
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
  have xn := n_cross_second T a₀ h hS hs w0 w1 w2
  have d2l := l_second T a₀ h hS hs w0 w1 w2
  obtain ⟨s10, s20⟩ := B_step_le T a₀ h hS k hs w0 w1
  obtain ⟨s11, s21⟩ := B_step_le T a₀ h hS (k + 1) hs w1 w2
  rw [e2] at s11 s21
  simp only [B1, B2] at s10 s11 s20 s21
  have hdb := And.intro s10 (And.intro s11 (And.intro s20 s21))
  have rp := lat_rp_sharp hn0 hn1 hn2 hl0 hl1 hl2 hf0 hf1 hf2 hsb dn0 dn1 dl0 dl1 xn hdb
  have yw := lat_yaw_sharp hn0 hn1 hn2 hl0 hl1 hl2 hf0 hf1 hf2 hsb dn0 dn1 dl0 dl1 xn d2l hdb
  simp only [av, B1, B2]
  rw [e2]
  refine ⟨?_, yw, rp⟩
  unfold da
  exact da_aux (R := rp2 P Q δ F s) rp yw

theorem drate_le : ‖(kp T a₀ h hS).rate (k + 1) - (kp T a₀ h hS).rate k‖ ≤ dΩ P Q δ F ‖T.v k‖ ∧
    |((kp T a₀ h hS).rate (k + 1) - (kp T a₀ h hS).rate k).ofLp 2| ≤ dΩz P Q δ F ‖T.v k‖ ∧
    |((kp T a₀ h hS).rate (k + 1) - (kp T a₀ h hS).rate k).ofLp 0| ≤ dΩrp P Q δ F ‖T.v k‖ ∧
    |((kp T a₀ h hS).rate (k + 1) - (kp T a₀ h hS).rate k).ofLp 1| ≤ dΩrp P Q δ F ‖T.v k‖ := by
  obtain ⟨hs, w0, w1, w2⟩ := windows T h k
  have a0 := av_le T a₀ h hS hs w0 w1
  have a1 : ‖av T a₀ (Q := Q) (F := F) (k + 1)‖ ≤ θa P Q δ F ‖T.v k‖ := av_le T a₀ h hS hs w1 w2
  obtain ⟨P1, P2⟩ := psiVec_sub_le a0 a1 (h.θ_lt _ hs)
  obtain ⟨D1, D2, D3⟩ := dav_le T a₀ h hS k
  have hδ := h.δ_pos
  have hG : 1 / √(1 - θa P Q δ F ‖T.v k‖ ^ 2) = Gψ P Q δ F ‖T.v k‖ := rfl
  have hGpos : 0 ≤ Gψ P Q δ F ‖T.v k‖ := by unfold Gψ; positivity
  have comp : ∀ i : Fin 3, |(av T a₀ (Q := Q) (F := F) (k + 1)).ofLp i
      - (av T a₀ (Q := Q) (F := F) k).ofLp i| ≤ |rp2 P Q δ F ‖T.v k‖| →
      |((kp T a₀ h hS).rate (k + 1) - (kp T a₀ h hS).rate k).ofLp i| ≤ dΩrp P Q δ F ‖T.v k‖ := by
    intro i hai
    rw [kp_rate, kp_rate, ← smul_sub]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
    rw [abs_div, abs_of_pos hδ]
    unfold dΩrp
    apply div_le_div_of_nonneg_right _ hδ.le
    refine (P2 i).trans ?_
    rw [div_eq_mul_one_div, hG, mul_comm]
    have := mul_le_mul_of_nonneg_left hai hGpos
    linarith
  have h0 : |(av T a₀ (Q := Q) (F := F) (k + 1)).ofLp 0 - (av T a₀ (Q := Q) (F := F) k).ofLp 0|
      ≤ |rp2 P Q δ F ‖T.v k‖| := by
    apply sq_le_sq.mp
    nlinarith [sq_nonneg ((av T a₀ (Q := Q) (F := F) (k + 1)).ofLp 1
      - (av T a₀ (Q := Q) (F := F) k).ofLp 1)]
  have h1 : |(av T a₀ (Q := Q) (F := F) (k + 1)).ofLp 1 - (av T a₀ (Q := Q) (F := F) k).ofLp 1|
      ≤ |rp2 P Q δ F ‖T.v k‖| := by
    apply sq_le_sq.mp
    nlinarith [sq_nonneg ((av T a₀ (Q := Q) (F := F) (k + 1)).ofLp 0
      - (av T a₀ (Q := Q) (F := F) k).ofLp 0)]
  refine ⟨?_, ?_, comp 0 h0, comp 1 h1⟩
  · rw [kp_rate, kp_rate, ← smul_sub]
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hδ.le, inv_mul_eq_div]
    apply div_le_div_of_nonneg_right _ hδ.le
    refine P1.trans ?_
    rw [div_eq_mul_one_div, hG, mul_comm]
    have := mul_le_mul_of_nonneg_left D1 hGpos
    linarith
  · rw [kp_rate, kp_rate, ← smul_sub]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
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

theorem kp_torque_rp_le : |((kp T a₀ h hS).torque k).ofLp 0| ≤ τrp P Q δ F ‖T.v k‖ ∧
    |((kp T a₀ h hS).torque k).ofLp 1| ≤ τrp P Q δ F ‖T.v k‖ := by
  set Ω := (kp T a₀ h hS).rate k
  have hδ := h.δ_pos
  obtain ⟨-, -, D0, D1⟩ := drate_le T a₀ h hS k
  have hr := kp_rate_le T a₀ h hS k
  have hprod : ∀ a b : Fin 3, |Ω.ofLp a * Ω.ofLp b| ≤ Ωb P Q δ F ‖T.v k‖ ^ 2 := by
    intro a b
    rw [abs_mul]
    have := mul_le_mul ((abs_coord_le Ω a).trans hr) ((abs_coord_le Ω b).trans hr)
      (abs_nonneg _) ((norm_nonneg _).trans hr)
    nlinarith
  have hJ : ∀ J x : ℝ, 0 < J → J ≤ Jxy Q → |x| ≤ dΩrp P Q δ F ‖T.v k‖ →
      |J * (δ⁻¹ * x)| ≤ Jxy Q * dΩrp P Q δ F ‖T.v k‖ / δ := by
    intro J x hJ0 hJle hx
    rw [abs_mul, abs_of_pos hJ0, abs_mul, abs_inv, abs_of_pos hδ, mul_div_assoc, inv_mul_eq_div]
    have hd : |x| / δ ≤ dΩrp P Q δ F ‖T.v k‖ / δ := div_le_div_of_nonneg_right hx hδ.le
    exact mul_le_mul hJle hd (by positivity) (le_trans hJ0.le hJle)
  have hg : ∀ x : ℝ, |x| ≤ Jg Q → ∀ a b : Fin 3,
      |x * (Ω.ofLp a * Ω.ofLp b)| ≤ Jg Q * Ωb P Q δ F ‖T.v k‖ ^ 2 := by
    intro x hx a b
    rw [abs_mul]; exact mul_le_mul hx (hprod a b) (abs_nonneg _) ((abs_nonneg _).trans hx)
  have e0 : ((kp T a₀ h hS).torque k).ofLp 0
      = Q.Jx * (δ⁻¹ * ((kp T a₀ h hS).rate (k + 1) - Ω).ofLp 0)
        + (Q.Jz - Q.Jy) * (Ω.ofLp 1 * Ω.ofLp 2) := by
    simp only [KinPlan.torque, WithLp.ofLp_add, Pi.add_apply, QuadParams.inertia, cross,
      crossProduct]
    simp [Ω]; ring
  have e1 : ((kp T a₀ h hS).torque k).ofLp 1
      = Q.Jy * (δ⁻¹ * ((kp T a₀ h hS).rate (k + 1) - Ω).ofLp 1)
        + (Q.Jx - Q.Jz) * (Ω.ofLp 0 * Ω.ofLp 2) := by
    simp only [KinPlan.torque, WithLp.ofLp_add, Pi.add_apply, QuadParams.inertia, cross,
      crossProduct]
    simp [Ω]; ring
  unfold τrp
  constructor
  · rw [e0]
    exact (abs_add_le _ _).trans (add_le_add (hJ _ _ Q.Jx_pos (le_max_left _ _) D0)
      (hg _ (le_max_left _ _) _ _))
  · rw [e1]
    exact (abs_add_le _ _).trans (add_le_add (hJ _ _ Q.Jy_pos (le_max_right _ _) D1)
      (hg _ (le_max_right _ _) _ _))

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
      (div_le_div_of_nonneg_right (drate_le T a₀ h hS k).2.1 hδ.le) Q.Jz_pos.le
  · rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have a0 := abs_coord_le Ω 0
    have a1 := abs_coord_le Ω 1
    have hr := kp_rate_le T a₀ h hS k
    rw [abs_mul]
    have := mul_le_mul (a0.trans hr) (a1.trans hr) (abs_nonneg _) ((norm_nonneg _).trans hr)
    nlinarith

omit T a₀ h hS in
theorem min_le_ratio {V X N sL sH Vt Tl Th : ℝ} (hV1 : sL ≤ V) (hV2 : V ≤ sH) (hsL : 0 ≤ sL)
    (hX : Vt ≤ X) (hN1 : Tl ≤ N) (hN2 : N ≤ Th) (hTl : 0 < Tl) :
    min (sL * Vt / Th) (sH * Vt / Tl) ≤ V * X / N := by
  have hN : 0 < N := hTl.trans_le hN1
  have hTh : 0 < Th := hN.trans_le hN2
  have hsH : 0 ≤ sH := (hsL.trans hV1).trans hV2
  rcases le_or_gt 0 X with hX0 | hX0
  · refine (min_le_left _ _).trans ?_
    calc sL * Vt / Th ≤ sL * X / Th :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hX hsL) hTh.le
      _ ≤ V * X / Th := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hV1 hX0) hTh.le
      _ ≤ V * X / N := div_le_div_of_nonneg_left (mul_nonneg (hsL.trans hV1) hX0) hN hN2
  · refine (min_le_right _ _).trans ?_
    calc sH * Vt / Tl ≤ sH * X / Tl :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hX hsH) hTl.le
      _ ≤ sH * X / N := by
          rw [div_le_div_iff₀ hTl hN]
          have : sH * X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hsH hX0.le
          nlinarith
      _ ≤ V * X / N :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonpos_right hV2 hX0.le) hN.le

omit hS in
theorem sLp_nonneg {s : ℝ} (hs : s ∈ Set.Icc P.vMin P.vMax) : 0 ≤ sLp P δ F s := by
  have hvh := h.vh_pos s hs
  have hc : Real.cos P.climbMax ≤ 1 := Real.cos_le_one _
  have hlo : 0 ≤ sLo P δ s := le_trans P.vMin_pos.le (le_max_left _ _)
  unfold vh at hvh; unfold sLp
  nlinarith [mul_le_mul_of_nonneg_left hc hlo]

/-- **Power of the planned thrust.** -/
theorem vP_thr_ge : VTlo P Q δ F ‖T.v k‖ ≤ ⟪vP T a₀ F k, thr T a₀ Q F k⟫ ∧
    sLp P δ F ‖T.v k‖ ≤ ‖vP T a₀ F k‖ ∧ ‖vP T a₀ F k‖ ≤ sHp P δ F ‖T.v k‖ := by
  obtain ⟨hs, w0, -, -⟩ := windows T h k
  set s := ‖T.v k‖
  have e := vP_err T a₀ h hS k
  have hv1 : sLp P δ F s ≤ ‖vP T a₀ F k‖ := by
    have := norm_le_insert' (T.v k) (vP T a₀ F k)
    rw [norm_sub_rev] at this; unfold sLp; linarith [w0.1]
  have hv2 : ‖vP T a₀ F k‖ ≤ sHp P δ F s := by unfold sHp; exact vP_le T a₀ h hS w0
  have hsL : 0 ≤ sLp P δ F s := sLp_nonneg h hs
  refine ⟨?_, hv1, hv2⟩
  have hthr : thr T a₀ Q F k = F.planAcc T a₀ k + Q.g • up
      + (Q.drag * ‖vP T a₀ F k‖) • vP T a₀ F k := rfl
  rw [hthr, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  have a1 : -(sHp P δ F s * (A P δ s + εD P δ F)) ≤ ⟪vP T a₀ F k, F.planAcc T a₀ k⟫ := by
    have := neg_abs_le ⟪vP T a₀ F k, F.planAcc T a₀ k⟫
    have h2 := abs_real_inner_le_norm (vP T a₀ F k) (F.planAcc T a₀ k)
    have h3 := planAcc_le T a₀ h hS w0
    have h4 := mul_le_mul hv2 h3 (norm_nonneg _) (hsL.trans hv1 |>.trans hv2)
    linarith
  have a2 : -(s * Real.sin P.climbMax + εV P δ F) ≤ ⟪vP T a₀ F k, up⟫ := by
    have hcl := (abs_le.1 (T.climb_le k)).1
    have := inner_up_sub_le (vP T a₀ F k) (T.v k)
    have h5 : |⟪vP T a₀ F k - T.v k, up⟫| ≤ εV P δ F := by
      have := abs_real_inner_le_norm (vP T a₀ F k - T.v k) up
      rw [norm_up', mul_one] at this; exact this.trans e
    rw [inner_sub_left] at h5
    linarith [(abs_le.1 h5).1]
  have a2' : -(sHi P δ s * Real.sin P.climbMax + εV P δ F) ≤ ⟪vP T a₀ F k, up⟫ := by
    have := mul_le_mul_of_nonneg_right w0.2 (sin_climb_nonneg P)
    linarith
  have a3 : Q.drag * sLp P δ F s ^ 3 ≤ Q.drag * ‖vP T a₀ F k‖ * ‖vP T a₀ F k‖ ^ 2 := by
    have := pow_le_pow_left₀ hsL hv1 3
    nlinarith [Q.drag_pos]
  unfold VTlo
  have := mul_le_mul_of_nonneg_left a2' Q.g_pos.le
  nlinarith

/-- **Sharp thrust bound.** The turn acceleration is normal to the velocity, so it does not
add linearly to the drag. -/
theorem thr_norm_le_Nhi : ‖thr T a₀ Q F k‖ ≤ Nhi P Q δ F ‖T.v k‖ := by
  obtain ⟨hs, w0, -, -⟩ := windows T h k
  set s := ‖T.v k‖
  have hδ := h.δ_pos
  have hc := Q.drag_pos
  have hg := Q.g_pos
  have eV0 := εV_nonneg T a₀ h hS
  have eD0 := εD_nonneg T a₀ h hS
  have hsg := sin_climb_nonneg P
  have hA0 : 0 ≤ A P δ s := by
    unfold A; have := P.aTan_nonneg; have := P.turnRadius_pos; positivity
  have hsHi : 0 ≤ sHi P δ s := (norm_nonneg _).trans w0.2
  set pa := F.planAcc T a₀ k
  set vp := vP T a₀ F k
  set v := T.v k
  set aT := δ⁻¹ • (T.v (k + 1) - T.v k)
  set V := ‖vp‖
  have e1 : ‖pa - aT‖ ≤ εD P δ F := acc_err T a₀ h hS k
  have e2 : ‖vp - v‖ ≤ εV P δ F := vP_err T a₀ h hS k
  have hpa : ‖pa‖ ≤ A P δ s + εD P δ F := planAcc_le T a₀ h hS w0
  have hV : V ≤ sHp P δ F s := vP_le T a₀ h hS w0
  have hv : ‖v‖ ≤ sHi P δ s := w0.2
  -- along-track acceleration
  have tang : ⟪v, aT⟫ ≤ P.aTan * sHi P δ s := by
    have ht := (abs_le.1 (T.tangential k)).2
    rw [real_inner_comm, real_inner_smul_left]
    have := mul_le_mul_of_nonneg_left ht (inv_pos.2 hδ).le
    rw [show δ⁻¹ * (δ * P.aTan * ‖T.v k‖) = P.aTan * ‖T.v k‖ by field_simp] at this
    have := mul_le_mul_of_nonneg_left hv P.aTan_nonneg
    linarith
  have i1 : ⟪vp, pa⟫ ≤ εV P δ F * (A P δ s + εD P δ F) + sHi P δ s * εD P δ F
      + P.aTan * sHi P δ s := by
    have sp : ⟪vp, pa⟫ = ⟪vp - v, pa⟫ + ⟪v, pa - aT⟫ + ⟪v, aT⟫ := by
      simp only [inner_sub_left, inner_sub_right]; ring
    have a1 : ⟪vp - v, pa⟫ ≤ εV P δ F * (A P δ s + εD P δ F) :=
      (real_inner_le_norm _ _).trans (mul_le_mul e2 hpa (norm_nonneg _) eV0)
    have a2 : ⟪v, pa - aT⟫ ≤ sHi P δ s * εD P δ F :=
      (real_inner_le_norm _ _).trans (mul_le_mul hv e1 (norm_nonneg _) hsHi)
    linarith
  have i2 : ⟪vp, up⟫ ≤ sHi P δ s * Real.sin P.climbMax + εV P δ F := by
    have hcl := (abs_le.1 (T.climb_le k)).2
    have b1 : ⟪vp - v, up⟫ ≤ εV P δ F := by
      have := real_inner_le_norm (vp - v) up; rw [norm_up', mul_one] at this
      exact this.trans e2
    rw [inner_sub_left] at b1
    have := mul_le_mul_of_nonneg_right hv hsg
    linarith
  have hr : ⟪pa + Q.g • up, vp⟫ ≤ Pv P Q δ F s := by
    rw [inner_add_left, real_inner_smul_left, real_inner_comm, real_inner_comm vp up]
    unfold Pv
    have := mul_le_mul_of_nonneg_left i2 hg.le
    linarith
  have hPv : 0 ≤ Pv P Q δ F s := by
    unfold Pv; have := P.aTan_nonneg; positivity
  have hup : ⟪pa, up⟫ ≤ P.aVert + εD P δ F := by
    have := (abs_le.1 (targetAcc_up_abs_le T hδ k)).2
    have b1 : ⟪pa - aT, up⟫ ≤ εD P δ F := by
      have := real_inner_le_norm (pa - aT) up; rw [norm_up', mul_one] at this
      exact this.trans e1
    rw [inner_sub_left] at b1
    linarith
  have huu : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up']; norm_num
  have hR : ‖pa + Q.g • up‖ ^ 2 ≤ Rr2 P Q δ F s := by
    rw [norm_add_sq_real, norm_smul, norm_up', mul_one, Real.norm_of_nonneg hg.le,
      real_inner_smul_right]
    unfold Rr2
    have := pow_le_pow_left₀ (norm_nonneg _) hpa 2
    have := mul_le_mul_of_nonneg_left hup (by positivity : (0 : ℝ) ≤ 2 * Q.g)
    nlinarith
  have hthr : thr T a₀ Q F k = (pa + Q.g • up) + (Q.drag * V) • vp := rfl
  have hsq : ‖thr T a₀ Q F k‖ ^ 2
      = ‖pa + Q.g • up‖ ^ 2 + 2 * (Q.drag * V) * ⟪pa + Q.g • up, vp⟫ + Q.drag ^ 2 * V ^ 4 := by
    rw [hthr, norm_add_sq_real, norm_smul, real_inner_smul_right,
      Real.norm_of_nonneg (mul_nonneg hc.le (norm_nonneg _))]
    ring
  have hV0 : 0 ≤ V := norm_nonneg _
  have t1 : Q.drag * V * ⟪pa + Q.g • up, vp⟫ ≤ Q.drag * sHp P δ F s * Pv P Q δ F s := by
    have := mul_le_mul_of_nonneg_left hr (mul_nonneg hc.le hV0)
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV hc.le) hPv
    linarith
  have t2 : V ^ 4 ≤ sHp P δ F s ^ 4 := pow_le_pow_left₀ hV0 hV 4
  unfold Nhi
  rw [← Real.sqrt_sq (norm_nonneg (thr T a₀ Q F k))]
  apply Real.sqrt_le_sqrt
  rw [hsq]
  nlinarith [mul_le_mul_of_nonneg_left t2 (sq_nonneg Q.drag)]

/-- **Collective bounds** with the rotor-disc normal force. -/
theorem kp_collective : Clo P Q δ F ‖T.v k‖ ≤ (kp T a₀ h hS).collective k ∧
    (kp T a₀ h hS).collective k ≤ Chi P Q δ F ‖T.v k‖ := by
  obtain ⟨hs, w0, -, -⟩ := windows T h k
  set s := ‖T.v k‖
  obtain ⟨hX, hv1, hv2⟩ := vP_thr_ge T a₀ h hS k
  have hT1 := thr_norm_ge T a₀ h hS w0
  have hT2 := (thr_norm_le T a₀ h hS w0).1
  have hTlo := Tlo_pos h hs
  have hkn := Q.normalDrag_nonneg
  have hcol : (kp T a₀ h hS).collective k = ‖thr T a₀ Q F k‖
      + Q.normalDrag * ‖vP T a₀ F k‖ * ⟪vP T a₀ F k, nP T a₀ Q F k⟫ := by
    simp only [KinPlan.collective]; rw [kp_thrust, kp_b₃]; rfl
  have hsL : 0 ≤ sLp P δ F s := sLp_nonneg h hs
  have hthr0 : 0 < ‖thr T a₀ Q F k‖ := hTlo.trans_le hT1
  have hn : ⟪vP T a₀ F k, nP T a₀ Q F k⟫ = ⟪vP T a₀ F k, thr T a₀ Q F k⟫ / ‖thr T a₀ Q F k‖ := by
    rw [nP, nrm, real_inner_smul_right]; field_simp
  rw [hcol]
  constructor
  · unfold Clo
    have key : min (sLp P δ F s * VTlo P Q δ F s / Thi P Q δ F s)
        (sHp P δ F s * VTlo P Q δ F s / Tlo P Q δ F s)
        ≤ ‖vP T a₀ F k‖ * ⟪vP T a₀ F k, nP T a₀ Q F k⟫ := by
      rw [hn, ← mul_div_assoc]
      exact min_le_ratio hv1 hv2 hsL hX hT1 hT2 hTlo
    have := mul_le_mul_of_nonneg_left key hkn
    nlinarith
  · unfold Chi
    have hT2 : ‖thr T a₀ Q F k‖ ≤ min (Thi P Q δ F s) (Nhi P Q δ F s) :=
      le_min hT2 (thr_norm_le_Nhi T a₀ h hS k)
    have h1 : ⟪vP T a₀ F k, nP T a₀ Q F k⟫ ≤ ‖vP T a₀ F k‖ := by
      have := real_inner_le_norm (vP T a₀ F k) (nP T a₀ Q F k)
      rwa [nP_unit T a₀ h hS w0 hs, mul_one] at this
    have h2 : ‖vP T a₀ F k‖ * ⟪vP T a₀ F k, nP T a₀ Q F k⟫ ≤ sHp P δ F s ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (norm_nonneg (vP T a₀ F k))
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) hv2 2]
    have := mul_le_mul_of_nonneg_left h2 hkn
    nlinarith

theorem kp_mix : MixerOK Q (Q.mass * (kp T a₀ h hS).collective k) ((kp T a₀ h hS).torque k) := by
  obtain ⟨hs, w0, -, -⟩ := windows T h k
  have hy := kp_torque_yaw_le T a₀ h hS k
  have hm := Q.mass_pos
  have hL : 0 < 2 * Q.arm := by linarith [Q.arm_pos]
  have hk : 0 < 4 * Q.kYaw := by linarith [Q.kYaw_pos]
  obtain ⟨hT1, hT2⟩ := kp_collective T a₀ h hS k
  have b0 : |((kp T a₀ h hS).torque k).ofLp 0| / (2 * Q.arm) ≤ τrp P Q δ F ‖T.v k‖ / (2 * Q.arm) :=
    div_le_div_of_nonneg_right (kp_torque_rp_le T a₀ h hS k).1 hL.le
  have b1 : |((kp T a₀ h hS).torque k).ofLp 1| / (2 * Q.arm) ≤ τrp P Q δ F ‖T.v k‖ / (2 * Q.arm) :=
    div_le_div_of_nonneg_right (kp_torque_rp_le T a₀ h hS k).2 hL.le
  have b2 : |((kp T a₀ h hS).torque k).ofLp 2| / (4 * Q.kYaw) ≤ τyaw P Q δ F ‖T.v k‖ / (4 * Q.kYaw) :=
    div_le_div_of_nonneg_right hy hk.le
  have m1 : Q.mass * Clo P Q δ F ‖T.v k‖ / 4 ≤ Q.mass * (kp T a₀ h hS).collective k / 4 := by
    have := mul_le_mul_of_nonneg_left hT1 hm.le; linarith
  have m2 : Q.mass * (kp T a₀ h hS).collective k / 4 ≤ Q.mass * Chi P Q δ F ‖T.v k‖ / 4 := by
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

section Final

theorem nP_tilt (k : ℕ) : angle (nP T a₀ Q F k) up ≤ Q.tiltMax := by
  obtain ⟨hs, w0, -, -⟩ := windows T h k
  have hZ := h.zlo_pos _ hs
  obtain ⟨zl, -⟩ := thr_up T a₀ h hS w0
  have hH := (thr_norm_le T a₀ h hS w0).2
  have hpos := thr_pos T a₀ h hS hs w0
  rw [nP, nrm, angle_smul_left_of_pos _ _ (inv_pos.2 hpos), angle_up_eq_arctan (by linarith)]
  refine le_trans ?_ (h.tilt _ hs)
  apply Real.arctan_strictMono.monotone
  exact div_le_div₀ (by linarith [norm_nonneg (horiz (thr T a₀ Q F k))]) hH hZ zl

theorem eta_rate (k : ℕ) : |eta T a₀ Q C F (k + 1) - eta T a₀ Q C F k| ≤ δ * C.hingeRate := by
  obtain ⟨hs, w0, w1, -⟩ := windows T h k
  set s := ‖T.v k‖
  refine (clamp_lip _ _ _ _).trans ?_
  have e : π / 2 - phi T a₀ Q F (k + 1) - (π / 2 - phi T a₀ Q F k)
      = -(phi T a₀ Q F (k + 1) - phi T a₀ Q F k) := by ring
  rw [e, abs_neg]
  have hM := M_pos T a₀ h hS hs w0
  have key := abs_arctan_sub_le (u3_pos T a₀ h hS hs w0) (u3_pos T a₀ h hS hs w1) hM
    (rho_ge T a₀ h hS hs w0) (rho_ge T a₀ h hS hs w1)
  refine key.trans (le_trans ?_ (h.hinge s hs))
  unfold hingeStep
  have d3 : |⟪nP T a₀ Q F (k + 1), up⟫ - ⟪nP T a₀ Q F k, up⟫| ≤ dn P Q δ F s :=
    (inner_up_sub_le _ _).trans (n_step T a₀ h hS hs w0 w1)
  have d1 : |⟪B1 T a₀ Q F (k + 1), up⟫ - ⟪B1 T a₀ Q F k, up⟫| ≤ db P Q δ F s :=
    (inner_up_sub_le _ _).trans (B_step_le T a₀ h hS k hs w0 w1).1
  have : (|⟪nP T a₀ Q F (k + 1), up⟫ - ⟪nP T a₀ Q F k, up⟫|
      + |⟪B1 T a₀ Q F (k + 1), up⟫ - ⟪B1 T a₀ Q F k, up⟫|) / M P Q δ F s
      ≤ (db P Q δ F s + dn P Q δ F s) / M P Q δ F s :=
    div_le_div_of_nonneg_right (by linarith) hM.le
  have hpi : 0 ≤ π / 2 := by positivity
  calc π / 2 * ((|⟪nP T a₀ Q F (k + 1), up⟫ - ⟪nP T a₀ Q F k, up⟫|
        + |⟪B1 T a₀ Q F (k + 1), up⟫ - ⟪B1 T a₀ Q F k, up⟫|) / M P Q δ F s)
      ≤ π / 2 * ((db P Q δ F s + dn P Q δ F s) / M P Q δ F s) :=
        mul_le_mul_of_nonneg_left this hpi
    _ = π / 2 * (db P Q δ F s + dn P Q δ F s) / M P Q δ F s := by ring

theorem cam_up_angle (k : ℕ) :
    angle (frameCam (B1 T a₀ Q F k) (nP T a₀ Q F k) (eta T a₀ Q C F k)) up
      ≤ camOff P Q C δ F ‖T.v k‖ := by
  obtain ⟨hs, w0, -, -⟩ := windows T h k
  set s := ‖T.v k‖
  obtain ⟨u1, -, -, x⟩ := B_facts T a₀ h hS k
  have hn := nP_unit T a₀ h hS w0 hs
  have h13 : ⟪B1 T a₀ Q F k, nP T a₀ Q F k⟫ = 0 := by
    rw [← x]; exact inner_cross_left _ _
  have hc : ‖frameCam (B1 T a₀ Q F k) (nP T a₀ Q F k) (eta T a₀ Q C F k)‖ = 1 :=
    norm_cos_smul_add_sin_smul u1 hn h13 _
  have hin : ⟪frameCam (B1 T a₀ Q F k) (nP T a₀ Q F k) (eta T a₀ Q C F k), up⟫
      = Real.cos (eta T a₀ Q C F k) * ⟪B1 T a₀ Q F k, up⟫
        + Real.sin (eta T a₀ Q C F k) * ⟪nP T a₀ Q F k, up⟫ := by
    rw [frameCam, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [inner_cam_up_eq (u3_pos T a₀ h hS hs w0)] at hin
  -- the miss angle
  obtain ⟨plo, phi_⟩ := phi_mem T a₀ h hS hs w0
  have hmiss : |π / 2 - phi T a₀ Q F k - eta T a₀ Q C F k| ≤ miss P Q C δ F s := by
    unfold eta miss
    exact clamp_dist C.hingeLo_le (by linarith) (by linarith)
  have hm := h.miss_le s hs
  have hm0 : 0 ≤ miss P Q C δ F s := (abs_nonneg _).trans hmiss
  have hcos : Real.cos (miss P Q C δ F s)
      ≤ Real.cos (π / 2 - eta T a₀ Q C F k - phi T a₀ Q F k) := by
    rw [show π / 2 - eta T a₀ Q C F k - phi T a₀ Q F k = π / 2 - phi T a₀ Q F k - eta T a₀ Q C F k
      by ring, show Real.cos (π / 2 - phi T a₀ Q F k - eta T a₀ Q C F k)
        = Real.cos |π / 2 - phi T a₀ Q F k - eta T a₀ Q C F k| from (Real.cos_abs _).symm]
    have hmπ : miss P Q C δ F s ≤ π := by linarith [Real.pi_pos]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hmπ hmiss
  have hcm : 0 ≤ Real.cos (miss P Q C δ F s) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hm⟩
  have hρ := rho_ge T a₀ h hS hs w0
  have hge : M P Q δ F s * Real.cos (miss P Q C δ F s)
      ≤ ⟪frameCam (B1 T a₀ Q F k) (nP T a₀ Q F k) (eta T a₀ Q C F k), up⟫ := by
    rw [hin]
    have hM := M_pos T a₀ h hS hs w0
    calc M P Q δ F s * Real.cos (miss P Q C δ F s)
        ≤ √(⟪nP T a₀ Q F k, up⟫ ^ 2 + ⟪B1 T a₀ Q F k, up⟫ ^ 2) * Real.cos (miss P Q C δ F s) :=
          mul_le_mul_of_nonneg_right hρ hcm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by unfold phi at hcos; exact hcos) (Real.sqrt_nonneg _)
  rw [angle, hc, norm_up', mul_one, div_one]
  exact Real.arccos_le_arccos hge

/-- The underneath formation as a valid rigid-body quadrotor trajectory. -/
noncomputable def traj : QuadTraj Q C δ :=
  QuadTraj.ofPlan (kp T a₀ h hS) h.δ_pos.ne' (kp_hdir T a₀ h hS) (kp_mix T a₀ h hS)
    (fun k => by rw [kp_b₃]; exact nP_tilt T a₀ h hS k)
    (fun k => (kp_rate_le T a₀ h hS k).trans (h.rate _ (speed_mem T k)))
    (fun k => by
      obtain ⟨hs, w0, -, -⟩ := windows T h k
      have := vP_le T a₀ h hS w0
      have : sHi P δ ‖T.v k‖ ≤ P.vMax := min_le_left _ _
      show ‖vP T a₀ F k‖ ≤ Q.speedEnv
      linarith [h.speed])
    (fun k => le_max_left _ _)
    (fun k => max_le C.hingeLo_le (min_le_left _ _))
    (fun k => eta_rate T a₀ h hS k)

theorem traj_cam (k : ℕ) : (traj T a₀ h hS).cam k
    = frameCam (B1 T a₀ Q F k) (nP T a₀ Q F k) (eta T a₀ Q C F k) := by
  simp only [QuadTraj.cam, traj, QuadTraj.ofPlan]
  rw [kp_b₃]; rfl

/-- **Visibility in every frame** (camera on top, drone underneath). -/
theorem traj_keeps : KeepsInView C P.size (traj T a₀ h hS) T := by
  intro k
  have hρ : ‖F.planPos T a₀ ((-d) • up) k - (T.p k + (-d) • up)‖ ≤ ρ P δ F :=
    F.planPos_err_sharp T a₀ ((-d) • up) h.δ_pos hS.1 k
  have hx : (traj T a₀ h hS).x k = F.planPos T a₀ ((-d) • up) k := rfl
  set e := F.planPos T a₀ ((-d) • up) k - (T.p k + (-d) • up) with he
  have hlos : T.p k - (traj T a₀ h hS).x k = d • up + -e := by rw [hx, he]; module
  have hd := h.d_pos
  have hdu : ‖d • up‖ = d := by rw [norm_smul, norm_up', Real.norm_of_nonneg hd.le, mul_one]
  refine ⟨?_, ?_⟩
  · rw [hlos]
    refine (norm_add_le _ _).trans ?_
    rw [hdu, norm_neg]; linarith [h.range]
  · rw [traj_cam]
    have t1 := cam_up_angle T a₀ h hS k
    have t2 : angle up (T.p k - (traj T a₀ h hS).x k) ≤ μ P δ F d := by
      rw [hlos, ← angle_smul_left_of_pos up _ hd]
      have hlt : ‖-e‖ < ‖d • up‖ := by rw [norm_neg, hdu]; linarith [h.ρ_lt]
      refine (angle_add_le_arcsin hlt).trans ?_
      rw [norm_neg, hdu]
      exact Real.arcsin_le_arcsin (div_le_div_of_nonneg_right hρ hd.le)
    have := angle_le_angle_add_angle (frameCam (B1 T a₀ Q F k) (nP T a₀ Q F k)
      (eta T a₀ Q C F k)) up (T.p k - (traj T a₀ h hS).x k)
    linarith [h.see _ (speed_mem T k)]

end Final

end Under

end VisionTracking
