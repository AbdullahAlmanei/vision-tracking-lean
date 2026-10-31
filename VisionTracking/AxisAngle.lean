import VisionTracking.Rotation

/-!
# Axis-angle for nearby frames

Two right-handed orthonormal frames `(a₁, a₂, a₁ × a₂)` and `(c₁, c₂, c₁ × c₂)` whose
trace `t = Σ ⟪aᵢ, cᵢ⟫` exceeds `-1` (rotation angle `< π`) differ by a single
Rodrigues rotation `rotate ω`, with `‖ω‖ = arccos ((t - 1) / 2)`
(`exists_rotate_frame`). When each frame vector moves by at most `ε ≤ π/2`, the
rotation angle is at most `2ε` (`rotAngle_le`). This lets per-step attitude changes
be realised by the Rodrigues attitude update of `QuadTraj` with bounded body rates.
-/

set_option linter.unusedSimpArgs false

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

/-- The trace `Σ ⟪aᵢ, cᵢ⟫` of the rotation taking frame `a` to frame `c`. -/
noncomputable def frameTrace (a₁ a₂ c₁ c₂ : E3) : ℝ :=
  ⟪a₁, c₁⟫ + ⟪a₂, c₂⟫ + ⟪cross a₁ a₂, cross c₁ c₂⟫

/-- The rotation angle between two frames. -/
noncomputable def rotAngle (a₁ a₂ c₁ c₂ : E3) : ℝ :=
  Real.arccos ((frameTrace a₁ a₂ c₁ c₂ - 1) / 2)


/-! ## Core: frames relative to the standard basis -/

section Core

noncomputable def ex : E3 := EuclideanSpace.single 0 1
noncomputable def ey : E3 := EuclideanSpace.single 1 1

theorem ex_ofLp : ex.ofLp 0 = 1 ∧ ex.ofLp 1 = 0 ∧ ex.ofLp 2 = 0 := by simp [ex]
theorem ey_ofLp : ey.ofLp 0 = 0 ∧ ey.ofLp 1 = 1 ∧ ey.ofLp 2 = 0 := by simp [ey]

theorem coords_unit {r : E3} (h : ‖r‖ = 1) :
    (r.ofLp 0) ^ 2 + (r.ofLp 1) ^ 2 + (r.ofLp 2) ^ 2 = 1 := by
  have := norm_sq_coords r; rw [h] at this; linarith

theorem coords_orth {r s : E3} (h : ⟪r, s⟫ = 0) :
    r.ofLp 0 * s.ofLp 0 + r.ofLp 1 * s.ofLp 1 + r.ofLp 2 * s.ofLp 2 = 0 := by
  rw [← inner_eq_coords]; exact h

/-- `σ = ½ Σ eᵢ × cᵢ` for the frame `(r, s, r × s)` in standard coordinates. -/
noncomputable def sigmaVec (r s : E3) : E3 :=
  !₂[(r.ofLp 0)*(s.ofLp 2)/2 - (r.ofLp 2)*(s.ofLp 0)/2 + (s.ofLp 2)/2,
     (r.ofLp 1)*(s.ofLp 2)/2 - (r.ofLp 2)*(s.ofLp 1)/2 - (r.ofLp 2)/2,
     (r.ofLp 1)/2 - (s.ofLp 0)/2]

/-- `cos θ = (trace - 1) / 2` for the frame `(r, s, r × s)`. -/
noncomputable def cosTr (r s : E3) : ℝ :=
  (r.ofLp 0 + s.ofLp 1 + (r.ofLp 0 * s.ofLp 1 - r.ofLp 1 * s.ofLp 0) - 1) / 2

theorem sigmaVec_ofLp (r s : E3) :
    (sigmaVec r s).ofLp 0 = (r.ofLp 0)*(s.ofLp 2)/2 - (r.ofLp 2)*(s.ofLp 0)/2 + (s.ofLp 2)/2 ∧
    (sigmaVec r s).ofLp 1 = (r.ofLp 1)*(s.ofLp 2)/2 - (r.ofLp 2)*(s.ofLp 1)/2 - (r.ofLp 2)/2 ∧
    (sigmaVec r s).ofLp 2 = (r.ofLp 1)/2 - (s.ofLp 0)/2 := by
  simp [sigmaVec]

variable {r s : E3}

theorem core_ex (hr : (r.ofLp 0) ^ 2 + (r.ofLp 1) ^ 2 + (r.ofLp 2) ^ 2 = 1)
    (hs : (s.ofLp 0) ^ 2 + (s.ofLp 1) ^ 2 + (s.ofLp 2) ^ 2 = 1)
    (hrs : r.ofLp 0 * s.ofLp 0 + r.ofLp 1 * s.ofLp 1 + r.ofLp 2 * s.ofLp 2 = 0) :
    (1 + cosTr r s) • (r - cosTr r s • ex - cross (sigmaVec r s) ex)
      = ⟪sigmaVec r s, ex⟫ • sigmaVec r s := by
  obtain ⟨g0, g1, g2⟩ := sigmaVec_ofLp r s
  obtain ⟨e0, e1, e2⟩ := ex_ofLp
  ext j; fin_cases j
  · simp only [Fin.zero_eta, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two, g0, g1, g2, e0, e1, e2, inner_eq_coords, cosTr]
    linear_combination (-(s.ofLp 0)^2/4) * hr + (-(r.ofLp 0)^2/4 - (r.ofLp 0)/2 - 1/4) * hs + ((r.ofLp 0)*(s.ofLp 0)/2 + (s.ofLp 0)/2) * hrs
  · simp only [Fin.mk_one, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two, g0, g1, g2, e0, e1, e2, inner_eq_coords, cosTr]
    linear_combination (-(s.ofLp 0)*(s.ofLp 1)/4 - (s.ofLp 0)/4) * hr + (-(r.ofLp 0)*(r.ofLp 1)/4 - (r.ofLp 1)/4) * hs + ((r.ofLp 0)*(s.ofLp 1)/4 + (r.ofLp 0)/4 + (r.ofLp 1)*(s.ofLp 0)/4 + (s.ofLp 1)/4 + 1/4) * hrs
  · simp only [Fin.reduceFinMk, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two, g0, g1, g2, e0, e1, e2, inner_eq_coords, cosTr]
    linear_combination (-(s.ofLp 0)*(s.ofLp 2)/4) * hr + (-(r.ofLp 0)*(r.ofLp 2)/4 - (r.ofLp 2)/4) * hs + ((r.ofLp 0)*(s.ofLp 2)/4 + (r.ofLp 2)*(s.ofLp 0)/4 + (s.ofLp 2)/4) * hrs

theorem core_ey (hr : (r.ofLp 0) ^ 2 + (r.ofLp 1) ^ 2 + (r.ofLp 2) ^ 2 = 1)
    (hs : (s.ofLp 0) ^ 2 + (s.ofLp 1) ^ 2 + (s.ofLp 2) ^ 2 = 1)
    (hrs : r.ofLp 0 * s.ofLp 0 + r.ofLp 1 * s.ofLp 1 + r.ofLp 2 * s.ofLp 2 = 0) :
    (1 + cosTr r s) • (s - cosTr r s • ey - cross (sigmaVec r s) ey)
      = ⟪sigmaVec r s, ey⟫ • sigmaVec r s := by
  obtain ⟨g0, g1, g2⟩ := sigmaVec_ofLp r s
  obtain ⟨e0, e1, e2⟩ := ey_ofLp
  ext j; fin_cases j
  · simp only [Fin.zero_eta, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two, g0, g1, g2, e0, e1, e2, inner_eq_coords, cosTr]
    linear_combination (-(s.ofLp 0)*(s.ofLp 1)/4 - (s.ofLp 0)/4) * hr + (-(r.ofLp 0)*(r.ofLp 1)/4 - (r.ofLp 1)/4) * hs + ((r.ofLp 0)*(s.ofLp 1)/4 + (r.ofLp 0)/4 + (r.ofLp 1)*(s.ofLp 0)/4 + (s.ofLp 1)/4 + 1/4) * hrs
  · simp only [Fin.mk_one, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two, g0, g1, g2, e0, e1, e2, inner_eq_coords, cosTr]
    linear_combination (-(s.ofLp 1)^2/4 - (s.ofLp 1)/2 - 1/4) * hr + (-(r.ofLp 1)^2/4) * hs + ((r.ofLp 1)*(s.ofLp 1)/2 + (r.ofLp 1)/2) * hrs
  · simp only [Fin.reduceFinMk, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two, g0, g1, g2, e0, e1, e2, inner_eq_coords, cosTr]
    linear_combination (-(s.ofLp 1)*(s.ofLp 2)/4 - (s.ofLp 2)/4) * hr + (-(r.ofLp 1)*(r.ofLp 2)/4) * hs + ((r.ofLp 1)*(s.ofLp 2)/4 + (r.ofLp 2)*(s.ofLp 1)/4 + (r.ofLp 2)/4) * hrs

theorem core_norm (hr : (r.ofLp 0) ^ 2 + (r.ofLp 1) ^ 2 + (r.ofLp 2) ^ 2 = 1)
    (hs : (s.ofLp 0) ^ 2 + (s.ofLp 1) ^ 2 + (s.ofLp 2) ^ 2 = 1)
    (hrs : r.ofLp 0 * s.ofLp 0 + r.ofLp 1 * s.ofLp 1 + r.ofLp 2 * s.ofLp 2 = 0) :
    ‖sigmaVec r s‖ ^ 2 = 1 - (cosTr r s) ^ 2 := by
  obtain ⟨g0, g1, g2⟩ := sigmaVec_ofLp r s
  rw [norm_sq_coords, g0, g1, g2, cosTr]
  linear_combination ((s.ofLp 0)^2/4 + (s.ofLp 1)^2/4 + (s.ofLp 1)/2 + (s.ofLp 2)^2/4 + 1/4) * hr + ((r.ofLp 0)/2 + 1/2) * hs + (-(r.ofLp 0)*(s.ofLp 0)/4 - (r.ofLp 1)*(s.ofLp 1)/4 - (r.ofLp 1)/2 - (r.ofLp 2)*(s.ofLp 2)/4 - (s.ofLp 0)/2) * hrs

/-- The rotation vector `(arcsin ‖σ‖ / ‖σ‖) σ` (zero at `σ = 0`): the axis-angle vector
of a rotation of angle at most `π/2` whose `σ = ½ Σ eᵢ × cᵢ` is given. -/
noncomputable def psiVec (σ : E3) : E3 := (Real.arcsin ‖σ‖ / ‖σ‖) • σ

/-- Rodrigues with axis `σ/‖σ‖`, sine `‖σ‖` and cosine `c`, when `‖σ‖² = 1 - c²`. -/
theorem rodr_sigma {σ x : E3} {c : ℝ} (hσ : σ ≠ 0) (hn : ‖σ‖ ^ 2 = 1 - c ^ 2)
    (hc : 1 + c ≠ 0) :
    rodr c ‖σ‖ (‖σ‖⁻¹ • σ) x = c • x + cross σ x + (⟪σ, x⟫ / (1 + c)) • σ := by
  have hp : 0 < ‖σ‖ := norm_pos_iff.2 hσ
  unfold rodr
  rw [cross_smul_left, smul_smul, mul_inv_cancel₀ hp.ne', one_smul, real_inner_smul_left,
    smul_smul]
  congr 2
  have h1c : 1 - c ^ 2 = (1 - c) * (1 + c) := by ring
  rw [h1c] at hn
  field_simp
  linear_combination (-⟪σ, x⟫) * hn

theorem core_rotate (hr : (r.ofLp 0) ^ 2 + (r.ofLp 1) ^ 2 + (r.ofLp 2) ^ 2 = 1)
    (hs : (s.ofLp 0) ^ 2 + (s.ofLp 1) ^ 2 + (s.ofLp 2) ^ 2 = 1)
    (hrs : r.ofLp 0 * s.ofLp 0 + r.ofLp 1 * s.ofLp 1 + r.ofLp 2 * s.ofLp 2 = 0)
    (hnear : -1 < cosTr r s) :
    ∃ ω : E3, ‖ω‖ = Real.arccos (cosTr r s) ∧ rotate ω ex = r ∧ rotate ω ey = s := by
  set σ := sigmaVec r s with hσdef
  set c := cosTr r s with hcdef
  have hn := core_norm hr hs hrs
  rw [← hσdef, ← hcdef] at hn
  have hc0 : 1 + c ≠ 0 := by linarith
  have hcle : c ≤ 1 := by nlinarith [sq_nonneg ‖σ‖]
  have hex := core_ex hr hs hrs
  have hey := core_ey hr hs hrs
  rw [← hσdef, ← hcdef] at hex hey
  -- Solve each core identity for the target vector.
  have solve : ∀ {t e : E3}, (1 + c) • (t - c • e - cross σ e) = ⟪σ, e⟫ • σ →
      t = c • e + cross σ e + (⟪σ, e⟫ / (1 + c)) • σ := by
    intro t e h
    apply smul_right_injective E3 hc0
    have hd : (1 + c) * (⟪σ, e⟫ / (1 + c)) = ⟪σ, e⟫ := by field_simp
    have hdd : (1 + c) • (⟪σ, e⟫ / (1 + c)) • σ = ⟪σ, e⟫ • σ := by rw [smul_smul, hd]
    simp only
    rw [smul_add, smul_add, hdd]
    linear_combination (norm := module) h
  by_cases hσ0 : σ = 0
  · have hc1 : c = 1 := by
      rw [hσ0, norm_zero] at hn; nlinarith
    refine ⟨0, by rw [norm_zero, hc1, Real.arccos_one], ?_, ?_⟩
    · rw [rotate_zero, solve hex, hσ0, hc1, cross_zero_left]; simp
    · rw [rotate_zero, solve hey, hσ0, hc1, cross_zero_left]; simp
  · have hp : 0 < ‖σ‖ := norm_pos_iff.2 hσ0
    have hc1 : c < 1 := by
      by_contra h; have h' := not_lt.1 h; nlinarith [hcle]
    set θ := Real.arccos c with hθ
    have hθpos : 0 < θ := Real.arccos_pos.2 hc1
    set ω := θ • (‖σ‖⁻¹ • σ) with hω
    have hωn : ‖ω‖ = θ := by
      rw [hω, norm_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp.ne', mul_one,
        Real.norm_of_nonneg hθpos.le]
    have hcos : Real.cos ‖ω‖ = c := by
      rw [hωn, hθ, Real.cos_arccos (by linarith) hcle]
    have hsin : Real.sin ‖ω‖ = ‖σ‖ := by
      rw [hωn, hθ, Real.sin_arccos, ← hn, Real.sqrt_sq hp.le]
    have hk : ‖ω‖⁻¹ • ω = ‖σ‖⁻¹ • σ := by
      rw [hωn, hω, smul_smul, inv_mul_cancel₀ hθpos.ne', one_smul]
    refine ⟨ω, hωn, ?_, ?_⟩
    · rw [rotate_eq_rodr, hcos, hsin, hk, rodr_sigma hσ0 hn hc0, ← solve hex]
    · rw [rotate_eq_rodr, hcos, hsin, hk, rodr_sigma hσ0 hn hc0, ← solve hey]

theorem core_rotate_psi (hr : (r.ofLp 0) ^ 2 + (r.ofLp 1) ^ 2 + (r.ofLp 2) ^ 2 = 1)
    (hs : (s.ofLp 0) ^ 2 + (s.ofLp 1) ^ 2 + (s.ofLp 2) ^ 2 = 1)
    (hrs : r.ofLp 0 * s.ofLp 0 + r.ofLp 1 * s.ofLp 1 + r.ofLp 2 * s.ofLp 2 = 0)
    (hcpos : 0 ≤ cosTr r s) :
    ‖psiVec (sigmaVec r s)‖ = Real.arccos (cosTr r s) ∧
      rotate (psiVec (sigmaVec r s)) ex = r ∧ rotate (psiVec (sigmaVec r s)) ey = s := by
  have hnear : -1 < cosTr r s := by linarith
  set σ := sigmaVec r s with hσdef
  set c := cosTr r s with hcdef
  have hn := core_norm hr hs hrs
  rw [← hσdef, ← hcdef] at hn
  have hc0 : 1 + c ≠ 0 := by linarith
  have hcle : c ≤ 1 := by nlinarith [sq_nonneg ‖σ‖]
  have hex := core_ex hr hs hrs
  have hey := core_ey hr hs hrs
  rw [← hσdef, ← hcdef] at hex hey
  -- Solve each core identity for the target vector.
  have solve : ∀ {t e : E3}, (1 + c) • (t - c • e - cross σ e) = ⟪σ, e⟫ • σ →
      t = c • e + cross σ e + (⟪σ, e⟫ / (1 + c)) • σ := by
    intro t e h
    apply smul_right_injective E3 hc0
    have hd : (1 + c) * (⟪σ, e⟫ / (1 + c)) = ⟪σ, e⟫ := by field_simp
    have hdd : (1 + c) • (⟪σ, e⟫ / (1 + c)) • σ = ⟪σ, e⟫ • σ := by rw [smul_smul, hd]
    simp only
    rw [smul_add, smul_add, hdd]
    linear_combination (norm := module) h
  by_cases hσ0 : σ = 0
  · have hc1 : c = 1 := by
      rw [hσ0, norm_zero] at hn; nlinarith
    have hψ0 : psiVec σ = 0 := by rw [hσ0]; simp [psiVec]
    rw [hψ0]
    refine ⟨by rw [norm_zero, hc1, Real.arccos_one], ?_, ?_⟩
    · rw [rotate_zero, solve hex, hσ0, hc1, cross_zero_left]; simp
    · rw [rotate_zero, solve hey, hσ0, hc1, cross_zero_left]; simp
  · have hp : 0 < ‖σ‖ := norm_pos_iff.2 hσ0
    have hc1 : c < 1 := by
      by_contra h; have h' := not_lt.1 h; nlinarith [hcle]
    set θ := Real.arccos c with hθ
    have hθpos : 0 < θ := Real.arccos_pos.2 hc1
    set ω := θ • (‖σ‖⁻¹ • σ) with hω
    have hωn : ‖ω‖ = θ := by
      rw [hω, norm_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp.ne', mul_one,
        Real.norm_of_nonneg hθpos.le]
    have hcos : Real.cos ‖ω‖ = c := by
      rw [hωn, hθ, Real.cos_arccos (by linarith) hcle]
    have hsin : Real.sin ‖ω‖ = ‖σ‖ := by
      rw [hωn, hθ, Real.sin_arccos, ← hn, Real.sqrt_sq hp.le]
    have hk : ‖ω‖⁻¹ • ω = ‖σ‖⁻¹ • σ := by
      rw [hωn, hω, smul_smul, inv_mul_cancel₀ hθpos.ne', one_smul]
    have hψ : psiVec σ = ω := by
      have hθs : θ = Real.arcsin ‖σ‖ := by
        rw [hθ, Real.arccos_eq_arcsin hcpos, ← hn, Real.sqrt_sq hp.le]
      rw [psiVec, hω, smul_smul, ← hθs, div_eq_mul_inv]
    rw [hψ]
    refine ⟨hωn, ?_, ?_⟩
    · rw [rotate_eq_rodr, hcos, hsin, hk, rodr_sigma hσ0 hn hc0, ← solve hex]
    · rw [rotate_eq_rodr, hcos, hsin, hk, rodr_sigma hσ0 hn hc0, ← solve hey]

end Core

/-! ## Frame coordinates -/

section FrameCoords

variable {a₁ a₂ : E3}

/-- Coordinates of `v` in the frame `(a₁, a₂, a₁ × a₂)`. -/
noncomputable def toF (a₁ a₂ v : E3) : E3 := !₂[⟪a₁, v⟫, ⟪a₂, v⟫, ⟪cross a₁ a₂, v⟫]

/-- The vector with coordinates `x` in the frame `(a₁, a₂, a₁ × a₂)`. -/
noncomputable def ofF (a₁ a₂ x : E3) : E3 :=
  x.ofLp 0 • a₁ + x.ofLp 1 • a₂ + x.ofLp 2 • cross a₁ a₂

theorem toF_ofLp (a₁ a₂ v : E3) :
    (toF a₁ a₂ v).ofLp 0 = ⟪a₁, v⟫ ∧ (toF a₁ a₂ v).ofLp 1 = ⟪a₂, v⟫ ∧
      (toF a₁ a₂ v).ofLp 2 = ⟪cross a₁ a₂, v⟫ := by
  simp [toF]

theorem ofF_add (a₁ a₂ x y : E3) : ofF a₁ a₂ (x + y) = ofF a₁ a₂ x + ofF a₁ a₂ y := by
  simp only [ofF, WithLp.ofLp_add, Pi.add_apply, add_smul]; abel

theorem ofF_smul (a₁ a₂ x : E3) (k : ℝ) : ofF a₁ a₂ (k • x) = k • ofF a₁ a₂ x := by
  simp only [ofF, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, smul_add, smul_smul]

theorem ofF_sub (a₁ a₂ x y : E3) : ofF a₁ a₂ (x - y) = ofF a₁ a₂ x - ofF a₁ a₂ y := by
  simp only [ofF, WithLp.ofLp_sub, Pi.sub_apply, sub_smul]; abel

theorem ofF_ex (a₁ a₂ : E3) : ofF a₁ a₂ ex = a₁ := by
  obtain ⟨e0, e1, e2⟩ := ex_ofLp; simp [ofF, e0, e1, e2]

theorem ofF_ey (a₁ a₂ : E3) : ofF a₁ a₂ ey = a₂ := by
  obtain ⟨e0, e1, e2⟩ := ey_ofLp; simp [ofF, e0, e1, e2]

variable (ha₁ : ‖a₁‖ = 1) (ha₂ : ‖a₂‖ = 1) (ha : ⟪a₁, a₂⟫ = 0)
include ha₁ ha₂ ha

theorem inner_ofF (x y : E3) : ⟪ofF a₁ a₂ x, ofF a₁ a₂ y⟫ = ⟪x, y⟫ := by
  have e11 : ⟪a₁, a₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, ha₁]; norm_num
  have e22 : ⟪a₂, a₂⟫ = 1 := by rw [real_inner_self_eq_norm_sq, ha₂]; norm_num
  have e33 : ⟪cross a₁ a₂, cross a₁ a₂⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_cross_of_orthonormal ha₁ ha₂ ha]; norm_num
  have e21 : ⟪a₂, a₁⟫ = 0 := by rw [real_inner_comm]; exact ha
  have e13 := inner_cross_left a₁ a₂
  have e23 := inner_cross_right a₁ a₂
  have e31 : ⟪cross a₁ a₂, a₁⟫ = 0 := by rw [real_inner_comm]; exact e13
  have e32 : ⟪cross a₁ a₂, a₂⟫ = 0 := by rw [real_inner_comm]; exact e23
  simp only [ofF, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    e11, e22, e33, ha, e21, e13, e23, e31, e32]
  rw [inner_eq_coords x y]; ring

theorem norm_ofF (x : E3) : ‖ofF a₁ a₂ x‖ = ‖x‖ := by
  have h := inner_ofF ha₁ ha₂ ha x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem ofF_toF (v : E3) : ofF a₁ a₂ (toF a₁ a₂ v) = v := by
  have hA1 := coords_unit ha₁
  have hA2 := coords_unit ha₂
  have hA12 := coords_orth ha
  obtain ⟨t0, t1, t2⟩ := toF_ofLp a₁ a₂ v
  ext j; fin_cases j
  · simp only [Fin.zero_eta, ofF, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, t0, t1, t2, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two, inner_eq_coords]
    linear_combination (-(a₂.ofLp 0)*(a₂.ofLp 1)*(v.ofLp 1) - (a₂.ofLp 0)*(a₂.ofLp 2)*(v.ofLp 2) + (a₂.ofLp 1)^2*(v.ofLp 0) + (a₂.ofLp 2)^2*(v.ofLp 0)) * hA1 + (-(a₁.ofLp 0)^2*(v.ofLp 0) - (a₁.ofLp 0)*(a₁.ofLp 1)*(v.ofLp 1) - (a₁.ofLp 0)*(a₁.ofLp 2)*(v.ofLp 2) + (v.ofLp 0)) * hA2 + ((a₁.ofLp 0)*(a₂.ofLp 0)*(v.ofLp 0) + (a₁.ofLp 0)*(a₂.ofLp 1)*(v.ofLp 1) + (a₁.ofLp 0)*(a₂.ofLp 2)*(v.ofLp 2) + (a₁.ofLp 1)*(a₂.ofLp 0)*(v.ofLp 1) - (a₁.ofLp 1)*(a₂.ofLp 1)*(v.ofLp 0) + (a₁.ofLp 2)*(a₂.ofLp 0)*(v.ofLp 2) - (a₁.ofLp 2)*(a₂.ofLp 2)*(v.ofLp 0)) * hA12
  · simp only [Fin.mk_one, ofF, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, t0, t1, t2, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two, inner_eq_coords]
    linear_combination ((a₂.ofLp 0)^2*(v.ofLp 1) - (a₂.ofLp 0)*(a₂.ofLp 1)*(v.ofLp 0) - (a₂.ofLp 1)*(a₂.ofLp 2)*(v.ofLp 2) + (a₂.ofLp 2)^2*(v.ofLp 1)) * hA1 + (-(a₁.ofLp 0)*(a₁.ofLp 1)*(v.ofLp 0) - (a₁.ofLp 1)^2*(v.ofLp 1) - (a₁.ofLp 1)*(a₁.ofLp 2)*(v.ofLp 2) + (v.ofLp 1)) * hA2 + (-(a₁.ofLp 0)*(a₂.ofLp 0)*(v.ofLp 1) + (a₁.ofLp 0)*(a₂.ofLp 1)*(v.ofLp 0) + (a₁.ofLp 1)*(a₂.ofLp 0)*(v.ofLp 0) + (a₁.ofLp 1)*(a₂.ofLp 1)*(v.ofLp 1) + (a₁.ofLp 1)*(a₂.ofLp 2)*(v.ofLp 2) + (a₁.ofLp 2)*(a₂.ofLp 1)*(v.ofLp 2) - (a₁.ofLp 2)*(a₂.ofLp 2)*(v.ofLp 1)) * hA12
  · simp only [Fin.reduceFinMk, ofF, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, t0, t1, t2, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two, inner_eq_coords]
    linear_combination (-(a₂.ofLp 0)*(a₂.ofLp 2)*(v.ofLp 0) - (a₂.ofLp 1)*(a₂.ofLp 2)*(v.ofLp 1) - (a₂.ofLp 2)^2*(v.ofLp 2) + (v.ofLp 2)) * hA1 + ((a₁.ofLp 0)^2*(v.ofLp 2) - (a₁.ofLp 0)*(a₁.ofLp 2)*(v.ofLp 0) + (a₁.ofLp 1)^2*(v.ofLp 2) - (a₁.ofLp 1)*(a₁.ofLp 2)*(v.ofLp 1)) * hA2 + (-(a₁.ofLp 0)*(a₂.ofLp 0)*(v.ofLp 2) + (a₁.ofLp 0)*(a₂.ofLp 2)*(v.ofLp 0) - (a₁.ofLp 1)*(a₂.ofLp 1)*(v.ofLp 2) + (a₁.ofLp 1)*(a₂.ofLp 2)*(v.ofLp 1) + (a₁.ofLp 2)*(a₂.ofLp 0)*(v.ofLp 0) + (a₁.ofLp 2)*(a₂.ofLp 1)*(v.ofLp 1) + (a₁.ofLp 2)*(a₂.ofLp 2)*(v.ofLp 2)) * hA12

theorem cross_ofF (x y : E3) :
    ofF a₁ a₂ (cross x y) = cross (ofF a₁ a₂ x) (ofF a₁ a₂ y) := by
  have hA1 := coords_unit ha₁
  have hA2 := coords_unit ha₂
  have hA12 := coords_orth ha
  ext j; fin_cases j
  · simp only [Fin.zero_eta, ofF, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two]
    linear_combination ((a₂.ofLp 0)*(x.ofLp 0)*(y.ofLp 2) - (a₂.ofLp 0)*(x.ofLp 2)*(y.ofLp 0)) * hA1 + (-(a₁.ofLp 0)*(x.ofLp 1)*(y.ofLp 2) + (a₁.ofLp 0)*(x.ofLp 2)*(y.ofLp 1)) * hA2 + (-(a₁.ofLp 0)*(x.ofLp 0)*(y.ofLp 2) + (a₁.ofLp 0)*(x.ofLp 2)*(y.ofLp 0) + (a₂.ofLp 0)*(x.ofLp 1)*(y.ofLp 2) - (a₂.ofLp 0)*(x.ofLp 2)*(y.ofLp 1)) * hA12
  · simp only [Fin.mk_one, ofF, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two]
    linear_combination ((a₂.ofLp 1)*(x.ofLp 0)*(y.ofLp 2) - (a₂.ofLp 1)*(x.ofLp 2)*(y.ofLp 0)) * hA1 + (-(a₁.ofLp 1)*(x.ofLp 1)*(y.ofLp 2) + (a₁.ofLp 1)*(x.ofLp 2)*(y.ofLp 1)) * hA2 + (-(a₁.ofLp 1)*(x.ofLp 0)*(y.ofLp 2) + (a₁.ofLp 1)*(x.ofLp 2)*(y.ofLp 0) + (a₂.ofLp 1)*(x.ofLp 1)*(y.ofLp 2) - (a₂.ofLp 1)*(x.ofLp 2)*(y.ofLp 1)) * hA12
  · simp only [Fin.reduceFinMk, ofF, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two]
    linear_combination ((a₂.ofLp 2)*(x.ofLp 0)*(y.ofLp 2) - (a₂.ofLp 2)*(x.ofLp 2)*(y.ofLp 0)) * hA1 + (-(a₁.ofLp 2)*(x.ofLp 1)*(y.ofLp 2) + (a₁.ofLp 2)*(x.ofLp 2)*(y.ofLp 1)) * hA2 + (-(a₁.ofLp 2)*(x.ofLp 0)*(y.ofLp 2) + (a₁.ofLp 2)*(x.ofLp 2)*(y.ofLp 0) + (a₂.ofLp 2)*(x.ofLp 1)*(y.ofLp 2) - (a₂.ofLp 2)*(x.ofLp 2)*(y.ofLp 1)) * hA12

theorem rotate_ofF (ω x : E3) : rotate (ofF a₁ a₂ ω) (ofF a₁ a₂ x) = ofF a₁ a₂ (rotate ω x) := by
  rw [rotate_eq_rodr, rotate_eq_rodr, norm_ofF ha₁ ha₂ ha, rodr, rodr,
    ← ofF_smul a₁ a₂ ω ‖ω‖⁻¹, ← cross_ofF ha₁ ha₂ ha, inner_ofF ha₁ ha₂ ha]
  simp only [ofF_add, ofF_smul]

theorem toF_unit {c : E3} (hc : ‖c‖ = 1) : ‖toF a₁ a₂ c‖ = 1 := by
  rw [← norm_ofF ha₁ ha₂ ha, ofF_toF ha₁ ha₂ ha, hc]

theorem toF_orth {c d : E3} (hcd : ⟪c, d⟫ = 0) : ⟪toF a₁ a₂ c, toF a₁ a₂ d⟫ = 0 := by
  rw [← inner_ofF ha₁ ha₂ ha, ofF_toF ha₁ ha₂ ha, ofF_toF ha₁ ha₂ ha, hcd]

end FrameCoords

theorem cosTr_toF (a₁ a₂ c₁ c₂ : E3) :
    cosTr (toF a₁ a₂ c₁) (toF a₁ a₂ c₂) = (frameTrace a₁ a₂ c₁ c₂ - 1) / 2 := by
  obtain ⟨p0, p1, p2⟩ := toF_ofLp a₁ a₂ c₁
  obtain ⟨q0, q1, q2⟩ := toF_ofLp a₁ a₂ c₂
  rw [cosTr, p0, p1, q0, q1, frameTrace, inner_cross_cross]
  ring

/-- **Axis-angle.** -/
theorem exists_rotate_frame {a₁ a₂ c₁ c₂ : E3} (ha₁ : ‖a₁‖ = 1) (ha₂ : ‖a₂‖ = 1)
    (ha : ⟪a₁, a₂⟫ = 0) (hc₁ : ‖c₁‖ = 1) (hc₂ : ‖c₂‖ = 1) (hc : ⟪c₁, c₂⟫ = 0)
    (hnear : -1 < frameTrace a₁ a₂ c₁ c₂) :
    ∃ ω : E3, ‖ω‖ = rotAngle a₁ a₂ c₁ c₂ ∧ rotate ω a₁ = c₁ ∧ rotate ω a₂ = c₂ ∧
      rotate ω (cross a₁ a₂) = cross c₁ c₂ := by
  set r := toF a₁ a₂ c₁
  set s := toF a₁ a₂ c₂
  have hr := coords_unit (toF_unit ha₁ ha₂ ha hc₁)
  have hs := coords_unit (toF_unit ha₁ ha₂ ha hc₂)
  have hrs := coords_orth (toF_orth ha₁ ha₂ ha hc)
  have hct := cosTr_toF a₁ a₂ c₁ c₂
  obtain ⟨ω₀, hn, h1, h2⟩ := core_rotate hr hs hrs (by rw [hct]; linarith)
  have hr1 : rotate (ofF a₁ a₂ ω₀) a₁ = c₁ := by
    have := rotate_ofF ha₁ ha₂ ha ω₀ ex
    rwa [ofF_ex, h1, ofF_toF ha₁ ha₂ ha] at this
  have hr2 : rotate (ofF a₁ a₂ ω₀) a₂ = c₂ := by
    have := rotate_ofF ha₁ ha₂ ha ω₀ ey
    rwa [ofF_ey, h2, ofF_toF ha₁ ha₂ ha] at this
  refine ⟨ofF a₁ a₂ ω₀, ?_, hr1, hr2, by rw [rotate_cross, hr1, hr2]⟩
  rw [norm_ofF ha₁ ha₂ ha, hn, hct, rotAngle]

/-- Nearby frames have trace above `-1`. -/
theorem frameTrace_gt_of_angle_le {a₁ a₂ c₁ c₂ : E3} (ha₁ : ‖a₁‖ = 1) (ha₂ : ‖a₂‖ = 1)
    (ha : ⟪a₁, a₂⟫ = 0) (hc₁ : ‖c₁‖ = 1) (hc₂ : ‖c₂‖ = 1) (hc : ⟪c₁, c₂⟫ = 0)
    {ε : ℝ} (hε : ε ≤ π / 2) (h₁ : angle a₁ c₁ ≤ ε) (h₂ : angle a₂ c₂ ≤ ε)
    (h₃ : angle (cross a₁ a₂) (cross c₁ c₂) ≤ ε) :
    3 * Real.cos ε ≤ frameTrace a₁ a₂ c₁ c₂ := by
  have key : ∀ {x y : E3}, ‖x‖ = 1 → ‖y‖ = 1 → angle x y ≤ ε → Real.cos ε ≤ ⟪x, y⟫ := by
    intro x y hx hy hxy
    have : ⟪x, y⟫ = Real.cos (angle x y) := by rw [cos_angle, hx, hy, mul_one, div_one]
    rw [this]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (angle_nonneg x y)
      (by linarith [Real.pi_pos]) hxy
  have h3 := key (norm_cross_of_orthonormal ha₁ ha₂ ha) (norm_cross_of_orthonormal hc₁ hc₂ hc) h₃
  unfold frameTrace
  linarith [key ha₁ hc₁ h₁, key ha₂ hc₂ h₂]

/-- **Angle bound.** If every frame vector moves by at most `ε ≤ π/2`, the rotation
angle is at most `2ε`. -/
theorem rotAngle_le {a₁ a₂ c₁ c₂ : E3} (ha₁ : ‖a₁‖ = 1) (ha₂ : ‖a₂‖ = 1)
    (ha : ⟪a₁, a₂⟫ = 0) (hc₁ : ‖c₁‖ = 1) (hc₂ : ‖c₂‖ = 1) (hc : ⟪c₁, c₂⟫ = 0)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ π / 2) (h₁ : angle a₁ c₁ ≤ ε) (h₂ : angle a₂ c₂ ≤ ε)
    (h₃ : angle (cross a₁ a₂) (cross c₁ c₂) ≤ ε) :
    rotAngle a₁ a₂ c₁ c₂ ≤ 2 * ε := by
  have ht := frameTrace_gt_of_angle_le ha₁ ha₂ ha hc₁ hc₂ hc hε h₁ h₂ h₃
  have hcos : Real.cos (2 * ε) ≤ (frameTrace a₁ a₂ c₁ c₂ - 1) / 2 := by
    rw [Real.cos_two_mul]
    have hx1 := Real.cos_le_one ε
    have hx0 : 0 ≤ Real.cos ε :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hε⟩
    nlinarith
  unfold rotAngle
  calc Real.arccos ((frameTrace a₁ a₂ c₁ c₂ - 1) / 2) ≤ Real.arccos (Real.cos (2 * ε)) :=
        Real.arccos_le_arccos hcos
    _ = 2 * ε := Real.arccos_cos (by linarith) (by linarith)

end VisionTracking
