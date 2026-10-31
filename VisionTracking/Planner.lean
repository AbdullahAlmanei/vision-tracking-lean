import VisionTracking.Model

/-!
# The FIR formation planner

The drone flies a causal linear filter of the target's past positions:
`x_k = Σᵢ hᵢ p_{k-i} + off`, with `hᵢ` supported on `[2, M]` (two steps of lag, so
the motor commands at step `k` depend on positions up to `k`). If the filter
reproduces quadratics exactly (`Σ hᵢ = 1`, `Σ i hᵢ = 0`, `Σ i² hᵢ = 0`), then
against any jerk-bounded target:

* position error `≤ H₃ δ³ j`, velocity error `≤ H₂ δ² j`, acceleration error `≤ H₁ δ j`;
* acceleration changes per step `≤ H₀ δ j`, and its second differences
  `≤ TV(h) δ j`. The total variation of the filter is what keeps the torque
  finite.

The target's history before step 0 is extended at its known initial
acceleration `a₀`, which keeps the jerk bound valid across the start.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {δ : ℝ}

namespace TargetTraj

variable (T : TargetTraj P δ) (a₀ : E3)

/-- Positions on all of `ℤ`: the trajectory for `n ≥ 0`, a constant-acceleration
history for `n < 0`. -/
noncomputable def ext (n : ℤ) : E3 :=
  if 0 ≤ n then T.p n.toNat
  else T.p 0 + ((n : ℝ) * δ) • T.v 0 + (δ ^ 2 * ((n : ℝ) * ((n : ℝ) - 1) / 2)) • a₀

noncomputable def velExt (n : ℤ) : E3 :=
  if 0 ≤ n then T.v n.toNat else T.v 0 + ((n : ℝ) * δ) • a₀

noncomputable def accExt (n : ℤ) : E3 :=
  if 0 ≤ n then δ⁻¹ • (T.v (n.toNat + 1) - T.v n.toNat) else a₀

theorem ext_succ (n : ℤ) : T.ext a₀ (n + 1) = T.ext a₀ n + δ • T.velExt a₀ n := by
  rcases le_or_gt 0 n with h | h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have h1 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
    simp only [ext, velExt, if_pos h, if_pos h1]
    rw [show ((m : ℤ) + 1).toNat = m + 1 by omega, show (m : ℤ).toNat = m by omega, T.steps m]
  · rcases (by omega : n = -1 ∨ n ≤ -2) with h1 | h1
    · subst h1
      simp only [ext, velExt]
      norm_num
      module
    · have h2 : ¬ (0 ≤ n + 1) := by omega
      simp only [ext, velExt, if_neg (not_le.2 h), if_neg h2]
      push_cast
      module

theorem velExt_succ (hδ : δ ≠ 0) (n : ℤ) :
    T.velExt a₀ (n + 1) = T.velExt a₀ n + δ • T.accExt a₀ n := by
  rcases le_or_gt 0 n with h | h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have h1 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
    simp only [velExt, accExt, if_pos h, if_pos h1]
    rw [show ((m : ℤ) + 1).toNat = m + 1 by omega, show (m : ℤ).toNat = m by omega,
      smul_smul, mul_inv_cancel₀ hδ, one_smul, add_sub_cancel]
  · rcases (by omega : n = -1 ∨ n ≤ -2) with h1 | h1
    · subst h1
      simp only [velExt, accExt]
      norm_num
    · have h2 : ¬ (0 ≤ n + 1) := by omega
      simp only [velExt, accExt, if_neg (not_le.2 h), if_neg h2]
      push_cast
      module

theorem accExt_succ_le (hδ : 0 < δ) (hS : T.v 1 = T.v 0 + δ • a₀) (n : ℤ) :
    ‖T.accExt a₀ (n + 1) - T.accExt a₀ n‖ ≤ δ * P.jerk := by
  have hJ : 0 ≤ δ * P.jerk := mul_nonneg hδ.le P.jerk_nonneg
  rcases le_or_gt 0 n with h | h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have h1 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
    simp only [accExt, if_pos h, if_pos h1]
    rw [show ((m : ℤ) + 1).toNat = m + 1 by omega, show (m : ℤ).toNat = m by omega, ← smul_sub,
      norm_smul, norm_inv, Real.norm_of_nonneg hδ.le]
    have := T.jerk_le m
    rw [inv_mul_le_iff₀ hδ]
    calc ‖T.v (m + 1 + 1) - T.v (m + 1) - (T.v (m + 1) - T.v m)‖ ≤ δ ^ 2 * P.jerk := this
      _ = δ * (δ * P.jerk) := by ring
  · rcases (by omega : n = -1 ∨ n ≤ -2) with h1 | h1
    · subst h1
      simp only [accExt]
      norm_num
      rw [hS, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hδ.ne', one_smul, sub_self,
        norm_zero]
      exact hJ
    · have h2 : ¬ (0 ≤ n + 1) := by omega
      simp only [accExt, if_neg (not_le.2 h), if_neg h2, sub_self, norm_zero]
      exact hJ

theorem ext_natCast (k : ℕ) : T.ext a₀ k = T.p k := by
  simp [ext]

theorem velExt_natCast (k : ℕ) : T.velExt a₀ k = T.v k := by
  simp [velExt]

/-- Accelerations `i` steps apart differ by at most `i δ j`. -/
theorem acc_diff_le (hδ : 0 < δ) (hS : T.v 1 = T.v 0 + δ • a₀) (n : ℤ) (i : ℕ) :
    ‖T.accExt a₀ n - T.accExt a₀ (n - i)‖ ≤ i * δ * P.jerk := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := T.accExt_succ_le a₀ hδ hS (n - (i + 1))
    rw [show n - (i + 1 : ℤ) + 1 = n - i by ring] at h1
    have : T.accExt a₀ n - T.accExt a₀ (n - ((i + 1 : ℕ) : ℤ))
        = (T.accExt a₀ n - T.accExt a₀ (n - i)) + (T.accExt a₀ (n - i)
          - T.accExt a₀ (n - (i + 1))) := by push_cast; abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    push_cast
    linarith

/-- Velocity Taylor remainder. -/
theorem vel_rem_le (hδ : 0 < δ) (hS : T.v 1 = T.v 0 + δ • a₀) (n : ℤ) (i : ℕ) :
    ‖T.velExt a₀ n - T.velExt a₀ (n - i) - ((i : ℝ) * δ) • T.accExt a₀ n‖
      ≤ δ ^ 2 * P.jerk * ((i : ℝ) * (i + 1) / 2) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hv := T.velExt_succ a₀ hδ.ne' (n - (i + 1))
    rw [show n - (i + 1 : ℤ) + 1 = n - i by ring] at hv
    have hsplit : T.velExt a₀ n - T.velExt a₀ (n - ((i + 1 : ℕ) : ℤ))
        - (((i + 1 : ℕ) : ℝ) * δ) • T.accExt a₀ n
        = (T.velExt a₀ n - T.velExt a₀ (n - i) - ((i : ℝ) * δ) • T.accExt a₀ n)
          + δ • (T.accExt a₀ (n - (i + 1)) - T.accExt a₀ n) := by
      push_cast; rw [hv]; module
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have ha := T.acc_diff_le a₀ hδ hS n (i + 1)
    rw [norm_sub_rev] at ha
    rw [norm_smul, Real.norm_of_nonneg hδ.le]
    push_cast at ha ⊢
    have := mul_le_mul_of_nonneg_left ha hδ.le
    nlinarith

/-- Position Taylor remainder. -/
theorem pos_rem_le (hδ : 0 < δ) (hS : T.v 1 = T.v 0 + δ • a₀) (n : ℤ) (i : ℕ) :
    ‖T.ext a₀ (n - i) - T.ext a₀ n + ((i : ℝ) * δ) • T.velExt a₀ n
      - (δ ^ 2 * ((i : ℝ) * (i + 1) / 2)) • T.accExt a₀ n‖
      ≤ δ ^ 3 * P.jerk * ((i : ℝ) * (i + 1) * (i + 2) / 6) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have he := T.ext_succ a₀ (n - (i + 1))
    rw [show n - (i + 1 : ℤ) + 1 = n - i by ring] at he
    have hsplit : T.ext a₀ (n - ((i + 1 : ℕ) : ℤ)) - T.ext a₀ n
        + (((i + 1 : ℕ) : ℝ) * δ) • T.velExt a₀ n
        - (δ ^ 2 * (((i + 1 : ℕ) : ℝ) * ((i + 1 : ℕ) + 1) / 2)) • T.accExt a₀ n
        = (T.ext a₀ (n - i) - T.ext a₀ n + ((i : ℝ) * δ) • T.velExt a₀ n
          - (δ ^ 2 * ((i : ℝ) * (i + 1) / 2)) • T.accExt a₀ n)
          + δ • (T.velExt a₀ n - T.velExt a₀ (n - ((i + 1 : ℕ) : ℤ))
            - (((i + 1 : ℕ) : ℝ) * δ) • T.accExt a₀ n) := by
      push_cast; rw [he]; module
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have hv := T.vel_rem_le a₀ hδ hS n (i + 1)
    rw [norm_smul, Real.norm_of_nonneg hδ.le]
    have := mul_le_mul_of_nonneg_left hv hδ.le
    push_cast at this ⊢
    nlinarith

end TargetTraj

/-- A causal FIR filter with two steps of lag that reproduces quadratics. -/
structure FIR where
  h : ℕ → ℝ
  M : ℕ
  h_zero : h 0 = 0
  h_one : h 1 = 0
  supp : ∀ i, M < i → h i = 0
  sum_h : ∑ i ∈ Finset.range (M + 1), h i = 1
  mom1 : ∑ i ∈ Finset.range (M + 1), (i : ℝ) * h i = 0
  mom2 : ∑ i ∈ Finset.range (M + 1), (i : ℝ) ^ 2 * h i = 0

/-- Abel summation. -/
theorem abel_sum (h : ℕ → ℝ) (G : ℕ → E3) (n : ℕ) :
    ∑ i ∈ Finset.range n, h i • (G i - G (i + 1))
      = h 0 • G 0 - h n • G n + ∑ i ∈ Finset.range n, (h (i + 1) - h i) • G (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    module

namespace FIR

variable (F : FIR)

noncomputable def H0 : ℝ := ∑ i ∈ Finset.range (F.M + 1), |F.h i|
noncomputable def H1 : ℝ := ∑ i ∈ Finset.range (F.M + 1), |F.h i| * i
noncomputable def H2 : ℝ := ∑ i ∈ Finset.range (F.M + 1), |F.h i| * ((i : ℝ) * (i + 1) / 2)
noncomputable def H3 : ℝ :=
  ∑ i ∈ Finset.range (F.M + 1), |F.h i| * ((i : ℝ) * (i + 1) * (i + 2) / 6)
/-- Total variation of the filter (with zero padding on both sides). -/
noncomputable def TV : ℝ := |F.h 0| + ∑ i ∈ Finset.range (F.M + 1), |F.h (i + 1) - F.h i|

/-- Planned position. -/
noncomputable def planPos (T : TargetTraj P δ) (a₀ off : E3) (k : ℕ) : E3 :=
  ∑ i ∈ Finset.range (F.M + 1), F.h i • T.ext a₀ ((k : ℤ) - i) + off

noncomputable def planVel (T : TargetTraj P δ) (a₀ : E3) (k : ℕ) : E3 :=
  ∑ i ∈ Finset.range (F.M + 1), F.h i • T.velExt a₀ ((k : ℤ) - i)

noncomputable def planAcc (T : TargetTraj P δ) (a₀ : E3) (k : ℕ) : E3 :=
  ∑ i ∈ Finset.range (F.M + 1), F.h i • T.accExt a₀ ((k : ℤ) - i)

variable (T : TargetTraj P δ) (a₀ off : E3)

theorem planPos_succ (k : ℕ) :
    F.planPos T a₀ off (k + 1) = F.planPos T a₀ off k + δ • F.planVel T a₀ k := by
  have : ∀ i : ℕ, F.h i • T.ext a₀ (((k + 1 : ℕ) : ℤ) - i)
      = F.h i • T.ext a₀ ((k : ℤ) - i) + δ • (F.h i • T.velExt a₀ ((k : ℤ) - i)) := by
    intro i
    rw [show ((k + 1 : ℕ) : ℤ) - i = ((k : ℤ) - i) + 1 by push_cast; ring, T.ext_succ]
    module
  simp only [planPos, planVel, this, Finset.sum_add_distrib, ← Finset.smul_sum]
  abel

theorem planVel_succ (hδ : δ ≠ 0) (k : ℕ) :
    F.planVel T a₀ (k + 1) = F.planVel T a₀ k + δ • F.planAcc T a₀ k := by
  have : ∀ i : ℕ, F.h i • T.velExt a₀ (((k + 1 : ℕ) : ℤ) - i)
      = F.h i • T.velExt a₀ ((k : ℤ) - i) + δ • (F.h i • T.accExt a₀ ((k : ℤ) - i)) := by
    intro i
    rw [show ((k + 1 : ℕ) : ℤ) - i = ((k : ℤ) - i) + 1 by push_cast; ring,
      T.velExt_succ a₀ hδ]
    module
  simp only [planVel, planAcc, this, Finset.sum_add_distrib, ← Finset.smul_sum]

variable (hδ : 0 < δ) (hS : T.StartsAt (T.p 0) (T.v 0) a₀)
include hδ hS

theorem planPos_err (k : ℕ) :
    ‖F.planPos T a₀ off k - (T.p k + off)‖ ≤ F.H3 * δ ^ 3 * P.jerk := by
  have hS' := hS.2.2
  set E : ℕ → E3 := fun i => T.ext a₀ ((k : ℤ) - i) - T.ext a₀ k + ((i : ℝ) * δ) • T.velExt a₀ k
    - (δ ^ 2 * ((i : ℝ) * (i + 1) / 2)) • T.accExt a₀ k with hE
  have term : ∀ i : ℕ, F.h i • E i = F.h i • T.ext a₀ ((k : ℤ) - i) - F.h i • T.ext a₀ k
      + (δ * ((i : ℝ) * F.h i)) • T.velExt a₀ k
      - (δ ^ 2 / 2 * ((i : ℝ) ^ 2 * F.h i + (i : ℝ) * F.h i)) • T.accExt a₀ k := by
    intro i; simp only [hE]; module
  have key : F.planPos T a₀ off k - (T.p k + off) = ∑ i ∈ Finset.range (F.M + 1), F.h i • E i := by
    rw [Finset.sum_congr rfl (fun i _ => term i)]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_smul,
      ← Finset.mul_sum, F.sum_h, F.mom1, F.mom2, one_smul, mul_zero, add_zero, zero_smul,
      sub_zero, T.ext_natCast, planPos]
    abel
  rw [key]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range (F.M + 1), ‖F.h i • E i‖
      ≤ ∑ i ∈ Finset.range (F.M + 1),
          |F.h i| * (δ ^ 3 * P.jerk * ((i : ℝ) * (i + 1) * (i + 2) / 6)) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (T.pos_rem_le a₀ hδ hS' k i) (abs_nonneg _)
    _ = F.H3 * δ ^ 3 * P.jerk := by
        rw [H3, Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i _; ring

theorem planVel_err (k : ℕ) : ‖F.planVel T a₀ k - T.v k‖ ≤ F.H2 * δ ^ 2 * P.jerk := by
  have hS' := hS.2.2
  set G : ℕ → E3 := fun i => T.velExt a₀ k - T.velExt a₀ ((k : ℤ) - i)
    - ((i : ℝ) * δ) • T.accExt a₀ k with hG
  have key : F.planVel T a₀ k - T.v k = -∑ i ∈ Finset.range (F.M + 1), F.h i • G i := by
    have h1 : ∑ i ∈ Finset.range (F.M + 1), F.h i • G i
        = (∑ i ∈ Finset.range (F.M + 1), F.h i) • T.velExt a₀ k
          - ∑ i ∈ Finset.range (F.M + 1), F.h i • T.velExt a₀ ((k : ℤ) - i)
          - (δ * ∑ i ∈ Finset.range (F.M + 1), (i : ℝ) * F.h i) • T.accExt a₀ k := by
      simp only [hG, smul_sub, smul_smul, Finset.sum_sub_distrib, Finset.sum_smul,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl; intro i _; congr 1; ring
    rw [h1, F.sum_h, F.mom1, one_smul, mul_zero, zero_smul, sub_zero, T.velExt_natCast, planVel]
    abel
  rw [key, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range (F.M + 1), ‖F.h i • G i‖
      ≤ ∑ i ∈ Finset.range (F.M + 1), |F.h i| * (δ ^ 2 * P.jerk * ((i : ℝ) * (i + 1) / 2)) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (T.vel_rem_le a₀ hδ hS' k i) (abs_nonneg _)
    _ = F.H2 * δ ^ 2 * P.jerk := by
        rw [H2, Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i _; ring

theorem planAcc_err (k : ℕ) :
    ‖F.planAcc T a₀ k - T.accExt a₀ k‖ ≤ F.H1 * δ * P.jerk := by
  have hS' := hS.2.2
  have key : F.planAcc T a₀ k - T.accExt a₀ k
      = ∑ i ∈ Finset.range (F.M + 1), F.h i • (T.accExt a₀ ((k : ℤ) - i) - T.accExt a₀ k) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, F.sum_h, one_smul, planAcc]
  rw [key]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range (F.M + 1), ‖F.h i • (T.accExt a₀ ((k : ℤ) - i) - T.accExt a₀ k)‖
      ≤ ∑ i ∈ Finset.range (F.M + 1), |F.h i| * (i * δ * P.jerk) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_smul, Real.norm_eq_abs, norm_sub_rev]
        exact mul_le_mul_of_nonneg_left (T.acc_diff_le a₀ hδ hS' k i) (abs_nonneg _)
    _ = F.H1 * δ * P.jerk := by
        rw [H1, Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i _; ring

theorem planAcc_step (k : ℕ) :
    ‖F.planAcc T a₀ (k + 1) - F.planAcc T a₀ k‖ ≤ F.H0 * δ * P.jerk := by
  have hS' := hS.2.2
  have key : F.planAcc T a₀ (k + 1) - F.planAcc T a₀ k
      = ∑ i ∈ Finset.range (F.M + 1),
          F.h i • (T.accExt a₀ (((k : ℤ) - i) + 1) - T.accExt a₀ ((k : ℤ) - i)) := by
    simp only [planAcc, smul_sub, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    rw [show ((k + 1 : ℕ) : ℤ) - i = ((k : ℤ) - i) + 1 by push_cast; ring]
  rw [key]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range (F.M + 1),
        ‖F.h i • (T.accExt a₀ (((k : ℤ) - i) + 1) - T.accExt a₀ ((k : ℤ) - i))‖
      ≤ ∑ i ∈ Finset.range (F.M + 1), |F.h i| * (δ * P.jerk) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (T.accExt_succ_le a₀ hδ hS' _) (abs_nonneg _)
    _ = F.H0 * δ * P.jerk := by
        rw [H0, Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i _; ring

theorem planAcc_second (k : ℕ) :
    ‖F.planAcc T a₀ (k + 2) - 2 • F.planAcc T a₀ (k + 1) + F.planAcc T a₀ k‖
      ≤ F.TV * δ * P.jerk := by
  have hS' := hS.2.2
  set G : ℕ → E3 := fun j => T.accExt a₀ ((k : ℤ) + 2 - j) - T.accExt a₀ ((k : ℤ) + 1 - j)
    with hG
  have hGb : ∀ j, ‖G j‖ ≤ δ * P.jerk := by
    intro j
    have := T.accExt_succ_le a₀ hδ hS' ((k : ℤ) + 1 - j)
    rwa [show (k : ℤ) + 1 - j + 1 = (k : ℤ) + 2 - j by ring] at this
  have key : F.planAcc T a₀ (k + 2) - 2 • F.planAcc T a₀ (k + 1) + F.planAcc T a₀ k
      = ∑ i ∈ Finset.range (F.M + 1), F.h i • (G i - G (i + 1)) := by
    simp only [planAcc, hG, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [show ((k + 2 : ℕ) : ℤ) - i = (k : ℤ) + 2 - i by push_cast; ring,
      show ((k + 1 : ℕ) : ℤ) - i = (k : ℤ) + 1 - i by push_cast; ring,
      show (k : ℤ) + 2 - ((i + 1 : ℕ) : ℤ) = (k : ℤ) + 1 - i by push_cast; ring,
      show (k : ℤ) + 1 - ((i + 1 : ℕ) : ℤ) = (k : ℤ) - i by push_cast; ring]
    module
  rw [key, abel_sum, F.supp (F.M + 1) (by omega), zero_smul, sub_zero]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h1 : |F.h 0| * ‖G 0‖ ≤ |F.h 0| * (δ * P.jerk) :=
    mul_le_mul_of_nonneg_left (hGb 0) (abs_nonneg _)
  have h2 : ‖∑ i ∈ Finset.range (F.M + 1), (F.h (i + 1) - F.h i) • G (i + 1)‖
      ≤ ∑ i ∈ Finset.range (F.M + 1), |F.h (i + 1) - F.h i| * (δ * P.jerk) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hGb _) (abs_nonneg _)
  rw [TV, add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
  have : ∑ i ∈ Finset.range (F.M + 1), |F.h (i + 1) - F.h i| * (δ * P.jerk)
      = ∑ i ∈ Finset.range (F.M + 1), |F.h (i + 1) - F.h i| * δ * P.jerk := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [this] at h2
  linarith

omit hδ hS in
/-- **Causality.** The planned position at step `j ≤ k + 2` depends on the target only
through its positions up to step `k` (and its known initial velocity). -/
theorem planPos_congr (T T' : TargetTraj P δ) (a₀ off : E3) (k : ℕ)
    (hp : ∀ j ≤ k, T.p j = T'.p j) (hv : T.v 0 = T'.v 0) :
    ∀ j ≤ k + 2, F.planPos T a₀ off j = F.planPos T' a₀ off j := by
  intro j hj
  unfold planPos
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i < 2
  · interval_cases i <;> simp [F.h_zero, F.h_one]
  · congr 1
    unfold TargetTraj.ext
    split_ifs with hn
    · exact hp _ (by omega)
    · rw [hp 0 (by omega), hv]

end FIR

/-- The two-step-lag quadratic extrapolator `6 p_{k-2} - 8 p_{k-3} + 3 p_{k-4}`. -/
noncomputable def FIR.extrap3 : FIR where
  h i := if i = 2 then 6 else if i = 3 then -8 else if i = 4 then 3 else 0
  M := 4
  h_zero := by simp
  h_one := by simp
  supp i hi := by
    have : i ≠ 2 ∧ i ≠ 3 ∧ i ≠ 4 := by omega
    simp [this.1, this.2.1, this.2.2]
  sum_h := by simp [Finset.sum_range_succ]; norm_num
  mom1 := by simp [Finset.sum_range_succ]; norm_num
  mom2 := by simp [Finset.sum_range_succ]; norm_num

end VisionTracking
