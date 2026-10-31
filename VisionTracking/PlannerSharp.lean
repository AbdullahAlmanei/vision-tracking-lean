import VisionTracking.Planner

/-!
# Sharp planner error constants

Summation by parts turns the planner errors into sums of the target's acceleration
*changes*, weighted by iterated tail sums of the filter:
`T₁ = tail h`, `T₂ = tail T₁`, `T₃ = tail T₂`, where `tail g m = Σ_{m<i≤M} g i`.
With `G_j = Σ |T_j|`, the acceleration, velocity and position errors are at most
`G₁ δ j`, `G₂ δ² j` and `G₃ δ³ j`. These are exact worst cases over jerk-bounded
targets, much smaller than the triangle-inequality constants `H₁, H₂, H₃`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {δ : ℝ}

/-- `tail g n m = Σ_{m < i < n} g i`. -/
noncomputable def tailSum (g : ℕ → ℝ) (n m : ℕ) : ℝ := ∑ i ∈ Finset.Ico (m + 1) n, g i

/-- **Summation by parts.** -/
theorem abel_tail {E : Type*} [AddCommGroup E] [Module ℝ E] (g : ℕ → ℝ) (f : ℕ → E) (n : ℕ) :
    ∑ i ∈ Finset.range n, g i • (f i - f 0)
      = ∑ m ∈ Finset.range n, tailSum g n m • (f (m + 1) - f m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht : ∀ m ∈ Finset.range n, tailSum g (n + 1) m = tailSum g n m + g n := by
      intro m hm
      have hm' : m + 1 ≤ n := Finset.mem_range.1 hm
      unfold tailSum
      exact Finset.sum_Ico_succ_top hm' g
    have htn : tailSum g (n + 1) n = 0 := by unfold tailSum; simp
    conv_lhs => rw [Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ, htn, zero_smul, add_zero,
      Finset.sum_congr rfl (fun m hm => by rw [ht m hm])]
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← Finset.smul_sum, Finset.sum_range_sub]

/-- Summation by parts for weights summing to zero. -/
theorem sum_smul_eq_tail {E : Type*} [AddCommGroup E] [Module ℝ E] (g : ℕ → ℝ) (f : ℕ → E)
    (n : ℕ) (hg : ∑ i ∈ Finset.range n, g i = 0) :
    ∑ i ∈ Finset.range n, g i • f i = ∑ m ∈ Finset.range n, tailSum g n m • (f (m + 1) - f m) := by
  rw [← abel_tail]
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hg, zero_smul, sub_zero]

theorem sum_tailSum (g : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ Finset.range n, tailSum g n m = ∑ i ∈ Finset.range n, (i : ℝ) * g i := by
  calc ∑ m ∈ Finset.range n, tailSum g n m
      = ∑ m ∈ Finset.range n, tailSum g n m •
          ((fun i : ℕ => (i : ℝ)) (m + 1) - (fun i : ℕ => (i : ℝ)) m) :=
        Finset.sum_congr rfl (fun m _ => by simp)
    _ = ∑ i ∈ Finset.range n, g i • ((fun i : ℕ => (i : ℝ)) i - (fun i : ℕ => (i : ℝ)) 0) :=
        (abel_tail g (fun i : ℕ => (i : ℝ)) n).symm
    _ = ∑ i ∈ Finset.range n, (i : ℝ) * g i :=
        Finset.sum_congr rfl (fun i _ => by simp [mul_comm])

theorem sum_mul_tailSum (g : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ Finset.range n, (m : ℝ) * tailSum g n m
      = ∑ i ∈ Finset.range n, ((i : ℝ) * (i - 1) / 2) * g i := by
  calc ∑ m ∈ Finset.range n, (m : ℝ) * tailSum g n m
      = ∑ m ∈ Finset.range n, tailSum g n m •
          ((fun i : ℕ => (i : ℝ) * (i - 1) / 2) (m + 1) - (fun i : ℕ => (i : ℝ) * (i - 1) / 2) m) :=
        Finset.sum_congr rfl (fun m _ => by simp only [smul_eq_mul]; push_cast; ring)
    _ = ∑ i ∈ Finset.range n, g i •
          ((fun i : ℕ => (i : ℝ) * (i - 1) / 2) i - (fun i : ℕ => (i : ℝ) * (i - 1) / 2) 0) :=
        (abel_tail g (fun i : ℕ => (i : ℝ) * (i - 1) / 2) n).symm
    _ = ∑ i ∈ Finset.range n, ((i : ℝ) * (i - 1) / 2) * g i :=
        Finset.sum_congr rfl (fun i _ => by simp only [smul_eq_mul]; push_cast; ring)

namespace FIR

variable (F : FIR)

noncomputable def T1 (m : ℕ) : ℝ := tailSum F.h (F.M + 1) m
noncomputable def T2 (m : ℕ) : ℝ := tailSum F.T1 (F.M + 1) m
noncomputable def T3 (m : ℕ) : ℝ := tailSum F.T2 (F.M + 1) m
noncomputable def G1 : ℝ := ∑ m ∈ Finset.range (F.M + 1), |F.T1 m|
noncomputable def G2 : ℝ := ∑ m ∈ Finset.range (F.M + 1), |F.T2 m|
noncomputable def G3 : ℝ := ∑ m ∈ Finset.range (F.M + 1), |F.T3 m|

theorem sum_T1 : ∑ m ∈ Finset.range (F.M + 1), F.T1 m = 0 := by
  unfold T1; rw [sum_tailSum, F.mom1]

theorem sum_T2 : ∑ m ∈ Finset.range (F.M + 1), F.T2 m = 0 := by
  unfold T2; rw [sum_tailSum]
  have : ∑ i ∈ Finset.range (F.M + 1), (i : ℝ) * F.T1 i
      = ∑ i ∈ Finset.range (F.M + 1), ((i : ℝ) * (i - 1) / 2) * F.h i := by
    unfold T1; exact sum_mul_tailSum F.h (F.M + 1)
  rw [this]
  have e : ∀ i : ℕ, ((i : ℝ) * (i - 1) / 2) * F.h i
      = ((i : ℝ) ^ 2 * F.h i - (i : ℝ) * F.h i) / 2 := by intro i; ring
  simp only [e, ← Finset.sum_div, Finset.sum_sub_distrib, F.mom1, F.mom2]
  norm_num

variable (T : TargetTraj P δ) (a₀ off : E3) (hδ : 0 < δ) (hS : T.StartsAt (T.p 0) (T.v 0) a₀)
include hδ hS

/-- Reversed sequences seen from step `k`. -/
theorem acc_rev_step (k m : ℕ) :
    ‖T.accExt a₀ ((k : ℤ) - (m + 1 : ℕ)) - T.accExt a₀ ((k : ℤ) - m)‖ ≤ δ * P.jerk := by
  have := T.accExt_succ_le a₀ hδ hS.2.2 ((k : ℤ) - (m + 1 : ℕ))
  rw [show (k : ℤ) - ((m + 1 : ℕ) : ℤ) + 1 = (k : ℤ) - m by push_cast; ring, norm_sub_rev] at this
  exact this

omit hS in
theorem vel_rev_step (k m : ℕ) :
    T.velExt a₀ ((k : ℤ) - (m + 1 : ℕ)) - T.velExt a₀ ((k : ℤ) - m)
      = -δ • T.accExt a₀ ((k : ℤ) - (m + 1 : ℕ)) := by
  have := T.velExt_succ a₀ hδ.ne' ((k : ℤ) - (m + 1 : ℕ))
  rw [show (k : ℤ) - ((m + 1 : ℕ) : ℤ) + 1 = (k : ℤ) - m by push_cast; ring] at this
  rw [this]; module

omit hδ hS in
theorem pos_rev_step (k m : ℕ) :
    T.ext a₀ ((k : ℤ) - (m + 1 : ℕ)) - T.ext a₀ ((k : ℤ) - m)
      = -δ • T.velExt a₀ ((k : ℤ) - (m + 1 : ℕ)) := by
  have := T.ext_succ a₀ ((k : ℤ) - (m + 1 : ℕ))
  rw [show (k : ℤ) - ((m + 1 : ℕ) : ℤ) + 1 = (k : ℤ) - m by push_cast; ring] at this
  rw [this]; module

theorem norm_tail_acc_le (g : ℕ → ℝ) (j k : ℕ) :
    ‖∑ m ∈ Finset.range (F.M + 1), g m •
        (T.accExt a₀ ((k : ℤ) - (m + j + 1 : ℕ)) - T.accExt a₀ ((k : ℤ) - (m + j : ℕ)))‖
      ≤ (∑ m ∈ Finset.range (F.M + 1), |g m|) * (δ * P.jerk) := by
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (acc_rev_step T a₀ hδ hS k (m + j)) (abs_nonneg _)

theorem planAcc_err_sharp (k : ℕ) :
    ‖F.planAcc T a₀ k - T.accExt a₀ k‖ ≤ F.G1 * δ * P.jerk := by
  have key : F.planAcc T a₀ k - T.accExt a₀ k
      = ∑ m ∈ Finset.range (F.M + 1), F.T1 m •
          (T.accExt a₀ ((k : ℤ) - (m + 0 + 1 : ℕ)) - T.accExt a₀ ((k : ℤ) - (m + 0 : ℕ))) := by
    have h := abel_tail F.h (fun i : ℕ => T.accExt a₀ ((k : ℤ) - i)) (F.M + 1)
    simp only [Nat.cast_zero, sub_zero] at h
    simp only [add_zero]
    unfold T1
    rw [← h]
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, F.sum_h, one_smul, planAcc]
  rw [key]
  refine (norm_tail_acc_le F T a₀ hδ hS F.T1 0 k).trans (le_of_eq ?_)
  unfold G1; ring

theorem planVel_err_sharp (k : ℕ) : ‖F.planVel T a₀ k - T.v k‖ ≤ F.G2 * δ ^ 2 * P.jerk := by
  have h1 := abel_tail F.h (fun i : ℕ => T.velExt a₀ ((k : ℤ) - i)) (F.M + 1)
  simp only [Nat.cast_zero, sub_zero, vel_rev_step T a₀ hδ] at h1
  have h2 := sum_smul_eq_tail F.T1 (fun m : ℕ => T.accExt a₀ ((k : ℤ) - (m + 1 : ℕ))) (F.M + 1)
    F.sum_T1
  have key : F.planVel T a₀ k - T.v k
      = -δ • ∑ m ∈ Finset.range (F.M + 1), F.T2 m •
          (T.accExt a₀ ((k : ℤ) - (m + 1 + 1 : ℕ)) - T.accExt a₀ ((k : ℤ) - (m + 1 : ℕ))) := by
    have hs : F.planVel T a₀ k - T.v k = ∑ i ∈ Finset.range (F.M + 1),
        F.h i • (T.velExt a₀ ((k : ℤ) - i) - T.velExt a₀ k) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, F.sum_h, one_smul, planVel,
        T.velExt_natCast]
    rw [hs, h1]
    have e : ∑ m ∈ Finset.range (F.M + 1), tailSum F.h (F.M + 1) m •
        (-δ • T.accExt a₀ ((k : ℤ) - (m + 1 : ℕ)))
        = -δ • ∑ m ∈ Finset.range (F.M + 1), F.T1 m • T.accExt a₀ ((k : ℤ) - (m + 1 : ℕ)) := by
      rw [Finset.smul_sum]; unfold T1; exact Finset.sum_congr rfl (fun m _ => by rw [smul_comm])
    rw [e, h2]; unfold T2; rfl
  rw [key, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδ]
  have := norm_tail_acc_le F T a₀ hδ hS F.T2 1 k
  calc δ * ‖∑ m ∈ Finset.range (F.M + 1), F.T2 m •
        (T.accExt a₀ ((k : ℤ) - (m + 1 + 1 : ℕ)) - T.accExt a₀ ((k : ℤ) - (m + 1 : ℕ)))‖
      ≤ δ * ((∑ m ∈ Finset.range (F.M + 1), |F.T2 m|) * (δ * P.jerk)) :=
        mul_le_mul_of_nonneg_left this hδ.le
    _ = F.G2 * δ ^ 2 * P.jerk := by unfold G2; ring

theorem planPos_err_sharp (k : ℕ) :
    ‖F.planPos T a₀ off k - (T.p k + off)‖ ≤ F.G3 * δ ^ 3 * P.jerk := by
  have h1 := abel_tail F.h (fun i : ℕ => T.ext a₀ ((k : ℤ) - i)) (F.M + 1)
  simp only [Nat.cast_zero, sub_zero, pos_rev_step T a₀] at h1
  have h2 := sum_smul_eq_tail F.T1 (fun m : ℕ => T.velExt a₀ ((k : ℤ) - (m + 1 : ℕ))) (F.M + 1)
    F.sum_T1
  simp only [show ∀ m : ℕ, m + 1 + 1 = (m + 1) + 1 from fun _ => rfl] at h2
  have hv2 : ∀ m : ℕ, T.velExt a₀ ((k : ℤ) - (m + 1 + 1 : ℕ)) - T.velExt a₀ ((k : ℤ) - (m + 1 : ℕ))
      = -δ • T.accExt a₀ ((k : ℤ) - (m + 1 + 1 : ℕ)) := fun m => vel_rev_step T a₀ hδ k (m + 1)
  simp only [hv2] at h2
  have h3 := sum_smul_eq_tail F.T2 (fun m : ℕ => T.accExt a₀ ((k : ℤ) - (m + 2 : ℕ))) (F.M + 1)
    F.sum_T2
  have key : F.planPos T a₀ off k - (T.p k + off)
      = δ ^ 2 • ∑ m ∈ Finset.range (F.M + 1), F.T3 m •
          (T.accExt a₀ ((k : ℤ) - (m + 2 + 1 : ℕ)) - T.accExt a₀ ((k : ℤ) - (m + 2 : ℕ))) := by
    have hs : F.planPos T a₀ off k - (T.p k + off) = ∑ i ∈ Finset.range (F.M + 1),
        F.h i • (T.ext a₀ ((k : ℤ) - i) - T.ext a₀ k) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, F.sum_h, one_smul, planPos,
        T.ext_natCast]
      abel
    rw [hs, h1]
    have e1 : ∑ m ∈ Finset.range (F.M + 1), tailSum F.h (F.M + 1) m •
        (-δ • T.velExt a₀ ((k : ℤ) - (m + 1 : ℕ)))
        = -δ • ∑ m ∈ Finset.range (F.M + 1), F.T1 m • T.velExt a₀ ((k : ℤ) - (m + 1 : ℕ)) := by
      rw [Finset.smul_sum]; unfold T1; exact Finset.sum_congr rfl (fun m _ => by rw [smul_comm])
    rw [e1, h2]
    have e2 : ∑ m ∈ Finset.range (F.M + 1), tailSum F.T1 (F.M + 1) m •
        (-δ • T.accExt a₀ ((k : ℤ) - (m + 1 + 1 : ℕ)))
        = -δ • ∑ m ∈ Finset.range (F.M + 1), F.T2 m • T.accExt a₀ ((k : ℤ) - (m + 2 : ℕ)) := by
      rw [Finset.smul_sum]; unfold T2; exact Finset.sum_congr rfl (fun m _ => by rw [smul_comm])
    rw [e2, h3, smul_smul]
    unfold T3
    congr 1
    · ring
  rw [key, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have := norm_tail_acc_le F T a₀ hδ hS F.T3 2 k
  calc δ ^ 2 * ‖∑ m ∈ Finset.range (F.M + 1), F.T3 m •
        (T.accExt a₀ ((k : ℤ) - (m + 2 + 1 : ℕ)) - T.accExt a₀ ((k : ℤ) - (m + 2 : ℕ)))‖
      ≤ δ ^ 2 * ((∑ m ∈ Finset.range (F.M + 1), |F.T3 m|) * (δ * P.jerk)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = F.G3 * δ ^ 3 * P.jerk := by unfold G3; ring

end FIR

end VisionTracking
