import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Convex.Slope
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Rat.BigOperators
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Countable.Defs
import Mathlib.Order.Filter.Cofinite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Logic.Relation
import Mathlib.Topology.Instances.Rat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

section
set_option autoImplicit true
open Finset

theorem integer_nearest (z m : ℤ) (a : ℝ)
    (hlo : (z : ℝ) - 1/2 ≤ a) (hhi : a ≤ (z : ℝ) + 1/2) :
    ((z : ℝ) - a)^2 ≤ ((m : ℝ) - a)^2 := by
  rcases lt_trichotomy m z with h | h | h
  · have hz : m + 1 ≤ z := by omega
    have hr : (m : ℝ) + 1 ≤ z := by exact_mod_cast hz
    nlinarith [sq_nonneg ((m : ℝ) - (z : ℝ))]
  · subst m
    exact le_refl _
  · have hz : z + 1 ≤ m := by omega
    have hr : (z : ℝ) + 1 ≤ m := by exact_mod_cast hz
    nlinarith [sq_nonneg ((m : ℝ) - (z : ℝ))]

theorem integer_nearest_strict (z m : ℤ) (a : ℝ)
    (hlo : (z : ℝ) - 1/2 < a) (hhi : a < (z : ℝ) + 1/2)
    (hne : m ≠ z) :
    ((z : ℝ) - a)^2 < ((m : ℝ) - a)^2 := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hz : m + 1 ≤ z := by omega
    have hr : (m : ℝ) + 1 ≤ z := by exact_mod_cast hz
    have hp : 0 < ((z : ℝ) - (m : ℝ)) * (2*a - (z : ℝ) - (m : ℝ)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · have hz : z + 1 ≤ m := by omega
    have hr : (z : ℝ) + 1 ≤ m := by exact_mod_cast hz
    have hp : 0 < ((m : ℝ) - (z : ℝ)) * ((m : ℝ) + (z : ℝ) - 2*a) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

noncomputable def fourTarget (q : ℕ) : Fin 4 → ℝ :=
  ![4*(q : ℝ)+2/5, 3*(q : ℝ)+3/10, 2*(q : ℝ)+1/5, (q : ℝ)+1/10]

def fourGrid (q : ℕ) : Fin 4 → ℤ :=
  ![4*(q : ℤ), 3*(q : ℤ), 2*(q : ℤ), (q : ℤ)]

def squareLoss (a : Fin 4 → ℝ) (z : Fin 4 → ℤ) : ℝ :=
  ∑ i, ((z i : ℝ) - a i)^2

theorem four_rounding_interior (q : ℕ) (i : Fin 4) :
    (fourGrid q i : ℝ) - 1/2 < fourTarget q i ∧
    fourTarget q i < (fourGrid q i : ℝ) + 1/2 := by
  fin_cases i <;> simp [fourTarget, fourGrid] <;> norm_num <;> linarith

theorem four_global_minimum (q : ℕ) (z : Fin 4 → ℤ) :
    squareLoss (fourTarget q) (fourGrid q) ≤ squareLoss (fourTarget q) z := by
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨hlo, hhi⟩ := four_rounding_interior q i
  exact integer_nearest _ _ _ hlo.le hhi.le

theorem four_unique_minimum (q : ℕ) (z : Fin 4 → ℤ) (hne : z ≠ fourGrid q) :
    squareLoss (fourTarget q) (fourGrid q) < squareLoss (fourTarget q) z := by
  have hex : ∃ i, z i ≠ fourGrid q i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨j, hj⟩ := hex
  apply Finset.sum_lt_sum
  · intro i _
    obtain ⟨hlo, hhi⟩ := four_rounding_interior q i
    exact integer_nearest _ _ _ hlo.le hhi.le
  · refine ⟨j, Finset.mem_univ _, ?_⟩
    obtain ⟨hlo, hhi⟩ := four_rounding_interior q j
    exact integer_nearest_strict _ _ _ hlo hhi hj

theorem four_grid_nonnegative (q : ℕ) (i : Fin 4) : 0 ≤ fourGrid q i := by
  fin_cases i <;> simp [fourGrid]

theorem four_grid_slack (q : ℕ) :
    (10*(q : ℤ)+1) - ∑ i, fourGrid q i = 1 := by
  simp [fourGrid, Fin.sum_univ_succ]
  ring

theorem four_exact_loss (q : ℕ) : squareLoss (fourTarget q) (fourGrid q) = 3/10 := by
  simp [squareLoss, fourTarget, fourGrid, Fin.sum_univ_succ]
  ring

theorem four_completed_square (d : Fin 4 → ℝ) :
    5 * ∑ i, (d i)^2 - (4*d 0 + 3*d 1 + 2*d 2 + d 3) =
      5 * ∑ i, (d i - (![4/10,3/10,2/10,1/10] : Fin 4 → ℝ) i)^2 - 3/2 := by
  simp [Fin.sum_univ_succ]
  ring



open Finset

namespace GridResidueCertificate

def loss {N : ℕ} (y : Fin N → ℝ) (n : Fin N → ℤ) : ℝ :=
  ∑ i, ((n i : ℝ) - y i)^2

def feasible {N : ℕ} (M : ℤ) (n : Fin N → ℤ) : Prop :=
  (∀ i, 0 ≤ n i) ∧ ∑ i, n i ≤ M

theorem nearest_integer (n z : ℤ) (a : ℝ)
    (hlo : (n : ℝ) - 1/2 ≤ a) (hhi : a ≤ (n : ℝ) + 1/2) :
    ((n : ℝ) - a)^2 ≤ ((z : ℝ) - a)^2 := by
  rcases lt_trichotomy z n with h | h | h
  · have hg : z + 1 ≤ n := by omega
    have hg' : (z : ℝ) + 1 ≤ n := by exact_mod_cast hg
    have hp : 0 ≤ ((n : ℝ) - z) * (2*a - n - z) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · subst z
    rfl
  · have hg : n + 1 ≤ z := by omega
    have hg' : (n : ℝ) + 1 ≤ z := by exact_mod_cast hg
    have hp : 0 ≤ ((z : ℝ) - n) * ((z : ℝ) + n - 2*a) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

theorem nearest_integer_strict (n z : ℤ) (a : ℝ)
    (hlo : (n : ℝ) - 1/2 < a) (hhi : a < (n : ℝ) + 1/2)
    (hne : z ≠ n) :
    ((n : ℝ) - a)^2 < ((z : ℝ) - a)^2 := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hg : z + 1 ≤ n := by omega
    have hg' : (z : ℝ) + 1 ≤ n := by exact_mod_cast hg
    have hp : 0 < ((n : ℝ) - z) * (2*a - n - z) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · have hg : n + 1 ≤ z := by omega
    have hg' : (n : ℝ) + 1 ≤ z := by exact_mod_cast hg
    have hp : 0 < ((z : ℝ) - n) * ((z : ℝ) + n - 2*a) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

theorem shifted_loss_difference {N : ℕ} (y : Fin N → ℝ)
    (n z : Fin N → ℤ) (lam : ℝ) :
    loss (fun i => y i - lam) z - loss (fun i => y i - lam) n =
      loss y z - loss y n + 2*lam*((∑ i, (z i : ℝ)) - ∑ i, (n i : ℝ)) := by
  have he : ∀ i, ((z i : ℝ) - (y i - lam))^2 - ((n i : ℝ) - (y i - lam))^2 =
      (((z i : ℝ) - y i)^2 - ((n i : ℝ) - y i)^2) +
        2*lam*((z i : ℝ) - n i) := by
    intro i
    ring
  unfold loss
  rw [← Finset.sum_sub_distrib]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]

theorem multiplier_certificate {N : ℕ} (y : Fin N → ℝ) (M : ℤ)
    (n z : Fin N → ℤ) (lam : ℝ)
    (_hn : feasible M n) (hz : feasible M z) (hlam : 0 ≤ lam)
    (hcomp : lam*((M : ℝ) - ∑ i, (n i : ℝ)) = 0)
    (hnearest : ∀ i, (n i : ℝ) - 1/2 ≤ y i - lam ∧
      y i - lam ≤ (n i : ℝ) + 1/2) :
    loss y n ≤ loss y z := by
  have hsum : loss (fun i => y i - lam) n ≤ loss (fun i => y i - lam) z := by
    apply Finset.sum_le_sum
    intro i _
    exact nearest_integer _ _ _ (hnearest i).1 (hnearest i).2
  have hzm : (∑ i, (z i : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hz.2
  have hprod : lam*((M : ℝ) - ∑ i, (z i : ℝ)) ≥ 0 :=
    mul_nonneg hlam (by linarith)
  have he := shifted_loss_difference y n z lam
  nlinarith

theorem strict_multiplier_certificate {N : ℕ} (y : Fin N → ℝ) (M : ℤ)
    (n z : Fin N → ℤ) (lam : ℝ)
    (_hn : feasible M n) (hz : feasible M z) (hlam : 0 ≤ lam)
    (hcomp : lam*((M : ℝ) - ∑ i, (n i : ℝ)) = 0)
    (hnearest : ∀ i, (n i : ℝ) - 1/2 < y i - lam ∧
      y i - lam < (n i : ℝ) + 1/2) (hne : z ≠ n) :
    loss y n < loss y z := by
  have hex : ∃ i, z i ≠ n i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨j, hj⟩ := hex
  have hsum : loss (fun i => y i - lam) n < loss (fun i => y i - lam) z := by
    apply Finset.sum_lt_sum
    · intro i _
      exact nearest_integer _ _ _ (hnearest i).1.le (hnearest i).2.le
    · refine ⟨j, Finset.mem_univ _, ?_⟩
      exact nearest_integer_strict _ _ _ (hnearest j).1 (hnearest j).2 hj
  have hzm : (∑ i, (z i : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hz.2
  have hprod : lam*((M : ℝ) - ∑ i, (z i : ℝ)) ≥ 0 :=
    mul_nonneg hlam (by linarith)
  have he := shifted_loss_difference y n z lam
  nlinarith

def weights : Fin 4 → ℤ := ![4,3,2,1]

def residueBase (r : Fin 10) : Fin 4 → ℤ :=
  match (r : ℕ) with
  | 0 => ![0,0,0,0]
  | 1 => ![0,0,0,0]
  | 2 => ![1,1,0,0]
  | 3 => ![1,1,1,0]
  | 4 => ![2,1,1,0]
  | 5 => ![2,1,1,0]
  | 6 => ![2,2,1,1]
  | 7 => ![3,2,1,1]
  | 8 => ![3,2,2,1]
  | _ => ![3,3,2,1]

def residuePoint (q : ℕ) (r : Fin 10) (i : Fin 4) : ℤ :=
  (q : ℤ)*weights i + residueBase r i

def residueCapacity (q : ℕ) (r : Fin 10) : ℤ := 10*(q : ℤ) + (r : ℕ)

noncomputable def residueTarget (q : ℕ) (r : Fin 10) (i : Fin 4) : ℝ :=
  (residueCapacity q r : ℝ)*(weights i : ℝ)/10

noncomputable def residueMultiplier (r : Fin 10) : ℝ := if (r : ℕ) = 9 then 3/20 else 0

theorem residue_feasible (q : ℕ) (r : Fin 10) :
    feasible (residueCapacity q r) (residuePoint q r) := by
  constructor
  · intro i
    fin_cases r <;> fin_cases i <;>
      simp [residuePoint, residueBase, weights] <;> omega
  · fin_cases r <;>
      simp [residueCapacity, residuePoint, residueBase, weights, Fin.sum_univ_succ] <;>
      omega

theorem residue_multiplier_nonnegative (r : Fin 10) : 0 ≤ residueMultiplier r := by
  unfold residueMultiplier
  split <;> norm_num

theorem residue_complementarity (q : ℕ) (r : Fin 10) :
    residueMultiplier r*((residueCapacity q r : ℝ) - ∑ i, (residuePoint q r i : ℝ)) = 0 := by
  fin_cases r <;>
    norm_num [residueMultiplier, residueCapacity, residuePoint, residueBase, weights,
      Fin.sum_univ_succ]
  all_goals ring

theorem residue_rounding (q : ℕ) (r : Fin 10) (i : Fin 4) :
    (residuePoint q r i : ℝ) - 1/2 ≤ residueTarget q r i - residueMultiplier r ∧
      residueTarget q r i - residueMultiplier r ≤ (residuePoint q r i : ℝ) + 1/2 := by
  fin_cases r <;> fin_cases i <;>
    norm_num [residuePoint, residueBase, weights, residueTarget, residueCapacity,
      residueMultiplier] <;> constructor <;> linarith

theorem residue_rounding_strict (q : ℕ) (r : Fin 10) (hr : (r : ℕ) ≠ 5) (i : Fin 4) :
    (residuePoint q r i : ℝ) - 1/2 < residueTarget q r i - residueMultiplier r ∧
      residueTarget q r i - residueMultiplier r < (residuePoint q r i : ℝ) + 1/2 := by
  fin_cases r <;> fin_cases i <;>
    norm_num [residuePoint, residueBase, weights, residueTarget, residueCapacity,
      residueMultiplier] at * <;> constructor <;> linarith

theorem residue_global_minimum (q : ℕ) (r : Fin 10) (z : Fin 4 → ℤ)
    (hz : feasible (residueCapacity q r) z) :
    loss (residueTarget q r) (residuePoint q r) ≤ loss (residueTarget q r) z := by
  exact multiplier_certificate _ _ _ _ _ (residue_feasible q r) hz
    (residue_multiplier_nonnegative r) (residue_complementarity q r)
    (residue_rounding q r)

theorem residue_unique_minimum (q : ℕ) (r : Fin 10) (hr : (r : ℕ) ≠ 5) (z : Fin 4 → ℤ)
    (hz : feasible (residueCapacity q r) z) (hne : z ≠ residuePoint q r) :
    loss (residueTarget q r) (residuePoint q r) < loss (residueTarget q r) z := by
  exact strict_multiplier_certificate _ _ _ _ _ (residue_feasible q r) hz
    (residue_multiplier_nonnegative r) (residue_complementarity q r)
    (residue_rounding_strict q r hr) hne

theorem residue_slack (q : ℕ) (r : Fin 10) :
    residueCapacity q r - ∑ i, residuePoint q r i = if (r : ℕ) = 1 ∨ (r : ℕ) = 5 then 1 else 0 := by
  fin_cases r <;>
    norm_num [residueCapacity, residuePoint, residueBase, weights, Fin.sum_univ_succ] <;> ring

theorem residue_exact_loss (q : ℕ) (r : Fin 10) :
    loss (residueTarget q r) (residuePoint q r) =
      (![0,30,40,30,40,50,40,30,40,50] : Fin 10 → ℝ) r / 100 := by
  fin_cases r <;>
    norm_num [loss, residueTarget, residueCapacity, residuePoint, residueBase, weights,
      Fin.sum_univ_succ] <;> ring

def halfPointOne (q : ℕ) : Fin 4 → ℤ :=
  ![4*(q : ℤ)+2, 3*(q : ℤ)+1, 2*(q : ℤ)+1, (q : ℤ)+1]

def halfPointTwo (q : ℕ) : Fin 4 → ℤ :=
  ![4*(q : ℤ)+2, 3*(q : ℤ)+2, 2*(q : ℤ)+1, (q : ℤ)]

theorem adjacent_product_nonnegative (z k : ℤ) : 0 ≤ (z-k)*(z-k-1) := by
  by_cases h : z ≤ k
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  · exact mul_nonneg (by omega) (by omega)

theorem half_point_one_feasible (q : ℕ) :
    feasible (residueCapacity q 5) (halfPointOne q) := by
  constructor
  · intro i
    fin_cases i <;> simp [halfPointOne] <;> omega
  · simp [residueCapacity, halfPointOne, Fin.sum_univ_succ]
    omega

theorem half_point_two_feasible (q : ℕ) :
    feasible (residueCapacity q 5) (halfPointTwo q) := by
  constructor
  · intro i
    fin_cases i <;> simp [halfPointTwo] <;> omega
  · simp [residueCapacity, halfPointTwo, Fin.sum_univ_succ]
    omega

theorem half_point_one_loss (q : ℕ) : loss (residueTarget q 5) (halfPointOne q) = 1/2 := by
  norm_num [loss, residueTarget, residueCapacity, weights, halfPointOne, Fin.sum_univ_succ]
  ring

theorem half_point_two_loss (q : ℕ) : loss (residueTarget q 5) (halfPointTwo q) = 1/2 := by
  norm_num [loss, residueTarget, residueCapacity, weights, halfPointTwo, Fin.sum_univ_succ]
  ring

theorem residue_five_complete (q : ℕ) (z : Fin 4 → ℤ)
    (hz : feasible (residueCapacity q 5) z) :
    loss (residueTarget q 5) z = 1/2 ↔
      z = residuePoint q 5 ∨ z = halfPointOne q ∨ z = halfPointTwo q := by
  constructor
  · intro he
    have h1 := adjacent_product_nonnegative (z 1) (3*(q : ℤ)+1)
    have h3 := adjacent_product_nonnegative (z 3) (q : ℤ)
    have h1r : (0 : ℝ) ≤ (((z 1 - (3*(q : ℤ)+1)) *
        (z 1 - (3*(q : ℤ)+1) - 1) : ℤ) : ℝ) := by exact_mod_cast h1
    have h3r : (0 : ℝ) ≤ (((z 3 - (q : ℤ)) * (z 3 - (q : ℤ) - 1) : ℤ) : ℝ) :=
      by exact_mod_cast h3
    push_cast at h1r h3r
    have h0 := sq_nonneg ((z 0 : ℝ) - (4*(q : ℝ)+2))
    have h2 := sq_nonneg ((z 2 : ℝ) - (2*(q : ℝ)+1))
    norm_num [loss, residueTarget, residueCapacity, weights, Fin.sum_univ_succ] at he
    change ((z 0 : ℝ) - (10*(q : ℝ)+5)*4/10)^2 +
      (((z 1 : ℝ) - (10*(q : ℝ)+5)*3/10)^2 +
        (((z 2 : ℝ) - (10*(q : ℝ)+5)*2/10)^2 +
          ((z 3 : ℝ) - (10*(q : ℝ)+5)/10)^2)) = 1/2 at he
    have h0eq : ((z 0 : ℝ) - (4*(q : ℝ)+2))^2 = 0 := by nlinarith
    have h2eq : ((z 2 : ℝ) - (2*(q : ℝ)+1))^2 = 0 := by nlinarith
    have h0real : (z 0 : ℝ) = 4*(q : ℝ)+2 := sub_eq_zero.mp (sq_eq_zero_iff.mp h0eq)
    have h2real : (z 2 : ℝ) = 2*(q : ℝ)+1 := sub_eq_zero.mp (sq_eq_zero_iff.mp h2eq)
    have hz0 : z 0 = 4*(q : ℤ)+2 := by exact_mod_cast h0real
    have hz2 : z 2 = 2*(q : ℤ)+1 := by exact_mod_cast h2real
    have h1eq : ((z 1 : ℝ) - (3*(q : ℝ)+1))*((z 1 : ℝ) - (3*(q : ℝ)+2)) = 0 :=
      by nlinarith
    have h3eq : ((z 3 : ℝ) - (q : ℝ))*((z 3 : ℝ) - ((q : ℝ)+1)) = 0 :=
      by nlinarith
    have hz1 : z 1 = 3*(q : ℤ)+1 ∨ z 1 = 3*(q : ℤ)+2 := by
      rcases mul_eq_zero.mp h1eq with h | h
      · left
        exact_mod_cast (sub_eq_zero.mp h)
      · right
        exact_mod_cast (sub_eq_zero.mp h)
    have hz3 : z 3 = (q : ℤ) ∨ z 3 = (q : ℤ)+1 := by
      rcases mul_eq_zero.mp h3eq with h | h
      · left
        exact_mod_cast (sub_eq_zero.mp h)
      · right
        exact_mod_cast (sub_eq_zero.mp h)
    have hmass := hz.2
    norm_num [residueCapacity, Fin.sum_univ_succ] at hmass
    change z 0 + (z 1 + (z 2 + z 3)) ≤ 10*(q : ℤ)+5 at hmass
    rcases hz1 with hz1 | hz1 <;> rcases hz3 with hz3 | hz3
    · left
      funext i
      fin_cases i <;> simp [residuePoint, residueBase, weights] <;> omega
    · right
      left
      funext i
      fin_cases i <;> simp [halfPointOne] <;> omega
    · right
      right
      funext i
      fin_cases i <;> simp [halfPointTwo] <;> omega
    · omega
  · intro hz
    rcases hz with rfl | rfl | rfl
    · have h := residue_exact_loss q 5
      change loss (residueTarget q 5) (residuePoint q 5) = (50 : ℝ)/100 at h
      norm_num at h
      exact h
    · exact half_point_one_loss q
    · exact half_point_two_loss q


end GridResidueCertificate

noncomputable def quadraticEnergy (d : Fin 4 → ℝ) : ℝ :=
  5*∑ i, (d i)^2-(4*d 0+3*d 1+2*d 2+d 3)

theorem four_energy_loss (q : ℕ) (z : Fin 4 → ℤ) :
    quadraticEnergy (fun i => (z i : ℝ)/(10*(q:ℝ)+1)) =
      (5/(10*(q:ℝ)+1)^2)*squareLoss (fourTarget q) z-3/2 := by
  have hM : 10*(q:ℝ)+1 ≠ 0 := by positivity
  simp [quadraticEnergy, squareLoss, fourTarget, Fin.sum_univ_succ]
  field_simp
  ring

theorem four_energy_unique (q : ℕ) (z : Fin 4 → ℤ) (hz : z ≠ fourGrid q) :
    quadraticEnergy (fun i => (fourGrid q i : ℝ)/(10*(q:ℝ)+1)) <
      quadraticEnergy (fun i => (z i : ℝ)/(10*(q:ℝ)+1)) := by
  rw [four_energy_loss, four_energy_loss]
  exact sub_lt_sub_right (mul_lt_mul_of_pos_left (four_unique_minimum q z hz) (by positivity)) _

theorem four_energy_gap (q : ℕ) :
    quadraticEnergy (fun i => (fourGrid q i : ℝ)/(10*(q:ℝ)+1)) + 3/2 =
      3/(2*(10*(q:ℝ)+1)^2) := by
  rw [four_energy_loss, four_exact_loss]
  have hM : 10*(q:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem four_terminal_value (q : ℕ) :
    1-(∑ i, (fourGrid q i : ℝ)/(10*(q:ℝ)+1)) = 1/(10*(q:ℝ)+1) := by
  have hM : 10*(q:ℝ)+1 ≠ 0 := by positivity
  simp [fourGrid, Fin.sum_univ_succ]
  field_simp
  ring

theorem four_terminal_positive (q : ℕ) :
    0 < 1-(∑ i, (fourGrid q i : ℝ)/(10*(q:ℝ)+1)) := by
  rw [four_terminal_value]
  positivity

theorem eleven_mesh_form (j : ℕ) : ∃ q : ℕ, 11^j=10*q+1 := by
  have hm : 11^j%10=1 := by simp [Nat.pow_mod]
  exact ⟨11^j/10,by omega⟩

theorem eleven_mesh_nested (j : ℕ) : 11^j ∣ 11^(j+1) := by
  rw [pow_succ]
  exact dvd_mul_right _ _

theorem ternary_residue_zero (j : ℕ) : 3^(4*j)%10=1 := by
  rw [pow_mul, Nat.pow_mod]
  norm_num

theorem ternary_residue_one (j : ℕ) : 3^(4*j+1)%10=3 := by
  rw [pow_add,Nat.mul_mod,ternary_residue_zero]
  norm_num

theorem ternary_residue_two (j : ℕ) : 3^(4*j+2)%10=9 := by
  rw [pow_add,Nat.mul_mod,ternary_residue_zero]
  norm_num

theorem ternary_residue_three (j : ℕ) : 3^(4*j+3)%10=7 := by
  rw [pow_add,Nat.mul_mod,ternary_residue_zero]
  norm_num

theorem ternary_mesh_nested (j : ℕ) : 3^j ∣ 3^(j+1) := by
  rw [pow_succ]
  exact dvd_mul_right _ _


namespace RematGeneral

def loss {N : ℕ} (y : Fin N → ℝ) (n : Fin N → ℤ) : ℝ :=
  ∑ i, ((n i : ℝ) - y i)^2

def feasible {N : ℕ} (M : ℤ) (n : Fin N → ℤ) : Prop :=
  (∀ i, 0 ≤ n i) ∧ ∑ i, n i ≤ M

def isMinimum {N : ℕ} (M : ℤ) (y : Fin N → ℝ) (n : Fin N → ℤ) : Prop :=
  feasible M n ∧ ∀ z, feasible M z → loss y n ≤ loss y z

theorem sum_update {N : ℕ} (n : Fin N → ℤ) (i : Fin N) (v : ℤ) :
    ∑ j, Function.update n i v j = (∑ j, n j) + v - n i := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  simp only [sdiff_singleton_eq_erase]
  have h := Finset.sum_erase_add Finset.univ n (Finset.mem_univ i)
  omega

theorem loss_update {N : ℕ} (y : Fin N → ℝ) (n : Fin N → ℤ)
    (i : Fin N) (v : ℤ) :
    loss y (Function.update n i v) = loss y n + ((v : ℝ)-y i)^2 - ((n i : ℝ)-y i)^2 := by
  have h : (fun j => (((Function.update n i v) j : ℝ)-y j)^2) =
      Function.update (fun j => ((n j : ℝ)-y j)^2) i (((v : ℝ)-y i)^2) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hj]
  unfold loss
  rw [h, Finset.sum_update_of_mem (Finset.mem_univ i)]
  simp only [sdiff_singleton_eq_erase]
  have hs := Finset.sum_erase_add Finset.univ (fun j => ((n j : ℝ)-y j)^2) (Finset.mem_univ i)
  linarith

theorem coordinate_upper {N : ℕ} (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (n : Fin N → ℤ) (hn : isMinimum M y n) (i : Fin N) :
    n i ≤ ⌈y i⌉ := by
  by_contra hi
  have hni : ⌈y i⌉ < n i := by omega
  have hyi : y i ≤ (n i : ℝ) - 1 := Int.ceil_lt_iff.mp hni
  have hp : 0 < n i := by
    have hc : 0 ≤ (⌈y i⌉ : ℤ) := by exact_mod_cast (hy i).trans (Int.le_ceil (y i))
    omega
  have hz : feasible M (Function.update n i (n i - 1)) := by
    constructor
    · intro j
      by_cases hji : j = i
      · subst j
        simp
        omega
      · simpa [Function.update_of_ne hji] using hn.1.1 j
    · rw [sum_update]
      have hs := hn.1.2
      omega
  have hmin := hn.2 _ hz
  rw [loss_update] at hmin
  push_cast at hmin
  nlinarith

theorem coordinate_lower {N : ℕ} (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (n : Fin N → ℤ) (hn : isMinimum M y n) (i : Fin N) :
    ⌊y i⌋ ≤ n i := by
  by_contra hi
  have hni : n i < ⌊y i⌋ := by omega
  have hyi : (n i : ℝ) + 1 ≤ y i := Int.lt_floor_iff.mp hni
  by_cases hslack : ∑ j, n j < M
  · have hz : feasible M (Function.update n i (n i + 1)) := by
      constructor
      · intro j
        by_cases hji : j = i
        · subst j
          simpa using add_nonneg (hn.1.1 i) (show (0 : ℤ) ≤ 1 by omega)
        · simpa [Function.update_of_ne hji] using hn.1.1 j
      · rw [sum_update]
        omega
    have hmin := hn.2 _ hz
    rw [loss_update] at hmin
    push_cast at hmin
    nlinarith
  · have heq : ∑ j, n j = M := le_antisymm hn.1.2 (by omega)
    have heqreal : ∑ j, (n j : ℝ) = (M : ℝ) := by exact_mod_cast heq
    have hex : ∃ j, y j < (n j : ℝ) := by
      by_contra h
      push Not at h
      have hlt : ∑ j, (n j : ℝ) < ∑ j, y j := by
        apply Finset.sum_lt_sum
        · intro j _
          exact h j
        · exact ⟨i, Finset.mem_univ i, by linarith⟩
      linarith
    obtain ⟨j, hj⟩ := hex
    have hji : j ≠ i := by
      intro h
      subst j
      linarith
    have hjpos : 0 < n j := by exact_mod_cast lt_of_le_of_lt (hy j) hj
    let z := Function.update (Function.update n j (n j - 1)) i (n i + 1)
    have hz : feasible M z := by
      constructor
      · intro k
        by_cases hki : k = i
        · subst k
          dsimp [z]
          simp
          have hi0 := hn.1.1 i
          omega
        · by_cases hkj : k = j
          · subst k
            simp [z, Function.update_of_ne hji]
            omega
          · simpa [z, Function.update_of_ne hki, Function.update_of_ne hkj] using hn.1.1 k
      · dsimp [z]
        rw [sum_update, sum_update]
        simp only [Function.update_of_ne (Ne.symm hji)]
        omega
    have hmin := hn.2 z hz
    dsimp [z] at hmin
    rw [loss_update, loss_update] at hmin
    simp only [Function.update_of_ne (Ne.symm hji)] at hmin
    push_cast at hmin
    nlinarith

theorem coordinate_proximity {N : ℕ} (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (n : Fin N → ℤ) (hn : isMinimum M y n) :
    ∀ i, ⌊y i⌋ ≤ n i ∧ n i ≤ ⌈y i⌉ := by
  intro i
  exact ⟨coordinate_lower M y hy hs n hn i, coordinate_upper M y hy n hn i⟩

theorem minimum_exists {N : ℕ} (M : ℤ) (hM : 0 ≤ M) (y : Fin N → ℝ) :
    ∃ n, isMinimum M y n := by
  classical
  let box := Fintype.piFinset (fun _ : Fin N => Finset.Icc (0 : ℤ) M)
  let candidates := box.filter (fun n => ∑ i, n i ≤ M)
  have mem_iff (n : Fin N → ℤ) : n ∈ candidates ↔ feasible M n := by
    simp only [candidates, box, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, feasible]
    constructor
    · intro h
      exact ⟨fun i => (h.1 i).1, h.2⟩
    · intro h
      refine ⟨?_, h.2⟩
      intro i
      refine ⟨h.1 i, le_trans ?_ h.2⟩
      exact Finset.single_le_sum (fun j _ => h.1 j) (Finset.mem_univ i)
  have hnonempty : candidates.Nonempty := by
    refine ⟨fun _ => 0, (mem_iff _).mpr ?_⟩
    exact ⟨fun _ => le_refl _, by simpa using hM⟩
  obtain ⟨n, hn, hmin⟩ := candidates.exists_min_image (loss y) hnonempty
  exact ⟨n, (mem_iff n).mp hn, fun z hz => hmin z ((mem_iff z).mpr hz)⟩

theorem loss_translation {N : ℕ} (p z : Fin N → ℤ) (y : Fin N → ℝ) :
    loss (fun i => (p i : ℝ) + y i) (fun i => p i + z i) = loss y z := by
  unfold loss
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

theorem feasible_translation {N : ℕ} (p z : Fin N → ℤ) (r : ℤ)
    (hp : ∀ i, 0 ≤ p i) (hz : feasible r z) :
    feasible ((∑ i, p i) + r) (fun i => p i + z i) := by
  constructor
  · intro i
    exact add_nonneg (hp i) (hz.1 i)
  · rw [Finset.sum_add_distrib]
    exact add_le_add_right hz.2 _

theorem minimum_translation_down {N : ℕ} (p : Fin N → ℤ) (y : Fin N → ℝ)
    (r : ℤ) (hp : ∀ i, 0 ≤ p i) (hy : ∀ i, 0 ≤ y i)
    (hs : ∑ i, y i = (r : ℝ)) (n : Fin N → ℤ)
    (hn : isMinimum ((∑ i, p i) + r) (fun i => (p i : ℝ) + y i) n) :
    isMinimum r y (fun i => n i - p i) := by
  have hs' : ∑ i, ((p i : ℝ) + y i) = ((∑ i, p i) + r : ℤ) := by
    rw [Finset.sum_add_distrib, hs]
    push_cast
    rfl
  have hcoord := coordinate_lower ((∑ i, p i) + r) (fun i => (p i : ℝ) + y i)
    (fun i => add_nonneg (by exact_mod_cast hp i) (hy i)) hs' n hn
  have hnge : ∀ i, p i ≤ n i := by
    intro i
    have hi := hcoord i
    rw [Int.floor_intCast_add] at hi
    have hf := Int.floor_nonneg.mpr (hy i)
    omega
  have hnloss : loss (fun i => (p i : ℝ) + y i) n = loss y (fun i => n i - p i) := by
    convert loss_translation p (fun i => n i - p i) y using 1
    congr 1
    funext i
    omega
  constructor
  · constructor
    · intro i
      dsimp
      have hi := hnge i
      omega
    · rw [Finset.sum_sub_distrib]
      have hncap := hn.1.2
      omega
  · intro z hz
    have hc := hn.2 _ (feasible_translation p z r hp hz)
    rw [hnloss, loss_translation] at hc
    exact hc

theorem minimum_translation_iff {N : ℕ} (p : Fin N → ℤ) (y : Fin N → ℝ)
    (r : ℤ) (hr : 0 ≤ r) (hp : ∀ i, 0 ≤ p i) (hy : ∀ i, 0 ≤ y i)
    (hs : ∑ i, y i = (r : ℝ)) (n : Fin N → ℤ) :
    isMinimum ((∑ i, p i) + r) (fun i => (p i : ℝ) + y i) n ↔
      ∃ z, n = (fun i => p i + z i) ∧ isMinimum r y z := by
  constructor
  · intro hn
    refine ⟨fun i => n i - p i, ?_, minimum_translation_down p y r hp hy hs n hn⟩
    funext i
    dsimp
    omega
  · rintro ⟨z, rfl, hz⟩
    refine ⟨feasible_translation p z r hp hz.1, ?_⟩
    intro w hw
    have hcap : 0 ≤ (∑ i, p i) + r := add_nonneg (Finset.sum_nonneg (fun i _ => hp i)) hr
    obtain ⟨v, hv⟩ := minimum_exists ((∑ i, p i) + r) hcap (fun i => (p i : ℝ) + y i)
    have hvdown := minimum_translation_down p y r hp hy hs v hv
    have hcompare := hz.2 _ hvdown.1
    have hvsum : (fun i => p i + (v i - p i)) = v := by
      funext i
      omega
    have he := loss_translation p (fun i => v i - p i) y
    rw [hvsum] at he
    rw [loss_translation]
    exact le_trans hcompare (by simpa only [← he] using hv.2 w hw)

theorem rational_residue_reduction {N : ℕ} (c : Fin N → ℤ) (D q r : ℤ)
    (hD : 0 < D) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hc : ∀ i, 0 ≤ c i) (hcs : ∑ i, c i = D) (n : Fin N → ℤ) :
    isMinimum (q * D + r) (fun i => ((q * D + r : ℤ) : ℝ) * (c i : ℝ) / D) n ↔
      ∃ z, n = (fun i => q * c i + z i) ∧
        isMinimum r (fun i => (r : ℝ) * (c i : ℝ) / D) z := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hcsreal : ∑ i, (c i : ℝ) = (D : ℝ) := by exact_mod_cast hcs
  have hy : ∀ i, 0 ≤ (r : ℝ) * (c i : ℝ) / D := by
    intro i
    exact div_nonneg (mul_nonneg (by exact_mod_cast hr) (by exact_mod_cast hc i)) hDreal.le
  have hsum : ∑ i, (r : ℝ) * (c i : ℝ) / D = (r : ℝ) := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hcsreal]
    field_simp
  have hpcap : ∑ i, q * c i = q * D := by
    rw [← Finset.mul_sum, hcs]
  have he : (fun i => ((q * c i : ℤ) : ℝ) + (r : ℝ) * (c i : ℝ) / D) =
      (fun i => ((q * D + r : ℤ) : ℝ) * (c i : ℝ) / D) := by
    funext i
    push_cast
    field_simp
  have h := minimum_translation_iff (fun i => q * c i)
    (fun i => (r : ℝ) * (c i : ℝ) / D) r hr (fun i => mul_nonneg hq (hc i)) hy hsum n
  simpa only [he, hpcap] using h

theorem rational_residue_slack {N : ℕ} (c z : Fin N → ℤ) (D q r : ℤ)
    (hcs : ∑ i, c i = D) :
    q * D + r - Finset.sum Finset.univ (fun i : Fin N => q * c i + z i) =
      r - Finset.sum Finset.univ z := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcs]
  ring

theorem scaled_loss_identity {N : ℕ} (M : ℝ) (hM : M ≠ 0)
    (a : Fin N → ℝ) (n : Fin N → ℤ) :
    M^2 * (∑ i, ((n i : ℝ) / M - a i)^2) = loss (fun i => M * a i) n := by
  rw [Finset.mul_sum]
  unfold loss
  apply Finset.sum_congr rfl
  intro i _
  field_simp

theorem rational_residue_loss {N : ℕ} (c z : Fin N → ℤ) (D q r : ℤ) (hD : D ≠ 0) :
    loss (fun i => ((q * D + r : ℤ) : ℝ) * (c i : ℝ) / D) (fun i => q * c i + z i) =
      loss (fun i => (r : ℝ) * (c i : ℝ) / D) z := by
  have hDreal : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have he : (fun i => ((q * c i : ℤ) : ℝ) + (r : ℝ) * (c i : ℝ) / D) =
      (fun i => ((q * D + r : ℤ) : ℝ) * (c i : ℝ) / D) := by
    funext i
    push_cast
    field_simp
  rw [← he]
  exact loss_translation (fun i => q * c i) z _


end RematGeneral

namespace RematSelection

noncomputable section

variable {N : ℕ}

def cost (c : Fin N → ℝ) (E : Finset (Fin N)) : ℝ := ∑ i ∈ E, c i

def negative (c : Fin N → ℝ) : Finset (Fin N) := Finset.univ.filter (fun i => c i < 0)

def zero (c : Fin N → ℝ) : Finset (Fin N) := Finset.univ.filter (fun i => c i = 0)

def minimum (c : Fin N → ℝ) (k : ℕ) (E : Finset (Fin N)) : Prop :=
  E.card ≤ k ∧ ∀ F : Finset (Fin N), F.card ≤ k → cost c E ≤ cost c F

theorem cost_terms (c : Fin N → ℝ) (E : Finset (Fin N)) :
    cost c E = ∑ i, if i ∈ E then c i else 0 := by
  classical
  simp [cost, Finset.sum_ite_mem]

theorem negative_lower (c : Fin N → ℝ) (E : Finset (Fin N)) :
    cost c (negative c) ≤ cost c E := by
  classical
  rw [cost_terms, cost_terms]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : c i < 0 <;> by_cases hE : i ∈ E <;> simp [negative, hi, hE] <;> linarith

theorem cost_eq_negative_iff (c : Fin N → ℝ) (E : Finset (Fin N)) :
    cost c E = cost c (negative c) ↔ negative c ⊆ E ∧ E ⊆ negative c ∪ zero c := by
  classical
  have hterm (i : Fin N) :
      (if i ∈ negative c then c i else 0) ≤ (if i ∈ E then c i else 0) := by
    by_cases hi : c i < 0 <;> by_cases hE : i ∈ E <;> simp [negative, hi, hE] <;> linarith
  constructor
  · intro h
    have hh : ∀ i ∈ (Finset.univ : Finset (Fin N)),
        (if i ∈ negative c then c i else 0) = (if i ∈ E then c i else 0) := by
      apply (Finset.sum_eq_sum_iff_of_le (fun i _ => hterm i)).mp
      simpa only [← cost_terms] using h.symm
    constructor
    · intro i hi
      have hc : c i < 0 := (Finset.mem_filter.mp hi).2
      have he := hh i (Finset.mem_univ i)
      by_contra hE
      simp [hi, hE] at he
      linarith
    · intro i hi
      have he := hh i (Finset.mem_univ i)
      by_cases hc : c i < 0
      · simp [negative, hc]
      · have hci : c i = 0 := by simpa [negative, hc, hi] using he.symm
        simp [zero, hci]
  · rintro ⟨hB, hU⟩
    rw [cost_terms, cost_terms]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ E
    · by_cases hb : i ∈ negative c
      · simp [hi, hb]
      · have hz : c i = 0 := (Finset.mem_filter.mp ((Finset.mem_union.mp (hU hi)).resolve_left hb)).2
        simp [hi, hb, hz]
    · have hb : i ∉ negative c := fun h => hi (hB h)
      simp [hi, hb]

theorem minimum_iff_when_negative_fits (c : Fin N → ℝ) (k : ℕ)
    (hk : (negative c).card ≤ k) (E : Finset (Fin N)) :
    minimum c k E ↔ E.card ≤ k ∧ negative c ⊆ E ∧ E ⊆ negative c ∪ zero c := by
  constructor
  · intro h
    refine ⟨h.1, (cost_eq_negative_iff c E).mp ?_⟩
    exact le_antisymm (h.2 _ hk) (negative_lower c E)
  · rintro ⟨hcard, hB, hU⟩
    refine ⟨hcard, fun F _ => ?_⟩
    rw [(cost_eq_negative_iff c E).mpr ⟨hB, hU⟩]
    exact negative_lower c F

theorem negative_minimum (c : Fin N → ℝ) (k : ℕ)
    (hk : (negative c).card ≤ k) : minimum c k (negative c) := by
  exact ⟨hk, fun F _ => negative_lower c F⟩

theorem saturated_when_many_negative (c : Fin N → ℝ) (k : ℕ)
    (hk : k ≤ (negative c).card) (E : Finset (Fin N)) (hE : minimum c k E) : E.card = k := by
  classical
  have hEcap := hE.1
  by_contra heq
  have hlt : E.card < k := by omega
  have hnot : ¬negative c ⊆ E := by
    intro h
    have hcard := Finset.card_le_card h
    omega
  obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hnot
  have hneg : c i < 0 := (Finset.mem_filter.mp hi).2
  have hcap : (insert i E).card ≤ k := by rw [Finset.card_insert_of_notMem hni];omega
  have hmin := hE.2 (insert i E) hcap
  simp [cost, Finset.sum_insert hni] at hmin
  linarith

theorem selected_before_unselected (c : Fin N → ℝ) (k : ℕ)
    (E : Finset (Fin N)) (hE : minimum c k E) (i j : Fin N)
    (hi : i ∈ E) (hj : j ∉ E) : c i ≤ c j := by
  classical
  have hEcap := hE.1
  have hje : j ∉ E.erase i := fun h => hj (Finset.mem_of_mem_erase h)
  have hcard := Finset.card_erase_add_one hi
  have hcap : (insert j (E.erase i)).card ≤ k := by
    rw [Finset.card_insert_of_notMem hje]
    omega
  have he := Finset.sum_erase_add E c hi
  have hmin := hE.2 (insert j (E.erase i)) hcap
  simp only [cost, Finset.sum_insert hje] at hmin
  linarith

theorem negative_zero_disjoint (c : Fin N → ℝ) : Disjoint (negative c) (zero c) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hz
  have hlt := (Finset.mem_filter.mp hi).2
  have heq := (Finset.mem_filter.mp hz).2
  linarith

theorem zero_subset_minimum (c : Fin N → ℝ) (k : ℕ) (S : Finset (Fin N))
    (hS : S ⊆ zero c) (hcap : (negative c).card + S.card ≤ k) :
    minimum c k (negative c ∪ S) := by
  classical
  have hdis : Disjoint (negative c) S := (negative_zero_disjoint c).mono_right hS
  have hb : (negative c).card ≤ k := by omega
  apply (minimum_iff_when_negative_fits c k hb _).mpr
  refine ⟨by simpa [Finset.card_union_of_disjoint hdis] using hcap, Finset.subset_union_left, ?_⟩
  exact Finset.union_subset_union_right hS

theorem minimum_cardinality_exists (c : Fin N → ℝ) (k s : ℕ)
    (hk : (negative c).card ≤ k) (hs : s ≤ min (zero c).card (k-(negative c).card)) :
    ∃ E, minimum c k E ∧ E.card = (negative c).card + s := by
  classical
  obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq (le_trans hs (min_le_left _ _))
  have hcap : (negative c).card + S.card ≤ k := by
    have ht := le_trans hs (min_le_right _ _)
    omega
  refine ⟨negative c ∪ S, zero_subset_minimum c k S hS hcap, ?_⟩
  rw [Finset.card_union_of_disjoint ((negative_zero_disjoint c).mono_right hS), hSc]

theorem minimum_cardinality_iff (c : Fin N → ℝ) (k m : ℕ)
    (hk : (negative c).card ≤ k) :
    (∃ E, minimum c k E ∧ E.card = m) ↔
      ∃ s : ℕ, s ≤ min (zero c).card (k-(negative c).card) ∧ m = (negative c).card + s := by
  classical
  constructor
  · rintro ⟨E, hE, rfl⟩
    obtain ⟨hcap,hB,hU⟩ := (minimum_iff_when_negative_fits c k hk E).mp hE
    refine ⟨(E \ negative c).card, ?_, ?_⟩
    · apply le_min
      · apply Finset.card_le_card
        intro i hi
        obtain ⟨hei,hni⟩ := Finset.mem_sdiff.mp hi
        exact (Finset.mem_union.mp (hU hei)).resolve_left hni
      · rw [Finset.card_sdiff_of_subset hB]
        omega
    · have h := Finset.card_sdiff_add_card_eq_card hB
      omega
  · rintro ⟨s,hs,rfl⟩
    exact minimum_cardinality_exists c k s hk hs

theorem some_slack_iff (c : Fin N → ℝ) (k : ℕ) :
    (∃ E, minimum c k E ∧ E.card < k) ↔ (negative c).card < k := by
  constructor
  · rintro ⟨E,hE,hslack⟩
    by_contra h
    have hsat := saturated_when_many_negative c k (by omega) E hE
    omega
  · intro hk
    exact ⟨negative c,negative_minimum c k hk.le,hk⟩

theorem minimum_exists (c : Fin N → ℝ) (k : ℕ) : ∃ E, minimum c k E := by
  classical
  let candidates := Finset.univ.filter (fun E : Finset (Fin N) => E.card ≤ k)
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨E,hE,hmin⟩ := candidates.exists_min_image (cost c) hne
  refine ⟨E,(Finset.mem_filter.mp hE).2, fun F hF => ?_⟩
  exact hmin F (by simp [candidates,hF])

theorem all_slack_iff (c : Fin N → ℝ) (k : ℕ) :
    (∀ E, minimum c k E → E.card < k) ↔ (negative c).card + (zero c).card < k := by
  classical
  constructor
  · intro h
    obtain ⟨E,hE⟩ := minimum_exists c k
    have hb : (negative c).card < k := (some_slack_iff c k).mp ⟨E,hE,h E hE⟩
    by_contra hnot
    have hs : k-(negative c).card ≤ min (zero c).card (k-(negative c).card) := by omega
    obtain ⟨F,hF,hFc⟩ := minimum_cardinality_exists c k (k-(negative c).card) hb.le hs
    have hc := h F hF
    omega
  · intro h E hE
    have hb : (negative c).card ≤ k := by omega
    have hU := ((minimum_iff_when_negative_fits c k hb E).mp hE).2.2
    have hc := Finset.card_le_card hU
    rw [Finset.card_union_of_disjoint (negative_zero_disjoint c)] at hc
    omega

theorem unique_minimum_with_slack_iff (c : Fin N → ℝ) (k : ℕ) :
    (∃ E, minimum c k E ∧ E.card < k ∧ ∀ F, minimum c k F → F = E) ↔
      (negative c).card < k ∧ (zero c).card = 0 := by
  classical
  constructor
  · rintro ⟨E,hE,hslack,huniq⟩
    have hb : (negative c).card < k := (some_slack_iff c k).mp ⟨E,hE,hslack⟩
    refine ⟨hb, ?_⟩
    have hBE := huniq (negative c) (negative_minimum c k hb.le)
    by_contra hz
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
    have hni : i ∉ negative c := fun h => (Finset.disjoint_left.mp (negative_zero_disjoint c)) h hi
    have hS : ({i} : Finset (Fin N)) ⊆ zero c := by simpa using hi
    have hcap : (negative c).card + ({i} : Finset (Fin N)).card ≤ k := by simp only [Finset.card_singleton];omega
    have hF := huniq (negative c ∪ {i}) (zero_subset_minimum c k {i} hS hcap)
    have heq : negative c ∪ {i} = negative c := hF.trans hBE.symm
    apply hni
    rw [← heq]
    simp
  · rintro ⟨hb,hz⟩
    refine ⟨negative c,negative_minimum c k hb.le,hb, ?_⟩
    intro F hF
    obtain ⟨_,hB,hU⟩ := (minimum_iff_when_negative_fits c k hb.le F).mp hF
    have hzero : zero c = ∅ := Finset.card_eq_zero.mp hz
    apply Finset.Subset.antisymm
    · simpa [hzero] using hU
    · exact hB

theorem cost_shift (c : Fin N → ℝ) (a : ℝ) (E : Finset (Fin N)) :
    cost (fun i => c i-a) E = cost c E - (E.card : ℝ)*a := by
  simp [cost,Finset.sum_sub_distrib]

theorem minimum_iff_when_many_negative (c : Fin N → ℝ) (k : ℕ)
    (hk : k ≤ (negative c).card) (E : Finset (Fin N)) :
    minimum c k E ↔ E.card = k ∧ ∀ i ∈ E, ∀ j ∉ E, c i ≤ c j := by
  classical
  constructor
  · intro h
    exact ⟨saturated_when_many_negative c k hk E h,
      fun i hi j hj => selected_before_unselected c k E h i j hi hj⟩
  · rintro ⟨hcard,horder⟩
    refine ⟨hcard.le,fun F hF => ?_⟩
    by_cases hne : E.Nonempty
    · obtain ⟨i,hi,hmax⟩ := E.exists_max_image c hne
      have hci : c i < 0 := by
        by_contra hnon
        have hB : negative c ⊆ E := by
          intro j hj
          by_contra hjE
          have ho := horder i hi j hjE
          have hn := (Finset.mem_filter.mp hj).2
          linarith
        have hBE : negative c = E := Finset.eq_of_subset_of_card_le hB (by omega)
        have hiB : i ∈ negative c := by rw [hBE];exact hi
        exact hnon (Finset.mem_filter.mp hiB).2
      have hB : negative (fun j => c j-c i) ⊆ E := by
        intro j hj
        by_contra hjE
        have ho := horder i hi j hjE
        have hn := (Finset.mem_filter.mp hj).2
        linarith
      have hU : E ⊆ negative (fun j => c j-c i) ∪ zero (fun j => c j-c i) := by
        intro j hj
        have hle := hmax j hj
        by_cases heq : c j = c i
        · simp [zero,heq]
        · have hlt : c j < c i := (lt_or_eq_of_le hle).resolve_right heq
          simp [negative,hlt]
      have hcost : cost (fun j => c j-c i) E ≤ cost (fun j => c j-c i) F := by
        rw [(cost_eq_negative_iff _ E).mpr ⟨hB,hU⟩]
        exact negative_lower _ F
      rw [cost_shift,cost_shift] at hcost
      have hcardR : (F.card : ℝ) ≤ (E.card : ℝ) := by exact_mod_cast (show F.card ≤ E.card by omega)
      nlinarith
    · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hf : F = ∅ := Finset.card_eq_zero.mp (by simp [he] at hcard;omega)
      simp [he,hf]


end

end RematSelection

namespace RematRounding

noncomputable section

open scoped BigOperators

variable {N : ℕ}

def base (y : Fin N → ℝ) (i : Fin N) : ℤ := ⌊y i⌋

def fraction (y : Fin N → ℝ) (i : Fin N) : ℝ := y i - (base y i : ℝ)

def benefit (y : Fin N → ℝ) (i : Fin N) : ℝ := 1 - 2 * fraction y i

def capacity (M : ℤ) (y : Fin N → ℝ) : ℕ := (M - ∑ i, base y i).toNat

def rounded (y : Fin N → ℝ) (E : Finset (Fin N)) (i : Fin N) : ℤ :=
  base y i + if i ∈ E then 1 else 0

def selected (y : Fin N → ℝ) (n : Fin N → ℤ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => base y i < n i)

theorem fraction_bounds (y : Fin N → ℝ) (i : Fin N) :
    0 ≤ fraction y i ∧ fraction y i < 1 := by
  change 0 ≤ Int.fract (y i) ∧ Int.fract (y i) < 1
  exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩

theorem capacity_cast (M : ℤ) (y : Fin N → ℝ) (hs : ∑ i, y i = (M : ℝ)) :
    (capacity M y : ℤ) = M - ∑ i, base y i := by
  have hle : ∑ i, (base y i : ℝ) ≤ (M : ℝ) := by
    rw [← hs]
    exact Finset.sum_le_sum (fun i _ => Int.floor_le (y i))
  have hleInt : ∑ i, base y i ≤ M := by exact_mod_cast hle
  exact Int.toNat_of_nonneg (by omega)

theorem fraction_sum (M : ℤ) (y : Fin N → ℝ) (hs : ∑ i, y i = (M : ℝ)) :
    ∑ i, fraction y i = (capacity M y : ℝ) := by
  simp only [fraction,Finset.sum_sub_distrib,hs]
  have h := capacity_cast M y hs
  exact_mod_cast h.symm

theorem rounded_sum (y : Fin N → ℝ) (E : Finset (Fin N)) :
    ∑ i, rounded y E i = (∑ i, base y i) + (E.card : ℤ) := by
  classical
  simp [rounded,Finset.sum_add_distrib,Finset.sum_ite_mem]

theorem rounded_slack (M : ℤ) (y : Fin N → ℝ) (hs : ∑ i, y i = (M : ℝ))
    (E : Finset (Fin N)) :
    M - ∑ i, rounded y E i = (capacity M y : ℤ) - (E.card : ℤ) := by
  rw [rounded_sum,capacity_cast M y hs]
  ring

theorem rounded_loss (y : Fin N → ℝ) (E : Finset (Fin N)) :
    RematGeneral.loss y (rounded y E) =
      RematGeneral.loss y (base y) + RematSelection.cost (benefit y) E := by
  classical
  rw [RematSelection.cost_terms]
  unfold RematGeneral.loss
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ E <;> simp [rounded,benefit,fraction,hi] <;> ring

theorem base_loss (y : Fin N → ℝ) : RematGeneral.loss y (base y) = ∑ i, (fraction y i)^2 := by
  unfold RematGeneral.loss fraction
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rounded_feasible_iff (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) (E : Finset (Fin N)) :
    RematGeneral.feasible M (rounded y E) ↔ E.card ≤ capacity M y := by
  classical
  have hcap := capacity_cast M y hs
  constructor
  · intro h
    have hsum := h.2
    rw [rounded_sum] at hsum
    exact_mod_cast (show (E.card : ℤ) ≤ (capacity M y : ℤ) by omega)
  · intro h
    constructor
    · intro i
      have hp : 0 ≤ base y i := Int.floor_nonneg.mpr (hy i)
      dsimp [rounded]
      split_ifs <;> omega
    · rw [rounded_sum]
      have hh : (E.card : ℤ) ≤ (capacity M y : ℤ) := by exact_mod_cast h
      omega

theorem rounded_injective (y : Fin N → ℝ) : Function.Injective (rounded y) := by
  classical
  intro E F heq
  apply Finset.ext
  intro i
  have hi := congrFun heq i
  by_cases he : i ∈ E <;> by_cases hf : i ∈ F <;> simp [rounded,he,hf] at hi ⊢

theorem minimum_rounded_representation (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (n : Fin N → ℤ) (hn : RematGeneral.isMinimum M y n) :
    n = rounded y (selected y n) := by
  classical
  funext i
  obtain ⟨hlo,hhi⟩ := RematGeneral.coordinate_proximity M y hy hs n hn i
  have hceil := Int.ceil_le_floor_add_one (y i)
  by_cases h : base y i < n i
  · simp [rounded,selected,h]
    dsimp [base] at h ⊢
    omega
  · simp [rounded,selected,h]
    dsimp [base] at h ⊢
    omega

theorem rounded_minimum_iff (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) (E : Finset (Fin N)) :
    RematGeneral.isMinimum M y (rounded y E) ↔
      RematSelection.minimum (benefit y) (capacity M y) E := by
  constructor
  · intro h
    refine ⟨(rounded_feasible_iff M y hy hs E).mp h.1, ?_⟩
    intro F hF
    have hcomp := h.2 (rounded y F) ((rounded_feasible_iff M y hy hs F).mpr hF)
    rw [rounded_loss,rounded_loss] at hcomp
    linarith
  · intro h
    refine ⟨(rounded_feasible_iff M y hy hs E).mpr h.1, ?_⟩
    intro z hz
    have hM : 0 ≤ M := by
      have hh : (0 : ℝ) ≤ M := by rw [← hs];exact Finset.sum_nonneg (fun i _ => hy i)
      exact_mod_cast hh
    obtain ⟨v,hv⟩ := RematGeneral.minimum_exists M hM y
    have hrep := minimum_rounded_representation M y hy hs v hv
    have hvfeas : RematGeneral.feasible M (rounded y (selected y v)) := by rw [← hrep];exact hv.1
    have hcomp := h.2 (selected y v) ((rounded_feasible_iff M y hy hs _).mp hvfeas)
    have hmin := hv.2 z hz
    rw [hrep,rounded_loss] at hmin
    rw [rounded_loss]
    linarith

theorem all_integer_minima_iff (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) (n : Fin N → ℤ) :
    RematGeneral.isMinimum M y n ↔
      ∃ E, n = rounded y E ∧ RematSelection.minimum (benefit y) (capacity M y) E := by
  constructor
  · intro h
    have hrep := minimum_rounded_representation M y hy hs n h
    refine ⟨selected y n,hrep, ?_⟩
    apply (rounded_minimum_iff M y hy hs _).mp
    rwa [← hrep]
  · rintro ⟨E,rfl,hE⟩
    exact (rounded_minimum_iff M y hy hs E).mpr hE

theorem negative_is_above_half (y : Fin N → ℝ) :
    RematSelection.negative (benefit y) = Finset.univ.filter (fun i => (1 : ℝ)/2 < fraction y i) := by
  classical
  ext i
  simp only [RematSelection.negative,Finset.mem_filter,Finset.mem_univ,true_and,benefit]
  constructor <;> intro h <;> linarith

theorem zero_is_half (y : Fin N → ℝ) :
    RematSelection.zero (benefit y) = Finset.univ.filter (fun i => fraction y i = (1 : ℝ)/2) := by
  classical
  ext i
  simp only [RematSelection.zero,Finset.mem_filter,Finset.mem_univ,true_and,benefit]
  constructor <;> intro h <;> linarith

def highCount (y : Fin N → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => (1 : ℝ)/2 < fraction y i)).card

def tieCount (y : Fin N → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => fraction y i = (1 : ℝ)/2)).card

theorem highCount_eq_negative (y : Fin N → ℝ) :
    highCount y = (RematSelection.negative (benefit y)).card := by
  rw [negative_is_above_half]
  rfl

theorem tieCount_eq_zero (y : Fin N → ℝ) :
    tieCount y = (RematSelection.zero (benefit y)).card := by
  rw [zero_is_half]
  rfl

theorem positive_slack_iff (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) :
    (∃ n, RematGeneral.isMinimum M y n ∧ 0 < M-∑ i, n i) ↔
      highCount y < capacity M y := by
  rw [highCount_eq_negative]
  constructor
  · rintro ⟨n,hn,hslack⟩
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff M y hy hs n).mp hn
    rw [rounded_slack M y hs] at hslack
    apply (RematSelection.some_slack_iff _ _).mp
    refine ⟨E,hE, ?_⟩
    omega
  · intro h
    obtain ⟨E,hE,hslack⟩ := (RematSelection.some_slack_iff _ _).mpr h
    refine ⟨rounded y E,(rounded_minimum_iff M y hy hs E).mpr hE, ?_⟩
    rw [rounded_slack M y hs]
    omega

theorem all_positive_slack_iff (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) :
    (∀ n, RematGeneral.isMinimum M y n → 0 < M-∑ i, n i) ↔
      highCount y + tieCount y < capacity M y := by
  rw [highCount_eq_negative,tieCount_eq_zero]
  constructor
  · intro h
    apply (RematSelection.all_slack_iff _ _).mp
    intro E hE
    have hslack := h (rounded y E) ((rounded_minimum_iff M y hy hs E).mpr hE)
    rw [rounded_slack M y hs] at hslack
    omega
  · intro h n hn
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff M y hy hs n).mp hn
    have hslack := (RematSelection.all_slack_iff _ _).mpr h E hE
    rw [rounded_slack M y hs]
    omega

theorem unique_global_minimum_with_slack_iff (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) :
    (∃ n, RematGeneral.isMinimum M y n ∧ 0 < M-∑ i, n i ∧
      ∀ z, RematGeneral.isMinimum M y z → z = n) ↔
      highCount y < capacity M y ∧ tieCount y = 0 := by
  rw [highCount_eq_negative,tieCount_eq_zero]
  constructor
  · rintro ⟨n,hn,hslack,huniq⟩
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff M y hy hs n).mp hn
    rw [rounded_slack M y hs] at hslack
    apply (RematSelection.unique_minimum_with_slack_iff _ _).mp
    refine ⟨E,hE,by omega, ?_⟩
    intro F hF
    apply rounded_injective y
    exact huniq (rounded y F) ((rounded_minimum_iff M y hy hs F).mpr hF)
  · intro h
    obtain ⟨E,hE,hslack,huniq⟩ := (RematSelection.unique_minimum_with_slack_iff _ _).mpr h
    refine ⟨rounded y E,(rounded_minimum_iff M y hy hs E).mpr hE, ?_, ?_⟩
    · rw [rounded_slack M y hs]
      omega
    · intro z hz
      obtain ⟨F,rfl,hF⟩ := (all_integer_minima_iff M y hy hs z).mp hz
      exact congrArg (rounded y) (huniq F hF)

theorem exact_slack_image (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (hb : highCount y < capacity M y) (ell : ℤ) :
    (∃ n, RematGeneral.isMinimum M y n ∧ M-∑ i, n i = ell) ↔
      ∃ s : ℤ, 0 ≤ s ∧ s ≤ min (tieCount y : ℤ) ((capacity M y : ℤ)-(highCount y : ℤ)) ∧
        ell = (capacity M y : ℤ)-(highCount y : ℤ)-s := by
  rw [highCount_eq_negative] at hb
  rw [highCount_eq_negative,tieCount_eq_zero]
  constructor
  · rintro ⟨n,hn,hell⟩
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff M y hy hs n).mp hn
    obtain ⟨s,hsize,hcard⟩ :=
      (RematSelection.minimum_cardinality_iff (benefit y) (capacity M y) E.card hb.le).mp ⟨E,hE,rfl⟩
    have ht := le_trans hsize (min_le_left _ _)
    have hk := le_trans hsize (min_le_right _ _)
    rw [rounded_slack M y hs] at hell
    refine ⟨(s : ℤ), by omega, ?_, ?_⟩
    · apply le_min <;> omega
    · omega
  · rintro ⟨s,hs0,hsize,hell⟩
    have hsn : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs0
    have ht := le_trans hsize (min_le_left _ _)
    have hk := le_trans hsize (min_le_right _ _)
    have hsizeN : s.toNat ≤ min (RematSelection.zero (benefit y)).card
        (capacity M y-(RematSelection.negative (benefit y)).card) := by
      apply le_min <;> omega
    obtain ⟨E,hE,hcard⟩ := RematSelection.minimum_cardinality_exists
      (benefit y) (capacity M y) s.toNat hb.le hsizeN
    refine ⟨rounded y E,(rounded_minimum_iff M y hy hs E).mpr hE, ?_⟩
    rw [rounded_slack M y hs]
    omega

theorem saturated_classification (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (hb : capacity M y ≤ highCount y) (n : Fin N → ℤ) :
    RematGeneral.isMinimum M y n ↔ ∃ E, n = rounded y E ∧ E.card = capacity M y ∧
      ∀ i ∈ E, ∀ j ∉ E, fraction y j ≤ fraction y i := by
  rw [highCount_eq_negative] at hb
  rw [all_integer_minima_iff M y hy hs n]
  constructor
  · rintro ⟨E,hn,hE⟩
    obtain ⟨hc,ho⟩ := (RematSelection.minimum_iff_when_many_negative _ _ hb E).mp hE
    refine ⟨E,hn,hc, ?_⟩
    intro i hi j hj
    have h := ho i hi j hj
    dsimp [benefit] at h
    linarith
  · rintro ⟨E,hn,hc,ho⟩
    refine ⟨E,hn,(RematSelection.minimum_iff_when_many_negative _ _ hb E).mpr ⟨hc, ?_⟩⟩
    intro i hi j hj
    have h := ho i hi j hj
    dsimp [benefit]
    linarith

theorem unsaturated_classification (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (hb : highCount y < capacity M y) (n : Fin N → ℤ) :
    RematGeneral.isMinimum M y n ↔ ∃ E, n = rounded y E ∧ E.card ≤ capacity M y ∧
      (Finset.univ.filter (fun i => (1 : ℝ)/2 < fraction y i)) ⊆ E ∧
      E ⊆ (Finset.univ.filter (fun i => (1 : ℝ)/2 < fraction y i)) ∪
        (Finset.univ.filter (fun i => fraction y i = (1 : ℝ)/2)) := by
  rw [highCount_eq_negative] at hb
  rw [all_integer_minima_iff M y hy hs n]
  simp_rw [RematSelection.minimum_iff_when_negative_fits _ _ hb.le,
    negative_is_above_half,zero_is_half]


end

end RematRounding

namespace RematGrid

open Finset

noncomputable def point {N : ℕ} (M : ℤ) (n : Fin N → ℤ) : Fin N → ℝ :=
  fun i => (n i : ℝ) / M

def feasible {N : ℕ} (M : ℤ) (d : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ d i) ∧ ∑ i, d i ≤ 1 ∧ ∃ n, d = point M n

def loss {N : ℕ} (a d : Fin N → ℝ) : ℝ := ∑ i, (d i - a i)^2

def isMinimum {N : ℕ} (M : ℤ) (a d : Fin N → ℝ) : Prop :=
  feasible M d ∧ ∀ e, feasible M e → loss a d ≤ loss a e

theorem point_sum {N : ℕ} (M : ℤ) (n : Fin N → ℤ) :
    ∑ i, point M n i = ((∑ i, n i : ℤ) : ℝ) / M := by
  simp only [point, div_eq_mul_inv, ← Finset.sum_mul, Int.cast_sum]

theorem point_injective {N : ℕ} (M : ℤ) (hM : 0 < M) :
    Function.Injective (point (N := N) M) := by
  intro n z h
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  funext i
  have hi := congrFun h i
  have hni : (n i : ℝ) = z i := (div_left_inj' hm).mp hi
  exact_mod_cast hni

theorem point_feasible_iff {N : ℕ} (M : ℤ) (hM : 0 < M) (n : Fin N → ℤ) :
    feasible M (point M n) ↔ RematGeneral.feasible M n := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  constructor
  · rintro ⟨hn, hs, _⟩
    constructor
    · intro i
      have hi : (0 : ℝ) ≤ n i := by
        simpa only [zero_mul] using (le_div_iff₀ hm).mp (hn i)
      exact_mod_cast hi
    · rw [point_sum] at hs
      have hi : ((∑ i, n i : ℤ) : ℝ) ≤ M := by
        have := (div_le_iff₀ hm).mp hs
        simpa only [one_mul] using this
      exact_mod_cast hi
  · rintro ⟨hn, hs⟩
    refine ⟨?_, ?_, n, rfl⟩
    · intro i
      exact div_nonneg (by exact_mod_cast hn i) hm.le
    · rw [point_sum]
      apply (div_le_iff₀ hm).mpr
      simpa only [one_mul] using (show ((∑ i, n i : ℤ) : ℝ) ≤ M by exact_mod_cast hs)

theorem loss_scaling {N : ℕ} (M : ℤ) (hM : 0 < M) (a : Fin N → ℝ) (n : Fin N → ℤ) :
    (M : ℝ)^2 * loss a (point M n) = RematGeneral.loss (fun i => (M : ℝ) * a i) n := by
  exact RematGeneral.scaled_loss_identity M (by exact_mod_cast ne_of_gt hM) a n

theorem minimum_point_iff {N : ℕ} (M : ℤ) (hM : 0 < M)
    (a : Fin N → ℝ) (n : Fin N → ℤ) :
    isMinimum M a (point M n) ↔ RematGeneral.isMinimum M (fun i => (M : ℝ) * a i) n := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hp : (0 : ℝ) < (M : ℝ)^2 := sq_pos_of_pos hm
  constructor
  · rintro ⟨hf, ho⟩
    refine ⟨(point_feasible_iff M hM n).mp hf, ?_⟩
    intro z hz
    rw [← loss_scaling M hM a n, ← loss_scaling M hM a z]
    exact mul_le_mul_of_nonneg_left (ho (point M z) ((point_feasible_iff M hM z).mpr hz)) hp.le
  · rintro ⟨hf, ho⟩
    refine ⟨(point_feasible_iff M hM n).mpr hf, ?_⟩
    intro e he
    obtain ⟨z, rfl⟩ := he.2.2
    have hi := ho z ((point_feasible_iff M hM z).mp he)
    rw [← loss_scaling M hM a n, ← loss_scaling M hM a z] at hi
    exact le_of_mul_le_mul_left hi hp

theorem minimum_iff_exists_integer {N : ℕ} (M : ℤ) (hM : 0 < M)
    (a d : Fin N → ℝ) :
    isMinimum M a d ↔ ∃ n, d = point M n ∧
      RematGeneral.isMinimum M (fun i => (M : ℝ) * a i) n := by
  constructor
  · intro h
    obtain ⟨n, hd⟩ := h.1.2.2
    refine ⟨n, hd, ?_⟩
    rw [hd] at h
    exact (minimum_point_iff M hM a n).mp h
  · rintro ⟨n, rfl, hn⟩
    exact (minimum_point_iff M hM a n).mpr hn

theorem slack_identity {N : ℕ} (M : ℤ) (hM : 0 < M) (n : Fin N → ℤ) :
    1 - ∑ i, point M n i = ((M - ∑ i, n i : ℤ) : ℝ) / M := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  rw [point_sum]
  push_cast
  field_simp

theorem slack_positive_iff {N : ℕ} (M : ℤ) (hM : 0 < M) (n : Fin N → ℤ) :
    0 < 1 - ∑ i, point M n i ↔ 0 < M - ∑ i, n i := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  rw [slack_identity M hM n, div_pos_iff_of_pos_right hm]
  exact_mod_cast (Iff.rfl : 0 < M - ∑ i, n i ↔ 0 < M - ∑ i, n i)

theorem scaled_target_hypotheses {N : ℕ} (M : ℤ) (hM : 0 < M)
    (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1) :
    (∀ i, 0 ≤ (M : ℝ) * a i) ∧ ∑ i, (M : ℝ) * a i = (M : ℝ) := by
  constructor
  · intro i
    exact mul_nonneg (by exact_mod_cast hM.le) (ha i)
  · rw [← Finset.mul_sum, hs, mul_one]


end RematGrid

namespace RematPenalty

open Finset

variable {N : ℕ}

def loss (lam : ℝ) (M : ℤ) (y : Fin N → ℝ) (n : Fin N → ℤ) : ℝ :=
  RematGeneral.loss y n + lam * ((M - ∑ i, n i : ℤ) : ℝ)^2

def isMinimum (lam : ℝ) (M : ℤ) (y : Fin N → ℝ) (n : Fin N → ℤ) : Prop :=
  RematGeneral.feasible M n ∧ ∀ z, RematGeneral.feasible M z → loss lam M y n ≤ loss lam M y z

theorem minimum_exists (lam : ℝ) (M : ℤ) (hM : 0 ≤ M) (y : Fin N → ℝ) :
    ∃ n, isMinimum lam M y n := by
  classical
  let candidates := (Fintype.piFinset (fun _ : Fin N => Finset.Icc (0 : ℤ) M)).filter
    (fun n => ∑ i, n i ≤ M)
  have mem_iff (n : Fin N → ℤ) : n ∈ candidates ↔ RematGeneral.feasible M n := by
    simp only [candidates, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc,
      RematGeneral.feasible]
    constructor
    · intro h
      exact ⟨fun i => (h.1 i).1, h.2⟩
    · intro h
      refine ⟨?_, h.2⟩
      intro i
      exact ⟨h.1 i, (Finset.single_le_sum (fun j _ => h.1 j) (Finset.mem_univ i)).trans h.2⟩
  have hne : candidates.Nonempty := by
    refine ⟨fun _ => 0, (mem_iff _).mpr ⟨fun _ => le_refl _, ?_⟩⟩
    simpa using hM
  obtain ⟨n, hn, hmin⟩ := candidates.exists_min_image (loss lam M y) hne
  exact ⟨n, (mem_iff n).mp hn, fun z hz => hmin z ((mem_iff z).mpr hz)⟩

theorem coordinate_lower (lam : ℝ) (hlam : 0 ≤ lam) (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (n : Fin N → ℤ) (hn : isMinimum lam M y n) (i : Fin N) : ⌊y i⌋ ≤ n i := by
  by_contra hi
  have hni : n i < ⌊y i⌋ := by omega
  have hyi : (n i : ℝ) + 1 ≤ y i := Int.lt_floor_iff.mp hni
  by_cases hslack : ∑ j, n j < M
  · have hz : RematGeneral.feasible M (Function.update n i (n i + 1)) := by
      constructor
      · intro j
        by_cases hji : j = i
        · subst j
          simpa using add_nonneg (hn.1.1 i) (show (0 : ℤ) ≤ 1 by omega)
        · simpa [Function.update_of_ne hji] using hn.1.1 j
      · rw [RematGeneral.sum_update]
        omega
    have hmin := hn.2 _ hz
    unfold loss at hmin
    rw [RematGeneral.loss_update, RematGeneral.sum_update] at hmin
    have hs1 : (1 : ℝ) ≤ ((M - ∑ j, n j : ℤ) : ℝ) := by exact_mod_cast (show 1 ≤ M - ∑ j, n j by omega)
    have hp : 0 ≤ lam * (2 * ((M - ∑ j, n j : ℤ) : ℝ) - 1) := mul_nonneg hlam (by linarith)
    push_cast at hmin hs1 hp
    nlinarith
  · have heq : ∑ j, n j = M := le_antisymm hn.1.2 (by omega)
    have heqreal : ∑ j, (n j : ℝ) = (M : ℝ) := by exact_mod_cast heq
    have hex : ∃ j, y j < (n j : ℝ) := by
      by_contra h
      push Not at h
      have hlt : ∑ j, (n j : ℝ) < ∑ j, y j := by
        apply Finset.sum_lt_sum
        · intro j _
          exact h j
        · exact ⟨i, Finset.mem_univ i, by linarith⟩
      linarith
    obtain ⟨j, hj⟩ := hex
    have hji : j ≠ i := by intro h; subst j; linarith
    have hjpos : 0 < n j := by exact_mod_cast lt_of_le_of_lt (hy j) hj
    let z := Function.update (Function.update n j (n j - 1)) i (n i + 1)
    have hzsum : ∑ k, z k = ∑ k, n k := by
      dsimp [z]
      rw [RematGeneral.sum_update, RematGeneral.sum_update]
      simp only [Function.update_of_ne (Ne.symm hji)]
      omega
    have hz : RematGeneral.feasible M z := by
      constructor
      · intro k
        by_cases hki : k = i
        · subst k
          simp [z]
          have := hn.1.1 i
          omega
        · by_cases hkj : k = j
          · subst k
            simp [z, Function.update_of_ne hji]
            omega
          · simpa [z, Function.update_of_ne hki, Function.update_of_ne hkj] using hn.1.1 k
      · rw [hzsum]
        exact hn.1.2
    have hmin := hn.2 z hz
    unfold loss at hmin
    rw [hzsum] at hmin
    dsimp [z] at hmin
    rw [RematGeneral.loss_update, RematGeneral.loss_update] at hmin
    simp only [Function.update_of_ne (Ne.symm hji)] at hmin
    push_cast at hmin
    nlinarith

theorem coordinate_upper (lam : ℝ) (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (n : Fin N → ℤ) (hn : isMinimum lam M y n) (i : Fin N) : n i ≤ ⌈y i⌉ := by
  by_contra hi
  have hni : ⌈y i⌉ < n i := by omega
  have hyi : y i ≤ (n i : ℝ) - 1 := Int.ceil_lt_iff.mp hni
  have hipos : 0 < n i := by
    have hr : (0 : ℝ) < n i := by linarith [hy i]
    exact_mod_cast hr
  have hncap : ∑ j, (n j : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn.1.2
  have hex : ∃ j, (n j : ℝ) < y j := by
    by_contra h
    push Not at h
    have hlt : ∑ j, y j < ∑ j, (n j : ℝ) := by
      apply Finset.sum_lt_sum
      · intro j _
        exact h j
      · exact ⟨i, Finset.mem_univ i, by linarith⟩
    linarith
  obtain ⟨j, hj⟩ := hex
  have hji : j ≠ i := by intro h; subst j; linarith
  let z := Function.update (Function.update n i (n i - 1)) j (n j + 1)
  have hzsum : ∑ k, z k = ∑ k, n k := by
    dsimp [z]
    rw [RematGeneral.sum_update, RematGeneral.sum_update]
    simp only [Function.update_of_ne hji]
    omega
  have hz : RematGeneral.feasible M z := by
    constructor
    · intro k
      by_cases hkj : k = j
      · subst k
        simp [z]
        have := hn.1.1 j
        omega
      · by_cases hki : k = i
        · subst k
          simp [z, Function.update_of_ne (Ne.symm hji)]
          omega
        · simpa [z, Function.update_of_ne hki, Function.update_of_ne hkj] using hn.1.1 k
    · rw [hzsum]
      exact hn.1.2
  have hmin := hn.2 z hz
  unfold loss at hmin
  rw [hzsum] at hmin
  dsimp [z] at hmin
  rw [RematGeneral.loss_update, RematGeneral.loss_update] at hmin
  simp only [Function.update_of_ne hji] at hmin
  push_cast at hmin
  nlinarith

theorem coordinate_proximity (lam : ℝ) (hlam : 0 ≤ lam) (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (n : Fin N → ℤ) (hn : isMinimum lam M y n) :
    ∀ i, ⌊y i⌋ ≤ n i ∧ n i ≤ ⌈y i⌉ := by
  intro i
  exact ⟨coordinate_lower lam hlam M y hy hs n hn i, coordinate_upper lam M y hy hs n hn i⟩

end RematPenalty

namespace RematPenalty

open Finset

variable {N : ℕ}

theorem loss_translation (lam : ℝ) (p z : Fin N → ℤ) (r : ℤ) (y : Fin N → ℝ) :
    loss lam ((∑ i, p i) + r) (fun i => (p i : ℝ) + y i) (fun i => p i + z i) =
      loss lam r y z := by
  unfold loss
  rw [RematGeneral.loss_translation, Finset.sum_add_distrib]
  have he : (∑ i,p i)+r-((∑ i,p i)+(∑ i,z i)) = r-∑ i,z i := by ring
  rw [he]

theorem minimum_translation_down (lam : ℝ) (hlam : 0 ≤ lam)
    (p : Fin N → ℤ) (y : Fin N → ℝ) (r : ℤ)
    (hp : ∀ i, 0 ≤ p i) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (r : ℝ))
    (n : Fin N → ℤ)
    (hn : isMinimum lam ((∑ i, p i) + r) (fun i => (p i : ℝ) + y i) n) :
    isMinimum lam r y (fun i => n i - p i) := by
  have hs' : ∑ i, ((p i : ℝ) + y i) = ((∑ i, p i) + r : ℤ) := by
    rw [Finset.sum_add_distrib, hs]
    push_cast
    rfl
  have hcoord := coordinate_lower lam hlam ((∑ i, p i) + r) (fun i => (p i : ℝ) + y i)
    (fun i => add_nonneg (by exact_mod_cast hp i) (hy i)) hs' n hn
  have hnge : ∀ i, p i ≤ n i := by
    intro i
    have hi := hcoord i
    rw [Int.floor_intCast_add] at hi
    have hf := Int.floor_nonneg.mpr (hy i)
    omega
  have hnloss : loss lam ((∑ i, p i) + r) (fun i => (p i : ℝ) + y i) n =
      loss lam r y (fun i => n i - p i) := by
    convert loss_translation lam p (fun i => n i - p i) r y using 1
    congr 1
    funext i
    omega
  constructor
  · constructor
    · intro i
      have := hnge i
      dsimp
      omega
    · rw [Finset.sum_sub_distrib]
      have := hn.1.2
      omega
  · intro z hz
    have hc := hn.2 _ (RematGeneral.feasible_translation p z r hp hz)
    rw [hnloss, loss_translation] at hc
    exact hc

theorem minimum_translation_iff (lam : ℝ) (hlam : 0 ≤ lam)
    (p : Fin N → ℤ) (y : Fin N → ℝ) (r : ℤ)
    (hr : 0 ≤ r) (hp : ∀ i, 0 ≤ p i) (hy : ∀ i, 0 ≤ y i)
    (hs : ∑ i, y i = (r : ℝ)) (n : Fin N → ℤ) :
    isMinimum lam ((∑ i, p i) + r) (fun i => (p i : ℝ) + y i) n ↔
      ∃ z, n = (fun i => p i + z i) ∧ isMinimum lam r y z := by
  constructor
  · intro hn
    refine ⟨fun i => n i - p i, ?_, minimum_translation_down lam hlam p y r hp hy hs n hn⟩
    funext i
    dsimp
    omega
  · rintro ⟨z, rfl, hz⟩
    refine ⟨RematGeneral.feasible_translation p z r hp hz.1, ?_⟩
    intro w hw
    have hcap : 0 ≤ (∑ i, p i) + r := add_nonneg (Finset.sum_nonneg (fun i _ => hp i)) hr
    obtain ⟨v, hv⟩ := minimum_exists lam ((∑ i, p i) + r) hcap (fun i => (p i : ℝ) + y i)
    have hvdown := minimum_translation_down lam hlam p y r hp hy hs v hv
    have hcompare := hz.2 _ hvdown.1
    have hvsum : (fun i => p i + (v i - p i)) = v := by funext i; omega
    have he := loss_translation lam p (fun i => v i - p i) r y
    rw [hvsum] at he
    rw [loss_translation]
    exact le_trans hcompare (by simpa only [← he] using hv.2 w hw)

theorem rational_residue_reduction (lam : ℝ) (hlam : 0 ≤ lam)
    (c : Fin N → ℤ) (D q r : ℤ) (hD : 0 < D) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hc : ∀ i, 0 ≤ c i) (hcs : ∑ i, c i = D) (n : Fin N → ℤ) :
    isMinimum lam (q * D + r) (fun i => ((q * D + r : ℤ) : ℝ) * (c i : ℝ) / D) n ↔
      ∃ z, n = (fun i => q * c i + z i) ∧
        isMinimum lam r (fun i => (r : ℝ) * (c i : ℝ) / D) z := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hcsreal : ∑ i, (c i : ℝ) = (D : ℝ) := by exact_mod_cast hcs
  have hy : ∀ i, 0 ≤ (r : ℝ) * (c i : ℝ) / D := by
    intro i
    exact div_nonneg (mul_nonneg (by exact_mod_cast hr) (by exact_mod_cast hc i)) hDreal.le
  have hsum : ∑ i, (r : ℝ) * (c i : ℝ) / D = (r : ℝ) := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hcsreal]
    field_simp
  have hpcap : ∑ i, q * c i = q * D := by rw [← Finset.mul_sum, hcs]
  have he : (fun i => ((q * c i : ℤ) : ℝ) + (r : ℝ) * (c i : ℝ) / D) =
      (fun i => ((q * D + r : ℤ) : ℝ) * (c i : ℝ) / D) := by
    funext i
    push_cast
    field_simp
  have h := minimum_translation_iff lam hlam (fun i => q * c i)
    (fun i => (r : ℝ) * (c i : ℝ) / D) r hr (fun i => mul_nonneg hq (hc i)) hy hsum n
  simpa only [he, hpcap] using h


end RematPenalty

namespace RematProbability

open Finset

variable {N : ℕ}

def solid (d : Fin N → ℝ) : Prop := (∀ i, 0 ≤ d i) ∧ ∑ i, d i ≤ 1

def simplex (p : Fin (N + 1) → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

noncomputable def embed (d : Fin N → ℝ) : Fin (N + 1) → ℝ :=
  Fin.snoc d (1 - ∑ i, d i)

noncomputable def support (p : Fin (N + 1) → ℝ) : Set (Fin (N + 1)) := {i | p i ≠ 0}

theorem embed_lexical (d : Fin N → ℝ) (i : Fin N) : embed d i.castSucc = d i := by
  simp [embed]

theorem embed_residual (d : Fin N → ℝ) : embed d (Fin.last N) = 1 - ∑ i, d i := by
  simp [embed]

theorem embed_simplex_iff (d : Fin N → ℝ) : simplex (embed d) ↔ solid d := by
  constructor
  · rintro ⟨hn, hs⟩
    constructor
    · intro i
      simpa [embed] using hn i.castSucc
    · have h := hn (Fin.last N)
      simp [embed] at h
      linarith
  · rintro ⟨hn, hs⟩
    constructor
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [embed]
        linarith
      · simpa [embed] using hn j
    · simp [embed, Fin.sum_univ_castSucc]

theorem embed_injective : Function.Injective (embed (N := N)) := by
  intro d e h
  funext i
  simpa [embed] using congrFun h i.castSucc

theorem simplex_inverse (p : Fin (N + 1) → ℝ) (hp : simplex p) :
    solid (fun i => p i.castSucc) ∧ embed (fun i => p i.castSucc) = p := by
  have hs : (∑ i : Fin N, p i.castSucc) + p (Fin.last N) = 1 := by
    simpa only [Fin.sum_univ_castSucc] using hp.2
  constructor
  · exact ⟨fun i => hp.1 i.castSucc, by linarith [hp.1 (Fin.last N)]⟩
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [embed]
      linarith
    · simp [embed]

theorem residual_support_iff (d : Fin N → ℝ) :
    Fin.last N ∉ support (embed d) ↔ ∑ i, d i = 1 := by
  simp only [support, Set.mem_setOf_eq, not_not, embed_residual]
  constructor <;> intro h <;> linarith

theorem full_euclidean_identity (a d : Fin N → ℝ) (ha : ∑ i, a i = 1) :
    (∑ i, (embed d i - embed a i)^2) =
      (∑ i, (d i - a i)^2) + (1 - ∑ i, d i)^2 := by
  simp [Fin.sum_univ_castSucc, embed, ha]

theorem grid_embedding (M : ℤ) (hM : 0 < M) (n : Fin N → ℤ) :
    embed (RematGrid.point M n) =
      RematGrid.point M (Fin.snoc n (M - ∑ i, n i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [embed_residual, RematGrid.point, Fin.snoc_last]
    exact RematGrid.slack_identity M hM n
  · simp [embed, RematGrid.point]

theorem penalty_loss_identity (lam : ℝ) (M : ℤ) (hM : 0 < M)
    (a : Fin N → ℝ) (n : Fin N → ℤ) :
    (M : ℝ)^2 * ((∑ i, (RematGrid.point M n i - a i)^2) +
      lam * (embed (RematGrid.point M n) (Fin.last N))^2) =
      RematPenalty.loss lam M (fun i => (M : ℝ) * a i) n := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  rw [mul_add]
  change (M : ℝ)^2 * RematGrid.loss a (RematGrid.point M n) + _ = _
  rw [RematGrid.loss_scaling M hM a n]
  rw [embed_residual, RematGrid.slack_identity M hM]
  unfold RematPenalty.loss
  field_simp

theorem zero_target_coordinate (lam : ℝ) (M : ℤ) (a : Fin N → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1) (hM : 0 < M)
    (n : Fin N → ℤ) (hn : RematPenalty.isMinimum lam M (fun i => (M : ℝ) * a i) n)
    (i : Fin N) (hi : a i = 0) : n i = 0 := by
  obtain ⟨hy, hyS⟩ := RematGrid.scaled_target_hypotheses M hM a ha hs
  have hu := RematPenalty.coordinate_upper lam M _ hy hyS n hn i
  simp [hi] at hu
  exact le_antisymm hu (hn.1.1 i)

theorem positive_target_coordinate (lam : ℝ) (hlam : 0 ≤ lam) (M : ℤ) (a : Fin N → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1) (hM : 0 < M)
    (n : Fin N → ℤ) (hn : RematPenalty.isMinimum lam M (fun i => (M : ℝ) * a i) n)
    (i : Fin N) (hi : 1 ≤ (M : ℝ) * a i) : 0 < n i := by
  obtain ⟨hy, hyS⟩ := RematGrid.scaled_target_hypotheses M hM a ha hs
  have hl := RematPenalty.coordinate_lower lam hlam M _ hy hyS n hn i
  have hf : (1 : ℤ) ≤ ⌊(M : ℝ) * a i⌋ := Int.le_floor.mpr (by simpa using hi)
  omega


end RematProbability

namespace RematPenaltySelection

noncomputable section

open Finset

variable {N : ℕ}

def cost (lam : ℝ) (k : ℕ) (c : Fin N → ℝ) (E : Finset (Fin N)) : ℝ :=
  RematSelection.cost c E + lam * ((k : ℝ) - E.card)^2

def minimum (lam : ℝ) (k : ℕ) (c : Fin N → ℝ) (E : Finset (Fin N)) : Prop :=
  E.card ≤ k ∧ ∀ F : Finset (Fin N), F.card ≤ k → cost lam k c E ≤ cost lam k c F

def cutoff (c : Fin N → ℝ) (E : Finset (Fin N)) : Prop :=
  ∀ i ∈ E, ∀ j ∉ E, c i ≤ c j

theorem fixed_cardinality_iff (c : Fin N → ℝ) (E : Finset (Fin N)) :
    (∀ F : Finset (Fin N), F.card = E.card → RematSelection.cost c E ≤ RematSelection.cost c F) ↔
      cutoff c E := by
  classical
  constructor
  · intro h i hi j hj
    have hje : j ∉ E.erase i := fun h => hj (Finset.mem_of_mem_erase h)
    have hcard : (insert j (E.erase i)).card = E.card := by
      rw [Finset.card_insert_of_notMem hje]
      exact Finset.card_erase_add_one hi
    have he := Finset.sum_erase_add E c hi
    have hm := h (insert j (E.erase i)) hcard
    simp only [RematSelection.cost, Finset.sum_insert hje] at hm
    linarith
  · intro h F hF
    by_cases hne : E.Nonempty
    · obtain ⟨i, hi, hmax⟩ := E.exists_max_image c hne
      have hB : RematSelection.negative (fun j => c j - c i) ⊆ E := by
        intro j hj
        by_contra hjE
        have ho := h i hi j hjE
        have hn := (Finset.mem_filter.mp hj).2
        linarith
      have hU : E ⊆ RematSelection.negative (fun j => c j - c i) ∪
          RematSelection.zero (fun j => c j - c i) := by
        intro j hj
        have hle := hmax j hj
        by_cases heq : c j = c i
        · simp [RematSelection.zero, heq]
        · have hlt : c j < c i := (lt_or_eq_of_le hle).resolve_right heq
          simp [RematSelection.negative, hlt]
      have hc : RematSelection.cost (fun j => c j - c i) E ≤
          RematSelection.cost (fun j => c j - c i) F := by
        rw [(RematSelection.cost_eq_negative_iff _ E).mpr ⟨hB, hU⟩]
        exact RematSelection.negative_lower _ F
      rw [RematSelection.cost_shift, RematSelection.cost_shift, hF] at hc
      linarith
    · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hf : F = ∅ := Finset.card_eq_zero.mp (by simpa [he] using hF)
      simp [he, hf]

def initial (m : ℕ) : Finset (Fin N) := Finset.univ.filter (fun i => i.val < m)

def firstSet (σ : Equiv.Perm (Fin N)) (m : ℕ) : Finset (Fin N) :=
  (initial m).map σ.toEmbedding

theorem initial_card (m : ℕ) (hm : m ≤ N) : (initial (N := N) m).card = m := by
  classical
  induction m with
  | zero => simp [initial]
  | succ m ih =>
    have hmN : m < N := by omega
    have hi : initial (m + 1) = insert (⟨m, hmN⟩ : Fin N) (initial m) := by
      ext i
      simp only [initial, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        by_cases he : i.val = m
        · left
          exact Fin.ext he
        · right
          omega
      · intro h
        rcases h with h | h
        · have hv := congrArg Fin.val h
          simp only at hv
          omega
        · omega
    rw [hi, Finset.card_insert_of_notMem, ih (by omega)]
    simp [initial]

theorem prefix_card (σ : Equiv.Perm (Fin N)) (m : ℕ) (hm : m ≤ N) :
    (firstSet σ m).card = m := by
  simp [firstSet, initial_card m hm]

theorem mem_prefix (σ : Equiv.Perm (Fin N)) (m : ℕ) (i : Fin N) :
    i ∈ firstSet σ m ↔ (σ.symm i).val < m := by
  simp [firstSet, initial]

theorem prefix_cutoff (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) (m : ℕ) : cutoff c (firstSet σ m) := by
  intro i hi j hj
  rw [mem_prefix] at hi hj
  have ho : σ.symm i ≤ σ.symm j := by exact_mod_cast (show (σ.symm i).val ≤ (σ.symm j).val by omega)
  simpa using hc ho

def scalar (lam : ℝ) (k : ℕ) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (m : ℕ) : ℝ :=
  RematSelection.cost c (firstSet σ m) + lam * ((k : ℝ) - m)^2

theorem cost_prefix (lam : ℝ) (k : ℕ) (c : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) (m : ℕ) (hm : m ≤ N) :
    cost lam k c (firstSet σ m) = scalar lam k c σ m := by
  simp only [cost, scalar, prefix_card σ m hm]

theorem cutoff_cost (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) (E : Finset (Fin N)) (hE : cutoff c E) :
    RematSelection.cost c E = RematSelection.cost c (firstSet σ E.card) := by
  have hm : E.card ≤ N := by simpa using E.card_le_univ
  apply le_antisymm
  · exact (fixed_cardinality_iff c E).mpr hE _ (prefix_card σ E.card hm)
  · exact (fixed_cardinality_iff c (firstSet σ E.card)).mpr (prefix_cutoff c σ hc E.card) E
      (prefix_card σ E.card hm).symm

theorem scalar_classification (lam : ℝ) (k : ℕ) (hk : k ≤ N)
    (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (hc : Monotone (fun i => c (σ i)))
    (E : Finset (Fin N)) :
    minimum lam k c E ↔ E.card ≤ k ∧ cutoff c E ∧
      ∀ m : ℕ, m ≤ k → scalar lam k c σ E.card ≤ scalar lam k c σ m := by
  constructor
  · intro h
    have hcut : cutoff c E := by
      apply (fixed_cardinality_iff c E).mp
      intro F hF
      have hm := h.2 F (by rw [hF]; exact h.1)
      unfold cost at hm
      rw [hF] at hm
      linarith
    refine ⟨h.1, hcut, ?_⟩
    intro m hm
    have hmin := h.2 (firstSet σ m) (by rw [prefix_card σ m (hm.trans hk)]; exact hm)
    rw [cost_prefix lam k c σ m (hm.trans hk)] at hmin
    unfold cost at hmin
    rw [cutoff_cost c σ hc E hcut] at hmin
    exact hmin
  · rintro ⟨hcap, hcut, hscalar⟩
    refine ⟨hcap, fun F hF => ?_⟩
    have hbound := (fixed_cardinality_iff c (firstSet σ F.card)).mpr
      (prefix_cutoff c σ hc F.card) F (prefix_card σ F.card (hF.trans hk)).symm
    have hs := hscalar F.card hF
    unfold scalar at hs
    unfold cost
    rw [cutoff_cost c σ hc E hcut]
    linarith

theorem prefix_succ (σ : Equiv.Perm (Fin N)) (m : ℕ) (hm : m < N) :
    firstSet σ (m + 1) = insert (σ ⟨m, hm⟩) (firstSet σ m) := by
  classical
  ext i
  simp only [Finset.mem_insert, mem_prefix]
  constructor
  · intro hi
    by_cases he : (σ.symm i).val = m
    · left
      have heq : σ.symm i = ⟨m, hm⟩ := Fin.ext he
      simpa using congrArg σ heq
    · right
      omega
  · rintro (rfl | hi)
    · simp
    · omega

theorem scalar_increment (lam : ℝ) (k : ℕ) (c : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) (m : ℕ) (hm : m < N) :
    scalar lam k c σ (m + 1) - scalar lam k c σ m =
      c (σ ⟨m, hm⟩) - lam * (2 * ((k : ℝ) - m) - 1) := by
  have hnot : σ ⟨m, hm⟩ ∉ firstSet σ m := by simp [mem_prefix]
  unfold scalar
  rw [prefix_succ σ m hm]
  simp [RematSelection.cost, Finset.sum_insert hnot]
  ring


end

end RematPenaltySelection

namespace RematPenalty

noncomputable section

open Finset

variable {N : ℕ}

theorem minimum_rounded_representation (lam : ℝ) (hlam : 0 ≤ lam)
    (M : ℤ) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (n : Fin N → ℤ) (hn : isMinimum lam M y n) :
    n = RematRounding.rounded y (RematRounding.selected y n) := by
  classical
  funext i
  obtain ⟨hlo,hhi⟩ := coordinate_proximity lam hlam M y hy hs n hn i
  have hceil := Int.ceil_le_floor_add_one (y i)
  by_cases h : RematRounding.base y i < n i
  · simp [RematRounding.rounded,RematRounding.selected,h]
    dsimp [RematRounding.base] at h ⊢
    omega
  · simp [RematRounding.rounded,RematRounding.selected,h]
    dsimp [RematRounding.base] at h ⊢
    omega

theorem rounded_loss (lam : ℝ) (M : ℤ) (y : Fin N → ℝ)
    (hs : ∑ i, y i = (M : ℝ)) (E : Finset (Fin N)) :
    loss lam M y (RematRounding.rounded y E) = RematGeneral.loss y (RematRounding.base y) +
      RematPenaltySelection.cost lam (RematRounding.capacity M y) (RematRounding.benefit y) E := by
  unfold loss RematPenaltySelection.cost
  rw [RematRounding.rounded_loss, RematRounding.rounded_slack M y hs]
  push_cast
  ring

theorem rounded_minimum_iff (lam : ℝ) (hlam : 0 ≤ lam) (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) (E : Finset (Fin N)) :
    isMinimum lam M y (RematRounding.rounded y E) ↔
      RematPenaltySelection.minimum lam (RematRounding.capacity M y) (RematRounding.benefit y) E := by
  constructor
  · intro h
    refine ⟨(RematRounding.rounded_feasible_iff M y hy hs E).mp h.1, ?_⟩
    intro F hF
    have hcomp := h.2 (RematRounding.rounded y F) ((RematRounding.rounded_feasible_iff M y hy hs F).mpr hF)
    rw [rounded_loss lam M y hs E, rounded_loss lam M y hs F] at hcomp
    linarith
  · intro h
    refine ⟨(RematRounding.rounded_feasible_iff M y hy hs E).mpr h.1, ?_⟩
    intro z hz
    have hM : 0 ≤ M := by
      have hh : (0 : ℝ) ≤ M := by rw [← hs]; exact Finset.sum_nonneg (fun i _ => hy i)
      exact_mod_cast hh
    obtain ⟨v,hv⟩ := minimum_exists lam M hM y
    have hrep := minimum_rounded_representation lam hlam M y hy hs v hv
    have hvfeas : RematGeneral.feasible M (RematRounding.rounded y (RematRounding.selected y v)) := by
      rw [← hrep]; exact hv.1
    have hcomp := h.2 (RematRounding.selected y v) ((RematRounding.rounded_feasible_iff M y hy hs _).mp hvfeas)
    have hmin := hv.2 z hz
    rw [hrep,rounded_loss lam M y hs] at hmin
    rw [rounded_loss lam M y hs]
    linarith

theorem all_integer_minima_iff (lam : ℝ) (hlam : 0 ≤ lam) (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) (n : Fin N → ℤ) :
    isMinimum lam M y n ↔ ∃ E, n = RematRounding.rounded y E ∧
      RematPenaltySelection.minimum lam (RematRounding.capacity M y) (RematRounding.benefit y) E := by
  constructor
  · intro h
    have hrep := minimum_rounded_representation lam hlam M y hy hs n h
    refine ⟨RematRounding.selected y n, hrep, ?_⟩
    apply (rounded_minimum_iff lam hlam M y hy hs _).mp
    rwa [← hrep]
  · rintro ⟨E,rfl,hE⟩
    exact (rounded_minimum_iff lam hlam M y hy hs E).mpr hE

theorem capacity_le_dimension (M : ℤ) (y : Fin N → ℝ) (hs : ∑ i, y i = (M : ℝ)) :
    RematRounding.capacity M y ≤ N := by
  have h : (RematRounding.capacity M y : ℝ) ≤ N := by
    rw [← RematRounding.fraction_sum M y hs]
    calc
      (∑ i, RematRounding.fraction y i) ≤ ∑ _ : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (RematRounding.fraction_bounds y i).2.le)
      _ = N := by simp
  exact_mod_cast h

theorem all_minimizer_scalar_classification (lam : ℝ) (hlam : 0 ≤ lam)
    (M : ℤ) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (σ : Equiv.Perm (Fin N)) (hσ : Monotone (fun i => RematRounding.benefit y (σ i)))
    (n : Fin N → ℤ) :
    isMinimum lam M y n ↔ ∃ E, n = RematRounding.rounded y E ∧
      E.card ≤ RematRounding.capacity M y ∧ RematPenaltySelection.cutoff (RematRounding.benefit y) E ∧
      ∀ m : ℕ, m ≤ RematRounding.capacity M y →
        RematPenaltySelection.scalar lam (RematRounding.capacity M y) (RematRounding.benefit y) σ E.card ≤
        RematPenaltySelection.scalar lam (RematRounding.capacity M y) (RematRounding.benefit y) σ m := by
  rw [all_integer_minima_iff lam hlam M y hy hs n]
  simp_rw [RematPenaltySelection.scalar_classification lam _ (capacity_le_dimension M y hs) _ σ hσ]


end

end RematPenalty

namespace RematPenaltySelection

noncomputable section

open Finset

variable {N : ℕ}

def lastCost (k : ℕ) (hk : 0 < k) (hkN : k ≤ N) (c : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) : ℝ := c (σ ⟨k - 1, by omega⟩)

theorem increment_le_last (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) (m : ℕ) (hm : m < k) :
    scalar lam k c σ (m+1) - scalar lam k c σ m ≤ lastCost k hk hkN c σ - lam := by
  rw [scalar_increment lam k c σ m (by omega)]
  have horder : (⟨m, by omega⟩ : Fin N) ≤ ⟨k-1, by omega⟩ := by
    exact_mod_cast (show m ≤ k-1 by omega)
  have hv := hc horder
  have hreal : (m : ℝ) + 1 ≤ k := by exact_mod_cast (show m+1 ≤ k by omega)
  have hp : lam ≤ lam * (2 * ((k : ℝ) - m) - 1) := by nlinarith
  dsimp [lastCost]
  linarith

theorem scalar_last_le (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) (hth : lastCost k hk hkN c σ ≤ lam)
    (m : ℕ) (hm : m ≤ k) : scalar lam k c σ k ≤ scalar lam k c σ m := by
  have step (b : ℕ) (hb : b < k) : scalar lam k c σ (b+1) ≤ scalar lam k c σ b := by
    have hd := increment_le_last lam hlam k hk hkN c σ hc b hb
    linarith
  have chain : ∀ b, m ≤ b → b ≤ k → scalar lam k c σ b ≤ scalar lam k c σ m := by
    intro b hmb
    induction b, hmb using Nat.le_induction with
    | base => intro _; exact le_refl _
    | succ b hmb ih =>
      intro hb
      exact (step b (by omega)).trans (ih (by omega))
  exact chain k hm (le_refl _)

theorem scalar_last_lt (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) (hth : lastCost k hk hkN c σ < lam)
    (m : ℕ) (hm : m < k) : scalar lam k c σ k < scalar lam k c σ m := by
  have hle := scalar_last_le lam hlam k hk hkN c σ hc hth.le (m+1) (by omega)
  have hd := increment_le_last lam hlam k hk hkN c σ hc m hm
  linarith

theorem scalar_last_increment (lam : ℝ) (k : ℕ) (hk : 0 < k) (hkN : k ≤ N)
    (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    scalar lam k c σ k - scalar lam k c σ (k-1) = lastCost k hk hkN c σ - lam := by
  have he : k-1+1 = k := by omega
  have h := scalar_increment lam k c σ (k-1) (by omega)
  rw [he] at h
  have hc : ((k-1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hc] at h
  dsimp [lastCost]
  linarith

theorem saturated_minimum_iff (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) :
    (∃ E, minimum lam k c E ∧ E.card = k) ↔ lastCost k hk hkN c σ ≤ lam := by
  constructor
  · rintro ⟨E,hE,hcard⟩
    obtain ⟨_, _, hs⟩ := (scalar_classification lam k hkN c σ hc E).mp hE
    have hb := hs (k-1) (by omega)
    rw [hcard] at hb
    have hd := scalar_last_increment lam k hk hkN c σ
    linarith
  · intro hth
    refine ⟨firstSet σ k, ?_, prefix_card σ k hkN⟩
    apply (scalar_classification lam k hkN c σ hc _).mpr
    rw [prefix_card σ k hkN]
    exact ⟨le_refl _, prefix_cutoff c σ hc k, scalar_last_le lam hlam k hk hkN c σ hc hth⟩

theorem minimum_exists (lam : ℝ) (k : ℕ) (c : Fin N → ℝ) :
    ∃ E, minimum lam k c E := by
  classical
  let candidates := Finset.univ.filter (fun E : Finset (Fin N) => E.card ≤ k)
  have hne : candidates.Nonempty := by refine ⟨∅, ?_⟩; simp [candidates]
  obtain ⟨E,hE,hm⟩ := candidates.exists_min_image (cost lam k c) hne
  exact ⟨E,(Finset.mem_filter.mp hE).2,fun F hF => hm F (by simp [candidates,hF])⟩

theorem last_two_tie (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) (hth : lam = lastCost k hk hkN c σ) :
    minimum lam k c (firstSet σ (k-1)) ∧ minimum lam k c (firstSet σ k) := by
  have hlast := scalar_last_le lam hlam k hk hkN c σ hc hth.ge
  have heq : scalar lam k c σ (k-1) = scalar lam k c σ k := by
    have hd := scalar_last_increment lam k hk hkN c σ
    linarith
  constructor
  · apply (scalar_classification lam k hkN c σ hc _).mpr
    rw [prefix_card σ (k-1) (by omega)]
    exact ⟨by omega, prefix_cutoff c σ hc (k-1), fun m hm => by rw [heq]; exact hlast m hm⟩
  · apply (scalar_classification lam k hkN c σ hc _).mpr
    rw [prefix_card σ k hkN]
    exact ⟨le_refl _, prefix_cutoff c σ hc k, hlast⟩

theorem all_saturated_iff (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) :
    (∀ E, minimum lam k c E → E.card = k) ↔ lastCost k hk hkN c σ < lam := by
  constructor
  · intro hall
    obtain ⟨E,hE⟩ := minimum_exists lam k c
    have hle := (saturated_minimum_iff lam hlam k hk hkN c σ hc).mp ⟨E,hE,hall E hE⟩
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · have hmin := (last_two_tie lam hlam k hk hkN c σ hc h.symm).1
      have hcard := hall _ hmin
      rw [prefix_card σ (k-1) (by omega)] at hcard
      omega
  · intro hth E hE
    obtain ⟨hcap, _, hs⟩ := (scalar_classification lam k hkN c σ hc E).mp hE
    by_contra hne
    have ht := scalar_last_lt lam hlam k hk hkN c σ hc hth E.card (by omega)
    exact (not_lt_of_ge (hs k (le_refl _))) ht

theorem all_unsaturated_iff (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) :
    (∀ E, minimum lam k c E → E.card < k) ↔ lam < lastCost k hk hkN c σ := by
  constructor
  · intro hall
    by_contra hn
    obtain ⟨E,hE,hcard⟩ := (saturated_minimum_iff lam hlam k hk hkN c σ hc).mpr (le_of_not_gt hn)
    have := hall E hE
    omega
  · intro hth E hE
    have hcap := hE.1
    by_contra hn
    have hcard : E.card = k := by omega
    have := (saturated_minimum_iff lam hlam k hk hkN c σ hc).mp ⟨E,hE,hcard⟩
    linarith

theorem coexistence_iff (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) :
    ((∃ E, minimum lam k c E ∧ E.card = k) ∧
      (∃ F, minimum lam k c F ∧ F.card < k)) ↔ lam = lastCost k hk hkN c σ := by
  constructor
  · rintro ⟨hsat, F, hF, hsl⟩
    have hle := (saturated_minimum_iff lam hlam k hk hkN c σ hc).mp hsat
    have hge : lam ≤ lastCost k hk hkN c σ := by
      by_contra hn
      have hall := (all_saturated_iff lam hlam k hk hkN c σ hc).mpr (lt_of_not_ge hn)
      have := hall F hF
      omega
    exact le_antisymm hge hle
  · intro he
    obtain ⟨ha,hb⟩ := last_two_tie lam hlam k hk hkN c σ hc he
    exact ⟨⟨firstSet σ k,hb,prefix_card σ k hkN⟩,
      ⟨firstSet σ (k-1),ha,by rw [prefix_card σ (k-1) (by omega)]; omega⟩⟩


end

end RematPenaltySelection

namespace RematPenalty

noncomputable section

open Finset

variable {N : ℕ}

theorem saturated_exists_iff_selection (lam : ℝ) (hlam : 0 ≤ lam)
    (M : ℤ) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) :
    (∃ n, isMinimum lam M y n ∧ ∑ i, n i = M) ↔
    (∃ E, RematPenaltySelection.minimum lam (RematRounding.capacity M y) (RematRounding.benefit y) E ∧
      E.card = RematRounding.capacity M y) := by
  constructor
  · rintro ⟨n,hn,hS⟩
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff lam hlam M y hy hs n).mp hn
    have hsl := RematRounding.rounded_slack M y hs E
    refine ⟨E,hE,?_⟩
    omega
  · rintro ⟨E,hE,hcard⟩
    refine ⟨RematRounding.rounded y E,(rounded_minimum_iff lam hlam M y hy hs E).mpr hE,?_⟩
    have hsl := RematRounding.rounded_slack M y hs E
    omega

theorem all_saturated_iff_selection (lam : ℝ) (hlam : 0 ≤ lam)
    (M : ℤ) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) :
    (∀ n, isMinimum lam M y n → ∑ i, n i = M) ↔
    (∀ E, RematPenaltySelection.minimum lam (RematRounding.capacity M y) (RematRounding.benefit y) E →
      E.card = RematRounding.capacity M y) := by
  constructor
  · intro h E hE
    have hsE := h _ ((rounded_minimum_iff lam hlam M y hy hs E).mpr hE)
    have hsl := RematRounding.rounded_slack M y hs E
    omega
  · intro h n hn
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff lam hlam M y hy hs n).mp hn
    have hsE := h E hE
    have hsl := RematRounding.rounded_slack M y hs E
    omega

theorem positive_slack_exists_iff_selection (lam : ℝ) (hlam : 0 ≤ lam)
    (M : ℤ) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) :
    (∃ n, isMinimum lam M y n ∧ 0 < M - ∑ i, n i) ↔
    (∃ E, RematPenaltySelection.minimum lam (RematRounding.capacity M y) (RematRounding.benefit y) E ∧
      E.card < RematRounding.capacity M y) := by
  constructor
  · rintro ⟨n,hn,hS⟩
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff lam hlam M y hy hs n).mp hn
    have hsl := RematRounding.rounded_slack M y hs E
    refine ⟨E,hE,?_⟩
    omega
  · rintro ⟨E,hE,hcard⟩
    refine ⟨RematRounding.rounded y E,(rounded_minimum_iff lam hlam M y hy hs E).mpr hE,?_⟩
    have hsl := RematRounding.rounded_slack M y hs E
    omega

theorem all_positive_slack_iff_selection (lam : ℝ) (hlam : 0 ≤ lam)
    (M : ℤ) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) :
    (∀ n, isMinimum lam M y n → 0 < M - ∑ i, n i) ↔
    (∀ E, RematPenaltySelection.minimum lam (RematRounding.capacity M y) (RematRounding.benefit y) E →
      E.card < RematRounding.capacity M y) := by
  constructor
  · intro h E hE
    have hsE := h _ ((rounded_minimum_iff lam hlam M y hy hs E).mpr hE)
    have hsl := RematRounding.rounded_slack M y hs E
    omega
  · intro h n hn
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff lam hlam M y hy hs n).mp hn
    have hsE := h E hE
    have hsl := RematRounding.rounded_slack M y hs E
    omega

def threshold (M : ℤ) (y : Fin N → ℝ) (hs : ∑ i, y i = (M : ℝ))
    (hk : 0 < RematRounding.capacity M y) (σ : Equiv.Perm (Fin N)) : ℝ :=
  RematPenaltySelection.lastCost (RematRounding.capacity M y) hk (capacity_le_dimension M y hs)
    (RematRounding.benefit y) σ

theorem exact_identification_threshold (lam : ℝ) (hlam : 0 ≤ lam)
    (M : ℤ) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (hk : 0 < RematRounding.capacity M y)
    (σ : Equiv.Perm (Fin N)) (hσ : Monotone (fun i => RematRounding.benefit y (σ i))) :
    ((∀ n, isMinimum lam M y n → ∑ i, n i = M) ↔ threshold M y hs hk σ < lam) ∧
    ((∃ n, isMinimum lam M y n ∧ ∑ i, n i = M) ↔ threshold M y hs hk σ ≤ lam) ∧
    ((∀ n, isMinimum lam M y n → 0 < M - ∑ i, n i) ↔ lam < threshold M y hs hk σ) ∧
    (((∃ n, isMinimum lam M y n ∧ ∑ i, n i = M) ∧
      (∃ n, isMinimum lam M y n ∧ 0 < M - ∑ i, n i)) ↔ lam = threshold M y hs hk σ) := by
  rw [all_saturated_iff_selection lam hlam M y hy hs,
    saturated_exists_iff_selection lam hlam M y hy hs,
    all_positive_slack_iff_selection lam hlam M y hy hs,
    positive_slack_exists_iff_selection lam hlam M y hy hs]
  exact ⟨RematPenaltySelection.all_saturated_iff lam hlam _ hk (capacity_le_dimension M y hs) _ σ hσ,
    RematPenaltySelection.saturated_minimum_iff lam hlam _ hk (capacity_le_dimension M y hs) _ σ hσ,
    RematPenaltySelection.all_unsaturated_iff lam hlam _ hk (capacity_le_dimension M y hs) _ σ hσ,
    RematPenaltySelection.coexistence_iff lam hlam _ hk (capacity_le_dimension M y hs) _ σ hσ⟩

theorem zero_capacity_unique_minimum (lam : ℝ) (hlam : 0 ≤ lam)
    (M : ℤ) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (hk : RematRounding.capacity M y = 0) (n : Fin N → ℤ) :
    isMinimum lam M y n ↔ n = RematRounding.base y := by
  have hM : 0 ≤ M := by
    have hh : (0 : ℝ) ≤ M := by rw [← hs]; exact Finset.sum_nonneg (fun i _ => hy i)
    exact_mod_cast hh
  have unique (v : Fin N → ℤ) (hv : isMinimum lam M y v) : v = RematRounding.base y := by
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff lam hlam M y hy hs v).mp hv
    have hcard := hE.1
    rw [hk] at hcard
    have he : E = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [he]
    funext i
    simp [RematRounding.rounded]
  constructor
  · exact unique n
  · intro hn
    obtain ⟨v,hv⟩ := minimum_exists lam M hM y
    rwa [hn,← unique v hv]


end

end RematPenalty

namespace RematPenalty

open Finset

variable {N : ℕ}

theorem uniform_identification (lam : ℝ) (hlam : 0 ≤ lam) (hN : 0 < N)
    (hsharp : 1 - 2 / (N : ℝ) < lam) (M : ℤ) (y : Fin N → ℝ)
    (hs : ∑ i, y i = (M : ℝ)) (n : Fin N → ℤ) (hn : isMinimum lam M y n) :
    ∑ i, n i = M := by
  by_contra hneq
  have hslack : ∑ i, n i < M := lt_of_le_of_ne hn.1.2 hneq
  have hs1 : (1 : ℝ) ≤ (M : ℝ) - ∑ i, (n i : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ M - ∑ i, n i by omega)
  have hinc (i : Fin N) :
      0 ≤ 2 * ((n i : ℝ) - y i) + 1 - lam * (2 * ((M : ℝ) - ∑ j, (n j : ℝ)) - 1) := by
    have hz : RematGeneral.feasible M (Function.update n i (n i + 1)) := by
      constructor
      · intro j
        by_cases hji : j = i
        · subst j
          simpa using add_nonneg (hn.1.1 i) (show (0 : ℤ) ≤ 1 by omega)
        · simpa [Function.update_of_ne hji] using hn.1.1 j
      · rw [RematGeneral.sum_update]
        omega
    have hm := hn.2 _ hz
    unfold loss at hm
    rw [RematGeneral.loss_update, RematGeneral.sum_update] at hm
    push_cast at hm
    nlinarith
  have hall := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hinc i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs] at hall
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hbound : (1 - lam) * (N : ℝ) < 2 :=
    (lt_div_iff₀ hNR).mp (by linarith)
  have hpen : lam ≤ lam * (2 * ((M : ℝ) - ∑ j, (n j : ℝ)) - 1) := by
    nlinarith
  have hpenN := mul_le_mul_of_nonneg_left hpen hNR.le
  nlinarith


end RematPenalty

namespace RematPenalty

noncomputable section

open Finset

variable {N : ℕ}

def unitVector (i : Fin N) : Fin N → ℤ := fun j => if j = i then 1 else 0

theorem unit_sum (i : Fin N) : ∑ j, unitVector i j = 1 := by
  simp [unitVector]

theorem unit_feasible (i : Fin N) : RematGeneral.feasible 1 (unitVector i) := by
  constructor
  · intro j
    simp only [unitVector]
    split_ifs <;> norm_num
  · rw [unit_sum]

theorem capacity_one_feasible_iff (n : Fin N → ℤ) :
    RematGeneral.feasible 1 n ↔ n = (fun _ => 0) ∨ ∃ i, n = unitVector i := by
  constructor
  · intro hn
    by_cases hz : ∀ i, n i = 0
    · exact Or.inl (funext hz)
    · push Not at hz
      obtain ⟨i,hi⟩ := hz
      have hni : n i = 1 := by
        have hlo := hn.1 i
        have hhi := (Finset.single_le_sum (fun j _ => hn.1 j) (Finset.mem_univ i)).trans hn.2
        omega
      right
      refine ⟨i, ?_⟩
      funext j
      by_cases hji : j = i
      · subst j
        simp [unitVector,hni]
      · have hsum := Finset.sum_erase_add Finset.univ n (Finset.mem_univ i)
        have hjsum : n j ≤ ∑ k ∈ Finset.univ.erase i, n k :=
          Finset.single_le_sum (fun k _ => hn.1 k) (by simp [hji])
        have hlo := hn.1 j
        have hcap := hn.2
        simp [unitVector,hji]
        omega
  · rintro (rfl | ⟨i,rfl⟩)
    · exact ⟨fun _ => le_refl _, by simp⟩
    · exact unit_feasible i

theorem zero_loss (lam : ℝ) (y : Fin N → ℝ) :
    loss lam 1 y (fun _ => 0) = (∑ i, (y i)^2) + lam := by
  simp [loss, RematGeneral.loss]

theorem unit_loss (lam : ℝ) (y : Fin N → ℝ) (i : Fin N) :
    loss lam 1 y (unitVector i) = (∑ j, (y j)^2) + (1 - 2 * y i) := by
  have he : unitVector i = Function.update (fun _ : Fin N => (0 : ℤ)) i 1 := by
    funext j
    by_cases h : j = i <;> simp [unitVector,h,Function.update_of_ne]
  unfold loss
  rw [unit_sum]
  simp only [sub_self,Int.cast_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero,add_zero]
  rw [he,RematGeneral.loss_update]
  simp [RematGeneral.loss]
  ring

theorem capacity_one_minimum_iff (lam : ℝ) (y : Fin N → ℝ) (n : Fin N → ℤ) :
    isMinimum lam 1 y n ↔
      (n = (fun _ => 0) ∧ ∀ i, lam ≤ 1 - 2 * y i) ∨
      ∃ i, n = unitVector i ∧ 1 - 2 * y i ≤ lam ∧ ∀ j, y j ≤ y i := by
  constructor
  · intro hn
    rcases (capacity_one_feasible_iff n).mp hn.1 with hz | ⟨i,hi⟩
    · left
      refine ⟨hz, fun i => ?_⟩
      have hm := hn.2 (unitVector i) (unit_feasible i)
      rw [hz,zero_loss,unit_loss] at hm
      linarith
    · right
      refine ⟨i,hi,?_,?_⟩
      · have hm := hn.2 (fun _ => 0) ⟨fun _ => le_refl _,by simp⟩
        rw [hi,unit_loss,zero_loss] at hm
        linarith
      · intro j
        have hm := hn.2 (unitVector j) (unit_feasible j)
        rw [hi,unit_loss,unit_loss] at hm
        linarith
  · rintro (⟨rfl,hle⟩ | ⟨i,rfl,hle,hmax⟩)
    · refine ⟨⟨fun _ => le_refl _,by simp⟩,fun z hz => ?_⟩
      rcases (capacity_one_feasible_iff z).mp hz with rfl | ⟨i,rfl⟩
      · exact le_refl _
      · rw [zero_loss,unit_loss]
        linarith [hle i]
    · refine ⟨unit_feasible i,fun z hz => ?_⟩
      rcases (capacity_one_feasible_iff z).mp hz with rfl | ⟨j,rfl⟩
      · rw [unit_loss,zero_loss]
        linarith
      · rw [unit_loss,unit_loss]
        linarith [hmax j]

theorem uniform_sharpness_family (lam : ℝ) (hlam : 0 ≤ lam)
    (hN : 0 < N) (q : ℕ) (n : Fin N → ℤ) :
    isMinimum lam ((q : ℤ) * N + 1)
      (fun _ => (((q : ℤ) * N + 1 : ℤ) : ℝ) / N) n ↔
      (n = (fun _ => (q : ℤ)) ∧ lam ≤ 1 - 2 / (N : ℝ)) ∨
      (∃ i, n = (fun j => (q : ℤ) + unitVector i j) ∧ 1 - 2 / (N : ℝ) ≤ lam) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have he : (fun i : Fin N => (((q : ℤ) * N + 1 : ℤ) : ℝ) / N) =
      (fun i => (q : ℝ) + 1 / (N : ℝ)) := by
    funext i
    push_cast
    field_simp
  have hs : ∑ _ : Fin N, (1 : ℝ) / N = 1 := by simp [ne_of_gt hNR]
  have hc : (∑ _ : Fin N, (q : ℤ)) + 1 = (q : ℤ) * N + 1 := by simp; ring
  have ht := minimum_translation_iff lam hlam (fun _ : Fin N => (q : ℤ))
    (fun _ : Fin N => (1 : ℝ) / N) 1 (by norm_num) (fun _ => by positivity)
    (fun _ => (one_div_pos.mpr hNR).le) (by simpa using hs) n
  rw [hc] at ht
  rw [he]
  simp only [Int.cast_natCast] at ht
  rw [ht]
  simp_rw [capacity_one_minimum_iff]
  constructor
  · rintro ⟨z,hn, hz | hz⟩
    · left
      refine ⟨?_,?_⟩
      · rw [hn,hz.1]
        simp
      · have hh := hz.2 ⟨0,hN⟩
        simpa [div_eq_mul_inv] using hh
    · right
      obtain ⟨i,hi,hli,_⟩ := hz
      refine ⟨i,?_,?_⟩
      · rw [hn,hi]
      · simpa [div_eq_mul_inv] using hli
  · rintro (⟨hn,hth⟩ | ⟨i,hn,hth⟩)
    · refine ⟨fun _ => 0,by simpa using hn,Or.inl ⟨rfl,?_⟩⟩
      intro i
      simpa [div_eq_mul_inv] using hth
    · refine ⟨unitVector i,hn,Or.inr ⟨i,rfl,?_,fun _ => le_refl _⟩⟩
      simpa [div_eq_mul_inv] using hth


end

end RematPenalty

namespace RematRefinement

open Finset GridResidueCertificate

noncomputable def target : Fin 4 → ℝ := fun i => (weights i : ℝ) / 10

noncomputable def representative (M : ℕ) : Fin 4 → ℝ :=
  RematGrid.point (M : ℤ) (residuePoint (M / 10) ⟨M % 10, Nat.mod_lt M (by decide)⟩)

theorem integer_residue_minimum_iff (q : ℕ) (r : Fin 10) (hr : r.val ≠ 5) (n : Fin 4 → ℤ) :
    RematGeneral.isMinimum (residueCapacity q r) (residueTarget q r) n ↔ n = residuePoint q r := by
  constructor
  · intro hn
    by_contra hne
    have hs := residue_unique_minimum q r hr n hn.1 hne
    have hl := hn.2 (residuePoint q r) (residue_feasible q r)
    exact (not_lt_of_ge hl) hs
  · rintro rfl
    exact ⟨residue_feasible q r, fun z hz => residue_global_minimum q r z hz⟩

theorem real_residue_minimum_iff (q : ℕ) (r : Fin 10)
    (hM : 0 < residueCapacity q r) (hr : r.val ≠ 5) (d : Fin 4 → ℝ) :
    RematGrid.isMinimum (residueCapacity q r) target d ↔
      d = RematGrid.point (residueCapacity q r) (residuePoint q r) := by
  have he : (fun i => (residueCapacity q r : ℝ) * target i) = residueTarget q r := by
    funext i
    dsimp [target, residueTarget]
    ring
  rw [RematGrid.minimum_iff_exists_integer _ hM, he]
  simp_rw [integer_residue_minimum_iff q r hr]
  simp

theorem mesh_minimum_iff (M : ℕ) (hM : 0 < M) (hr : M % 10 ≠ 5) (d : Fin 4 → ℝ) :
    RematGrid.isMinimum (M : ℤ) target d ↔ d = representative M := by
  let r : Fin 10 := ⟨M % 10, Nat.mod_lt M (by decide)⟩
  have hc : residueCapacity (M / 10) r = (M : ℤ) := by
    unfold residueCapacity
    dsimp [r]
    omega
  have hp : 0 < residueCapacity (M / 10) r := by rw [hc]; exact_mod_cast hM
  have h := real_residue_minimum_iff (M / 10) r hp hr d
  simpa only [hc, representative, r] using h

theorem representative_slack (M : ℕ) (hM : 0 < M) :
    1 - ∑ i, representative M i = if M % 10 = 1 ∨ M % 10 = 5 then 1 / (M : ℝ) else 0 := by
  let r : Fin 10 := ⟨M % 10, Nat.mod_lt M (by decide)⟩
  have hc : residueCapacity (M / 10) r = (M : ℤ) := by
    unfold residueCapacity
    dsimp [r]
    omega
  have hp : (0 : ℤ) < M := by exact_mod_cast hM
  have hslack := residue_slack (M / 10) r
  rw [hc] at hslack
  unfold representative
  rw [RematGrid.slack_identity _ hp]
  change (((M : ℤ) - ∑ i, residuePoint (M / 10) r i : ℤ) : ℝ) / M = _
  rw [hslack]
  by_cases h : M % 10 = 1 ∨ M % 10 = 5
  · simp [r, h]
  · simp [r, h]

theorem representative_loss (M : ℕ) (hM : 0 < M) :
    (M : ℝ)^2 * RematGrid.loss target (representative M) =
      (![0,30,40,30,40,50,40,30,40,50] : Fin 10 → ℝ) ⟨M % 10, Nat.mod_lt M (by decide)⟩ / 100 := by
  let r : Fin 10 := ⟨M % 10, Nat.mod_lt M (by decide)⟩
  have hc : residueCapacity (M / 10) r = (M : ℤ) := by
    unfold residueCapacity
    dsimp [r]
    omega
  have hp : (0 : ℤ) < M := by exact_mod_cast hM
  unfold representative
  have hscale := RematGrid.loss_scaling (M : ℤ) hp target (residuePoint (M / 10) r)
  simp only [Int.cast_natCast] at hscale
  rw [hscale]
  have he : (fun i => (M : ℝ) * target i) = residueTarget (M / 10) r := by
    funext i
    dsimp [target, residueTarget]
    rw [hc]
    push_cast
    ring
  rw [he]
  exact residue_exact_loss (M / 10) r

theorem eleven_permanent_failure (j : ℕ) :
    (∀ d, RematGrid.isMinimum ((11^j : ℕ) : ℤ) target d ↔ d = representative (11^j)) ∧
    1 - ∑ i, representative (11^j) i = 1 / ((11^j : ℕ) : ℝ) ∧
    (0 : ℝ) < 1 - ∑ i, representative (11^j) i := by
  have hM : 0 < (11 : ℕ)^j := by positivity
  have hr : (11 : ℕ)^j % 10 = 1 := by simp [Nat.pow_mod]
  refine ⟨fun d => mesh_minimum_iff _ hM (by omega) d, ?_, ?_⟩
  · rw [representative_slack _ hM]
    simp [hr]
  · rw [representative_slack _ hM]
    simp [hr]

theorem doubled_eleven_permanent_identification (j : ℕ) :
    (∀ d, RematGrid.isMinimum ((2*11^j : ℕ) : ℤ) target d ↔ d = representative (2*11^j)) ∧
    1 - ∑ i, representative (2*11^j) i = 0 ∧
    ((2*11^j : ℕ) : ℝ)^2 * RematGrid.loss target (representative (2*11^j)) = 2/5 ∧
    representative (2*11^j) ≠ target := by
  have hM : 0 < 2 * (11 : ℕ)^j := by positivity
  have hr : 2 * (11 : ℕ)^j % 10 = 2 := by simp [Nat.mul_mod, Nat.pow_mod]
  have hl : ((2*11^j : ℕ) : ℝ)^2 * RematGrid.loss target (representative (2*11^j)) = 2/5 := by
    rw [representative_loss _ hM]
    norm_num [hr]
  refine ⟨fun d => mesh_minimum_iff _ hM (by omega) d, ?_, hl, ?_⟩
  · rw [representative_slack _ hM]
    simp [hr]
  · intro he
    rw [he] at hl
    norm_num [RematGrid.loss] at hl

theorem ternary_residue_classification (j : ℕ) :
    3^j % 10 = if j % 4 = 0 then 1 else if j % 4 = 1 then 3 else if j % 4 = 2 then 9 else 7 := by
  have hj : j = 4 * (j / 4) + j % 4 := by omega
  have hr : j % 4 < 4 := Nat.mod_lt j (by decide)
  rcases (show j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 by omega) with h | h | h | h
  · have he : j = 4*(j/4) := by omega
    conv_lhs => rw [he]
    rw [ternary_residue_zero]
    simp [h]
  · have he : j = 4*(j/4)+1 := by omega
    conv_lhs => rw [he]
    rw [ternary_residue_one]
    simp [h]
  · have he : j = 4*(j/4)+2 := by omega
    conv_lhs => rw [he]
    rw [ternary_residue_two]
    simp [h]
  · have he : j = 4*(j/4)+3 := by omega
    conv_lhs => rw [he]
    rw [ternary_residue_three]
    simp [h]

theorem ternary_alternating_identification (j : ℕ) :
    (∀ d, RematGrid.isMinimum ((3^j : ℕ) : ℤ) target d ↔ d = representative (3^j)) ∧
    1 - ∑ i, representative (3^j) i = if j % 4 = 0 then 1 / ((3^j : ℕ) : ℝ) else 0 := by
  have hM : 0 < (3 : ℕ)^j := by positivity
  have hr := ternary_residue_classification j
  have hr5 : 3^j % 10 ≠ 5 := by split_ifs at hr <;> omega
  refine ⟨fun d => mesh_minimum_iff _ hM hr5 d, ?_⟩
  rw [representative_slack _ hM, hr]
  split_ifs <;> norm_num at *

theorem three_refinement_regimes :
    (∀ j : ℕ, (∀ d, RematGrid.isMinimum ((11^j : ℕ) : ℤ) target d ↔ d = representative (11^j)) ∧
      1 - ∑ i, representative (11^j) i = 1 / ((11^j : ℕ) : ℝ) ∧
      (0 : ℝ) < 1 - ∑ i, representative (11^j) i) ∧
    (∀ j : ℕ, (∀ d, RematGrid.isMinimum ((2*11^j : ℕ) : ℤ) target d ↔ d = representative (2*11^j)) ∧
      1 - ∑ i, representative (2*11^j) i = 0 ∧
      ((2*11^j : ℕ) : ℝ)^2 * RematGrid.loss target (representative (2*11^j)) = 2/5 ∧
      representative (2*11^j) ≠ target) ∧
    (∀ j : ℕ, (∀ d, RematGrid.isMinimum ((3^j : ℕ) : ℤ) target d ↔ d = representative (3^j)) ∧
      1 - ∑ i, representative (3^j) i = if j % 4 = 0 then 1 / ((3^j : ℕ) : ℝ) else 0) := by
  exact ⟨eleven_permanent_failure, doubled_eleven_permanent_identification, ternary_alternating_identification⟩


end RematRefinement

namespace RematPenalty

noncomputable section

open Finset GridResidueCertificate

theorem four_capacity_one_minimum_iff (lam : ℝ) (n : Fin 4 → ℤ) :
    isMinimum lam 1 RematRefinement.target n ↔
      (n = (fun _ => 0) ∧ lam ≤ 1/5) ∨ (n = unitVector 0 ∧ 1/5 ≤ lam) := by
  rw [capacity_one_minimum_iff]
  constructor
  · rintro (⟨hn,hall⟩ | ⟨i,hn,hle,hmax⟩)
    · exact Or.inl ⟨hn,by have h := hall 0; norm_num [RematRefinement.target,weights] at h; linarith⟩
    · right
      have hi : i = 0 := by
        have h0 := hmax 0
        fin_cases i <;> norm_num [RematRefinement.target,weights] at *
      subst i
      exact ⟨hn,by norm_num [RematRefinement.target,weights] at hle ⊢; linarith⟩
  · rintro (⟨hn,hle⟩ | ⟨hn,hle⟩)
    · refine Or.inl ⟨hn,?_⟩
      intro i
      fin_cases i <;> norm_num [RematRefinement.target,weights] <;> linarith
    · refine Or.inr ⟨0,hn,by norm_num [RematRefinement.target,weights] at hle ⊢; linarith,?_⟩
      intro j
      fin_cases j <;> norm_num [RematRefinement.target,weights]

theorem four_penalty_transition (lam : ℝ) (hlam : 0 ≤ lam) (q : ℕ) (n : Fin 4 → ℤ) :
    isMinimum lam (10*(q : ℤ)+1) (fourTarget q) n ↔
      (n = fourGrid q ∧ lam ≤ 1/5) ∨
      (n = (fun i => fourGrid q i + unitVector 0 i) ∧ 1/5 ≤ lam) := by
  have hp : ∀ i, 0 ≤ fourGrid q i := four_grid_nonnegative q
  have hy : ∀ i, 0 ≤ RematRefinement.target i := by
    intro i; fin_cases i <;> norm_num [RematRefinement.target,weights]
  have hs : ∑ i, RematRefinement.target i = (1 : ℝ) := by
    norm_num [RematRefinement.target,weights,Fin.sum_univ_succ]
  have ht := minimum_translation_iff lam hlam (fourGrid q) RematRefinement.target 1
    (by norm_num) hp hy (by simpa using hs) n
  have hsum : (∑ i, fourGrid q i) + 1 = 10*(q : ℤ)+1 := by
    simp [fourGrid,Fin.sum_univ_succ]; ring
  have htar : (fun i => (fourGrid q i : ℝ) + RematRefinement.target i) = fourTarget q := by
    funext i
    fin_cases i <;> simp [fourGrid,RematRefinement.target,weights,fourTarget] <;> ring
  rw [hsum,htar] at ht
  rw [ht]
  simp_rw [four_capacity_one_minimum_iff]
  constructor
  · rintro ⟨z,hn,hz | hz⟩
    · left
      refine ⟨?_,hz.2⟩
      rw [hn,hz.1]
      simp
    · right
      refine ⟨?_,hz.2⟩
      rw [hn,hz.1]
  · rintro (⟨hn,hth⟩ | ⟨hn,hth⟩)
    · exact ⟨fun _ => 0,by simpa using hn,Or.inl ⟨rfl,hth⟩⟩
    · exact ⟨unitVector 0,hn,Or.inr ⟨rfl,hth⟩⟩

theorem four_penalty_errors (lam : ℝ) (q : ℕ) :
    loss lam (10*(q : ℤ)+1) (fourTarget q) (fourGrid q) = 3/10+lam ∧
    loss lam (10*(q : ℤ)+1) (fourTarget q)
      (fun i => fourGrid q i + unitVector 0 i) = 1/2 := by
  constructor
  · unfold loss
    change squareLoss (fourTarget q) (fourGrid q) + _ = _
    rw [four_exact_loss,four_grid_slack]
    norm_num
  · unfold loss RematGeneral.loss
    simp [fourTarget,fourGrid,unitVector,Fin.sum_univ_succ]
    ring

theorem eleven_positive_penalty_failure (lam : ℝ) (hlam : 0 ≤ lam) (hth : lam < 1/5) (j : ℕ) :
    ∃ q : ℕ, 11^j = 10*q+1 ∧
      (∀ n, isMinimum lam ((11^j : ℕ) : ℤ) (fourTarget q) n ↔ n = fourGrid q) ∧
      ((11^j : ℕ) : ℤ) - ∑ i, fourGrid q i = 1 := by
  obtain ⟨q,hq⟩ := eleven_mesh_form j
  refine ⟨q,hq,?_,?_⟩
  · intro n
    have hcap : ((11^j : ℕ) : ℤ) = 10*(q : ℤ)+1 := by exact_mod_cast hq
    rw [hcap,four_penalty_transition lam hlam q n]
    constructor
    · rintro (⟨hn,_⟩ | ⟨_,hle⟩)
      · exact hn
      · linarith
    · intro hn
      exact Or.inl ⟨hn,hth.le⟩
  · have hcap : ((11^j : ℕ) : ℤ) = 10*(q : ℤ)+1 := by exact_mod_cast hq
    rw [hcap]
    exact four_grid_slack q


end

end RematPenalty

namespace RematPenaltyGrid

open Finset

variable {N : ℕ}

def loss (lam : ℝ) (a d : Fin N → ℝ) : ℝ :=
  RematGrid.loss a d + lam * (1 - ∑ i, d i)^2

def isMinimum (lam : ℝ) (M : ℤ) (a d : Fin N → ℝ) : Prop :=
  RematGrid.feasible M d ∧ ∀ e, RematGrid.feasible M e → loss lam a d ≤ loss lam a e

theorem loss_scaling (lam : ℝ) (M : ℤ) (hM : 0 < M) (a : Fin N → ℝ) (n : Fin N → ℤ) :
    (M : ℝ)^2 * loss lam a (RematGrid.point M n) =
      RematPenalty.loss lam M (fun i => (M : ℝ) * a i) n := by
  simpa only [loss, RematGrid.loss, RematProbability.embed_residual] using
    RematProbability.penalty_loss_identity lam M hM a n

theorem minimum_point_iff (lam : ℝ) (M : ℤ) (hM : 0 < M)
    (a : Fin N → ℝ) (n : Fin N → ℤ) :
    isMinimum lam M a (RematGrid.point M n) ↔
      RematPenalty.isMinimum lam M (fun i => (M : ℝ) * a i) n := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hp : (0 : ℝ) < (M : ℝ)^2 := sq_pos_of_pos hm
  constructor
  · rintro ⟨hf,ho⟩
    refine ⟨(RematGrid.point_feasible_iff M hM n).mp hf,?_⟩
    intro z hz
    rw [← loss_scaling lam M hM a n,← loss_scaling lam M hM a z]
    exact mul_le_mul_of_nonneg_left (ho (RematGrid.point M z)
      ((RematGrid.point_feasible_iff M hM z).mpr hz)) hp.le
  · rintro ⟨hf,ho⟩
    refine ⟨(RematGrid.point_feasible_iff M hM n).mpr hf,?_⟩
    intro e he
    obtain ⟨z,rfl⟩ := he.2.2
    have hi := ho z ((RematGrid.point_feasible_iff M hM z).mp he)
    rw [← loss_scaling lam M hM a n,← loss_scaling lam M hM a z] at hi
    exact le_of_mul_le_mul_left hi hp

theorem minimum_iff_exists_integer (lam : ℝ) (M : ℤ) (hM : 0 < M)
    (a d : Fin N → ℝ) :
    isMinimum lam M a d ↔ ∃ n, d = RematGrid.point M n ∧
      RematPenalty.isMinimum lam M (fun i => (M : ℝ) * a i) n := by
  constructor
  · intro h
    obtain ⟨n,hd⟩ := h.1.2.2
    refine ⟨n,hd,?_⟩
    rw [hd] at h
    exact (minimum_point_iff lam M hM a n).mp h
  · rintro ⟨n,rfl,hn⟩
    exact (minimum_point_iff lam M hM a n).mpr hn


end RematPenaltyGrid

namespace RematProbability

open Finset

variable {N : ℕ}

def simplexGrid (M : ℤ) (p : Fin (N+1) → ℝ) : Prop :=
  simplex p ∧ ∃ z : Fin (N+1) → ℤ, p = RematGrid.point M z

theorem grid_embedding_iff (M : ℤ) (hM : 0 < M) (d : Fin N → ℝ) :
    simplexGrid M (embed d) ↔ RematGrid.feasible M d := by
  constructor
  · rintro ⟨hp,z,hz⟩
    obtain ⟨hn,hs⟩ := (embed_simplex_iff d).mp hp
    refine ⟨hn,hs,(fun i => z i.castSucc),?_⟩
    funext i
    have hi := congrFun hz i.castSucc
    simpa [embed,RematGrid.point] using hi
  · rintro ⟨hn,hs,n,rfl⟩
    refine ⟨(embed_simplex_iff _).mpr ⟨hn,hs⟩,Fin.snoc n (M-∑ i,n i),?_⟩
    exact grid_embedding M hM n

theorem lexical_support_preserved (lam : ℝ) (hlam : 0 ≤ lam) (M : ℤ) (hM : 0 < M)
    (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1)
    (hlarge : ∀ i, 0 < a i → 1 ≤ (M : ℝ) * a i)
    (n : Fin N → ℤ) (hn : RematPenalty.isMinimum lam M (fun i => (M : ℝ) * a i) n)
    (i : Fin N) :
    i.castSucc ∈ support (embed (RematGrid.point M n)) ↔ i.castSucc ∈ support (embed a) := by
  simp only [support,Set.mem_setOf_eq,embed_lexical,RematGrid.point]
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  rw [div_ne_zero_iff]
  by_cases hzero : a i = 0
  · have hnzero := zero_target_coordinate lam M a ha hs hM n hn i hzero
    simp [hnzero,hzero]
  · have haPos : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hzero)
    have hnPos := positive_target_coordinate lam hlam M a ha hs hM n hn i (hlarge i haPos)
    have hnNe : (n i : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hnPos
    simp [hnNe,hm,hzero]

theorem full_support_iff_saturated (lam : ℝ) (hlam : 0 ≤ lam) (M : ℤ) (hM : 0 < M)
    (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1)
    (hlarge : ∀ i, 0 < a i → 1 ≤ (M : ℝ) * a i)
    (n : Fin N → ℤ) (hn : RematPenalty.isMinimum lam M (fun i => (M : ℝ) * a i) n) :
    support (embed (RematGrid.point M n)) = support (embed a) ↔ ∑ i, n i = M := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  have hr : Fin.last N ∉ support (embed a) := (residual_support_iff a).mpr hs
  constructor
  · intro he
    have hl : Fin.last N ∉ support (embed (RematGrid.point M n)) := by rwa [he]
    have hsum := (residual_support_iff _).mp hl
    rw [RematGrid.point_sum] at hsum
    have hi := (div_eq_one_iff_eq hm).mp hsum
    exact_mod_cast hi
  · intro hsum
    apply Set.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hpoint : ∑ j, RematGrid.point M n j = 1 := by
        rw [RematGrid.point_sum,hsum]
        exact div_self hm
      have hl : Fin.last N ∉ support (embed (RematGrid.point M n)) :=
        (residual_support_iff _).mpr hpoint
      simp [hl,hr]
    · exact lexical_support_preserved lam hlam M hM a ha hs hlarge n hn j


end RematProbability

namespace RematRefinement

open Finset

def nested (M : ℕ → ℕ) : Prop :=
  ∀ j (d : Fin 4 → ℝ), RematGrid.feasible (M j : ℤ) d → RematGrid.feasible (M (j+1) : ℤ) d

def unbounded (M : ℕ → ℕ) : Prop := ∀ B : ℕ, ∃ j, B < M j

theorem grid_multiply_nested {N : ℕ} (M b : ℤ) (hM : 0 < M) (hb : 0 < b)
    (d : Fin N → ℝ) (hd : RematGrid.feasible M d) : RematGrid.feasible (M*b) d := by
  obtain ⟨hn,hs,n,rfl⟩ := hd
  refine ⟨hn,hs,(fun i => b * n i),?_⟩
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  funext i
  dsimp [RematGrid.point]
  push_cast
  field_simp

theorem eleven_nested : nested (fun j => 11^j) := by
  intro j d hd
  have hm : (0 : ℤ) < (11^j : ℕ) := by positivity
  have h := grid_multiply_nested ((11^j : ℕ) : ℤ) 11 hm (by norm_num) d hd
  simpa only [pow_succ,Nat.cast_mul,Nat.cast_ofNat] using h

theorem doubled_eleven_nested : nested (fun j => 2*11^j) := by
  intro j d hd
  have hm : (0 : ℤ) < (2*11^j : ℕ) := by positivity
  have h := grid_multiply_nested ((2*11^j : ℕ) : ℤ) 11 hm (by norm_num) d hd
  simpa only [pow_succ,Nat.cast_mul,Nat.cast_ofNat,mul_assoc] using h

theorem ternary_nested : nested (fun j => 3^j) := by
  intro j d hd
  have hm : (0 : ℤ) < (3^j : ℕ) := by positivity
  have h := grid_multiply_nested ((3^j : ℕ) : ℤ) 3 hm (by norm_num) d hd
  simpa only [pow_succ,Nat.cast_mul,Nat.cast_ofNat] using h

theorem power_unbounded (b : ℕ) (hb : 2 ≤ b) : unbounded (fun j => b^j) := by
  have hpow (j : ℕ) : j < b^j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      have hp : 0 < b^j := pow_pos (by omega) _
      nlinarith
  intro B
  exact ⟨B,hpow B⟩

theorem doubled_eleven_unbounded : unbounded (fun j => 2*11^j) := by
  intro B
  obtain ⟨j,hj⟩ := power_unbounded 11 (by norm_num) B
  refine ⟨j,?_⟩
  dsimp at hj ⊢
  omega

theorem ternary_infinitely_many_each (J : ℕ) :
    (∃ j, J ≤ j ∧ 0 < 1 - ∑ i, representative (3^j) i) ∧
    (∃ j, J ≤ j ∧ 1 - ∑ i, representative (3^j) i = 0) := by
  constructor
  · refine ⟨4*(J+1),by omega,?_⟩
    rw [(ternary_alternating_identification (4*(J+1))).2]
    simp
  · refine ⟨4*(J+1)+1,by omega,?_⟩
    rw [(ternary_alternating_identification (4*(J+1)+1)).2]
    simp

theorem nested_unbounded_refinements :
    nested (fun j => 11^j) ∧ nested (fun j => 2*11^j) ∧ nested (fun j => 3^j) ∧
    unbounded (fun j => 11^j) ∧ unbounded (fun j => 2*11^j) ∧ unbounded (fun j => 3^j) ∧
    ∀ J : ℕ, (∃ j, J ≤ j ∧ 0 < 1 - ∑ i, representative (3^j) i) ∧
      (∃ j, J ≤ j ∧ 1 - ∑ i, representative (3^j) i = 0) := by
  exact ⟨eleven_nested,doubled_eleven_nested,ternary_nested,power_unbounded 11 (by norm_num),
    doubled_eleven_unbounded,power_unbounded 3 (by norm_num),ternary_infinitely_many_each⟩


end RematRefinement

namespace RematPenaltyGrid

open Finset

variable {N : ℕ}

theorem uniform_identification (lam : ℝ) (hlam : 0 ≤ lam) (hN : 0 < N)
    (hsharp : 1 - 2 / (N : ℝ) < lam) (M : ℤ) (hM : 0 < M)
    (a d : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (hs : ∑ i,a i = 1)
    (hn : isMinimum lam M a d) : ∑ i, d i = 1 := by
  obtain ⟨n,rfl,hni⟩ := (minimum_iff_exists_integer lam M hM a d).mp hn
  obtain ⟨_,hsy⟩ := RematGrid.scaled_target_hypotheses M hM a ha hs
  have he := RematPenalty.uniform_identification lam hlam hN hsharp M _ hsy n hni
  rw [RematGrid.point_sum,he]
  exact div_self (by exact_mod_cast ne_of_gt hM)

theorem full_euclidean_identification (hN : 0 < N) (M : ℤ) (hM : 0 < M)
    (a d : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (hs : ∑ i,a i = 1)
    (hn : isMinimum 1 M a d) : ∑ i,d i = 1 := by
  have hp : (0 : ℝ) < 2 / N := div_pos (by norm_num) (by exact_mod_cast hN)
  exact uniform_identification 1 (by norm_num) hN (by linarith) M hM a d ha hs hn


end RematPenaltyGrid

namespace RematRefinement

open Finset GridResidueCertificate

theorem residue_point_lower (q : ℕ) (r : Fin 10) (i : Fin 4) : (q : ℤ) ≤ residuePoint q r i := by
  fin_cases r <;> fin_cases i <;> simp [residuePoint,residueBase,weights] <;> omega

theorem ternary_lexical_positive (j : ℕ) (hj : 2 ≤ j) (i : Fin 4) :
    0 < representative (3^j) i := by
  by_cases he : j = 2
  · subst j
    fin_cases i <;> norm_num [representative,RematGrid.point,residuePoint,residueBase,weights]
  · have hthree : 3 ≤ j := by omega
    have hbound : 10 ≤ (3 : ℕ)^j := by
      induction j, hthree using Nat.le_induction with
      | base => norm_num
      | succ k hk ih =>
        rw [pow_succ]
        omega
    have hq : 1 ≤ (3 : ℕ)^j / 10 := by omega
    have hn := residue_point_lower ((3 : ℕ)^j / 10)
      ⟨3^j % 10,Nat.mod_lt _ (by norm_num)⟩ i
    have hpos : (0 : ℤ) < residuePoint ((3 : ℕ)^j / 10)
      ⟨3^j % 10,Nat.mod_lt _ (by norm_num)⟩ i := by omega
    unfold representative RematGrid.point
    exact div_pos (by exact_mod_cast hpos) (by positivity)

theorem exact_target_control (j : ℕ) (d : Fin 4 → ℝ) :
    RematGrid.isMinimum ((10*11^j : ℕ) : ℤ) target d ↔ d = target := by
  have hcap : residueCapacity (11^j) 0 = ((10*11^j : ℕ) : ℤ) := by
    simp [residueCapacity]
  have hm : 0 < residueCapacity (11^j) 0 := by rw [hcap]; positivity
  have he : RematGrid.point (residueCapacity (11^j) 0) (residuePoint (11^j) 0) = target := by
    funext i
    have hp : (((11^j : ℕ) : ℝ)) ≠ 0 := by positivity
    simp [RematGrid.point,residueCapacity,residuePoint,residueBase,target]
    field_simp
    fin_cases i <;> simp
  have hh := real_residue_minimum_iff (11^j) 0 hm (by norm_num) d
  rw [he,hcap] at hh
  exact hh


end RematRefinement

namespace RematPenalty

variable {N : ℕ}

theorem zero_penalty_minimum_iff (M : ℤ) (y : Fin N → ℝ) (n : Fin N → ℤ) :
    isMinimum 0 M y n ↔ RematGeneral.isMinimum M y n := by
  simp [isMinimum,loss,RematGeneral.isMinimum]


end RematPenalty

namespace RematPenaltySelection

noncomputable section

variable {N : ℕ}

theorem sorted_permutation_exists (c : Fin N → ℝ) :
    ∃ σ : Equiv.Perm (Fin N), Monotone (fun i => c (σ i)) := by
  letI : LinearOrder (Fin N) := LinearOrder.lift' (fun i : Fin N => toLex (c i,i)) (by
    intro i j hij
    exact congrArg (fun z => (ofLex z).2) hij)
  let e := Fintype.orderIsoFinOfCardEq (Fin N) (Fintype.card_fin N)
  refine ⟨e.toEquiv,?_⟩
  intro i j hij
  have he : toLex (c (e i),e i) ≤ toLex (c (e j),e j) := by
    exact e.map_rel_iff.mpr hij
  exact Prod.Lex.monotone_fst _ _ he


end

end RematPenaltySelection

namespace RematPenalty

noncomputable section

open Finset

variable {N : ℕ}

theorem increment_inequality (lam : ℝ) (M : ℤ) (y : Fin N → ℝ)
    (n : Fin N → ℤ) (hn : isMinimum lam M y n) (hslack : ∑ j,n j < M) (i : Fin N) :
    0 ≤ 2*((n i : ℝ)-y i)+1-lam*(2*((M : ℝ)-∑ j,(n j : ℝ))-1) := by
  have hz : RematGeneral.feasible M (Function.update n i (n i+1)) := by
    constructor
    · intro j
      by_cases hji : j = i
      · subst j
        simpa using add_nonneg (hn.1.1 i) (show (0 : ℤ) ≤ 1 by omega)
      · simpa [Function.update_of_ne hji] using hn.1.1 j
    · rw [RematGeneral.sum_update]
      omega
  have hm := hn.2 _ hz
  unfold loss at hm
  rw [RematGeneral.loss_update,RematGeneral.sum_update] at hm
  push_cast at hm
  nlinarith

theorem equality_forces_uniform_fractions (hN : 2 ≤ N) (M : ℤ) (y : Fin N → ℝ)
    (hs : ∑ i,y i = (M : ℝ)) (n : Fin N → ℤ)
    (hn : isMinimum (1-2/(N : ℝ)) M y n) (hslack : 0 < M-∑ i,n i) :
    RematRounding.capacity M y = 1 ∧ ∀ i, RematRounding.fraction y i = 1/(N : ℝ) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNP : (0 : ℝ) < N := by linarith
  let s : ℝ := (M : ℝ)-∑ i,(n i : ℝ)
  have hs1 : 1 ≤ s := by
    dsimp [s]
    exact_mod_cast (show (1 : ℤ) ≤ M-∑ i,n i by omega)
  let D : Fin N → ℝ := fun i => 2*((n i : ℝ)-y i)+1-(1-2/(N : ℝ))*(2*s-1)
  have hD : ∀ i, 0 ≤ D i := fun i => increment_inequality _ M y n hn (by omega) i
  have hsumD : ∑ i,D i = 2*((N : ℝ)-1)*(1-s) := by
    dsimp [D]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hs]
    dsimp [s]
    field_simp
    ring
  have hnonneg : 0 ≤ 2*((N : ℝ)-1)*(1-s) := by
    rw [← hsumD]
    exact Finset.sum_nonneg (fun i _ => hD i)
  have hres : 0 ≤ 1-s := by
    by_contra hbad
    have hneg := mul_neg_of_pos_of_neg (show (0 : ℝ) < 2*((N : ℝ)-1) by linarith) (lt_of_not_ge hbad)
    linarith
  have hsEq : s = 1 := by linarith
  have hsumZero : ∑ i,D i = 0 := by rw [hsumD,hsEq]; ring
  have hDz : ∀ i, D i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hD j)).mp hsumZero i (Finset.mem_univ i)
  have hdiff (i : Fin N) : y i - (n i : ℝ) = 1/(N : ℝ) := by
    have h := hDz i
    dsimp [D] at h
    rw [hsEq] at h
    simp only [div_eq_mul_inv,one_mul] at h ⊢
    nlinarith
  have hfrac : ∀ i, RematRounding.fraction y i = 1/(N : ℝ) := by
    intro i
    have hfloor : ⌊y i⌋ = n i := by
      apply Int.floor_eq_iff.mpr
      have hp : 0 < (1 : ℝ)/N := one_div_pos.mpr hNP
      have hu : (1 : ℝ)/N < 1 := (div_lt_one hNP).mpr (by linarith)
      constructor <;> linarith [hdiff i]
    change y i - (⌊y i⌋ : ℝ) = 1/(N : ℝ)
    rw [hfloor]
    exact hdiff i
  refine ⟨?_,hfrac⟩
  have hc := RematRounding.fraction_sum M y hs
  simp_rw [hfrac] at hc
  have hkReal : (RematRounding.capacity M y : ℝ) = 1 := by
    simpa [ne_of_gt hNP] using hc.symm
  exact_mod_cast hkReal

theorem equality_coexistence_iff (hN : 2 ≤ N) (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i,0 ≤ y i) (hs : ∑ i,y i = (M : ℝ)) :
    ((∃ n, isMinimum (1-2/(N : ℝ)) M y n ∧ ∑ i,n i = M) ∧
      (∃ n, isMinimum (1-2/(N : ℝ)) M y n ∧ 0 < M-∑ i,n i)) ↔
      RematRounding.capacity M y = 1 ∧ ∀ i,RematRounding.fraction y i = 1/(N : ℝ) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNP : (0 : ℝ) < N := by linarith
  have hlam : 0 ≤ 1-2/(N : ℝ) := by
    have hdiv : (2 : ℝ)/N ≤ 1 := (div_le_one hNP).mpr hNR
    linarith
  constructor
  · rintro ⟨_,n,hn,hslack⟩
    exact equality_forces_uniform_fractions hN M y hs n hn hslack
  · rintro ⟨hk,hf⟩
    have hkpos : 0 < RematRounding.capacity M y := by omega
    have hc (i : Fin N) : RematRounding.benefit y i = 1-2/(N : ℝ) := by
      simp [RematRounding.benefit,hf,div_eq_mul_inv]
    have hmono : Monotone (fun i => RematRounding.benefit y ((Equiv.refl (Fin N)) i)) := by
      intro i j _
      simp only [Equiv.refl_apply,hc]
      exact le_refl _
    have hth : threshold M y hs hkpos (Equiv.refl (Fin N)) = 1-2/(N : ℝ) := by
      unfold threshold RematPenaltySelection.lastCost
      exact hc _
    exact (exact_identification_threshold _ hlam M y hy hs hkpos (Equiv.refl (Fin N)) hmono).2.2.2.mpr hth.symm

theorem equality_otherwise_saturated (hN : 2 ≤ N) (M : ℤ) (y : Fin N → ℝ)
    (hs : ∑ i,y i = (M : ℝ))
    (hnot : ¬(RematRounding.capacity M y = 1 ∧ ∀ i,RematRounding.fraction y i = 1/(N : ℝ)))
    (n : Fin N → ℤ) (hn : isMinimum (1-2/(N : ℝ)) M y n) : ∑ i,n i = M := by
  by_contra he
  have hslack : 0 < M-∑ i,n i := by have := hn.1.2; omega
  exact hnot (equality_forces_uniform_fractions hN M y hs n hn hslack)


end

end RematPenalty

namespace RematProbability

open Finset

variable {N : ℕ}

theorem embedding_affine (t : ℝ) (d e : Fin N → ℝ) :
    embed (fun i => t*d i+(1-t)*e i) =
      (fun i => t*embed d i+(1-t)*embed e i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [embed_residual,Finset.sum_add_distrib,← Finset.mul_sum]
    ring
  · simp only [embed_lexical]

theorem target_embedding (a : Fin N → ℝ) (hs : ∑ i,a i = 1) :
    embed a = Fin.snoc a 0 := by simp [embed,hs]


end RematProbability

namespace RematPenalty

open Finset

variable {N : ℕ}

theorem zero_capacity_target_integral (M : ℤ) (y : Fin N → ℝ)
    (hs : ∑ i,y i = (M : ℝ)) (hk : RematRounding.capacity M y = 0) :
    ∀ i,y i = (RematRounding.base y i : ℝ) := by
  have hsum : ∑ i,RematRounding.fraction y i = 0 := by
    rw [RematRounding.fraction_sum M y hs,hk]
    norm_num
  have hf (i : Fin N) : RematRounding.fraction y i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (RematRounding.fraction_bounds y j).1)).mp hsum i
      (Finset.mem_univ i)
  intro i
  have h := hf i
  dsimp [RematRounding.fraction] at h
  linarith


end RematPenalty

namespace RematPenaltySelection

noncomputable section

open Finset

variable {N : ℕ}

def difference (F : ℕ → ℝ) (k : ℕ) (i : Fin k) : ℝ := F (i.val+1)-F i.val

theorem difference_sum (F : ℕ → ℝ) (k m : ℕ) (hm : m ≤ k) :
    RematSelection.cost (difference F k) (firstSet (Equiv.refl (Fin k)) m) = F m-F 0 := by
  induction m with
  | zero => simp [firstSet,initial,RematSelection.cost]
  | succ m ih =>
    have hmk : m < k := by omega
    have hnot : (⟨m,hmk⟩ : Fin k) ∉ firstSet (Equiv.refl (Fin k)) m := by simp [mem_prefix]
    rw [prefix_succ _ m hmk]
    change RematSelection.cost (difference F k) (insert ⟨m,hmk⟩ (firstSet (Equiv.refl (Fin k)) m)) = _
    simp only [RematSelection.cost,Finset.sum_insert hnot]
    change difference F k ⟨m,hmk⟩ + RematSelection.cost (difference F k) (firstSet (Equiv.refl (Fin k)) m) = _
    rw [ih (by omega)]
    dsimp [difference]
    ring

theorem scalar_minimum_iff_prefix (F : ℕ → ℝ) (k m : ℕ) (hm : m ≤ k)
    (hmono : Monotone (difference F k)) :
    (∀ r : ℕ, r ≤ k → F m ≤ F r) ↔
      RematSelection.minimum (difference F k) k (firstSet (Equiv.refl (Fin k)) m) := by
  constructor
  · intro hmin
    refine ⟨by rw [prefix_card _ m hm]; exact hm,fun E hE => ?_⟩
    have hcut := prefix_cutoff (difference F k) (Equiv.refl (Fin k)) hmono E.card
    have hb := (fixed_cardinality_iff _ _).mpr hcut E (prefix_card _ E.card hE).symm
    rw [difference_sum F k E.card hE] at hb
    rw [difference_sum F k m hm]
    linarith [hmin E.card hE]
  · intro hmin r hr
    have hh := hmin.2 (firstSet (Equiv.refl (Fin k)) r) (by rw [prefix_card _ r hr]; exact hr)
    rw [difference_sum F k m hm,difference_sum F k r hr] at hh
    linarith

theorem minimum_cardinality_iff_scalar (F : ℕ → ℝ) (k m : ℕ) (hm : m ≤ k)
    (hmono : Monotone (difference F k)) :
    (∀ r : ℕ, r ≤ k → F m ≤ F r) ↔
      ∃ E, RematSelection.minimum (difference F k) k E ∧ E.card = m := by
  rw [scalar_minimum_iff_prefix F k m hm hmono]
  constructor
  · intro h
    exact ⟨_,h,prefix_card _ m hm⟩
  · rintro ⟨E,hE,hcard⟩
    have hb := (fixed_cardinality_iff _ _).mpr
      (prefix_cutoff (difference F k) (Equiv.refl (Fin k)) hmono m) E
      (by rw [prefix_card _ m hm,hcard])
    exact ⟨by rw [prefix_card _ m hm]; exact hm,fun Z hZ => hb.trans (hE.2 Z hZ)⟩

theorem convex_scalar_cardinality_interval (F : ℕ → ℝ) (k m : ℕ) (hm : m ≤ k)
    (hmono : Monotone (difference F k)) :
    (∀ r : ℕ, r ≤ k → F m ≤ F r) ↔
      (RematSelection.negative (difference F k)).card ≤ m ∧
      m ≤ (Finset.univ.filter (fun i : Fin k => difference F k i ≤ 0)).card := by
  classical
  let c := difference F k
  have hb : (RematSelection.negative c).card ≤ k := by
    simpa using (RematSelection.negative c).card_le_univ
  have hU : RematSelection.negative c ∪ RematSelection.zero c =
      Finset.univ.filter (fun i : Fin k => c i ≤ 0) := by
    ext i
    simp only [RematSelection.negative,RematSelection.zero,Finset.mem_union,
      Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro (h | h)
      · exact h.le
      · exact h.le
    · exact lt_or_eq_of_le
  have hcard : (Finset.univ.filter (fun i : Fin k => c i ≤ 0)).card =
      (RematSelection.negative c).card + (RematSelection.zero c).card := by
    rw [← hU,Finset.card_union_of_disjoint (RematSelection.negative_zero_disjoint c)]
  have htot : (RematSelection.negative c).card + (RematSelection.zero c).card ≤ k := by
    rw [← hcard]
    simpa using (Finset.univ.filter (fun i : Fin k => c i ≤ 0)).card_le_univ
  rw [minimum_cardinality_iff_scalar F k m hm hmono]
  change (∃ E,RematSelection.minimum c k E ∧ E.card=m) ↔ _
  rw [RematSelection.minimum_cardinality_iff c k m hb]
  change _ ↔ (RematSelection.negative c).card ≤ m ∧
    m ≤ (Finset.univ.filter (fun i : Fin k => c i ≤ 0)).card
  rw [hcard]
  constructor
  · rintro ⟨s,hs,he⟩
    have hsz := hs.trans (min_le_left _ _)
    omega
  · rintro ⟨hlo,hhi⟩
    refine ⟨m-(RematSelection.negative c).card,?_,by omega⟩
    apply le_min <;> omega

theorem penalty_difference_monotone (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (hk : k ≤ N)
    (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (hc : Monotone (fun i => c (σ i))) :
    Monotone (difference (scalar lam k c σ) k) := by
  intro i j hij
  have hiN : i.val < N := i.isLt.trans_le hk
  have hjN : j.val < N := j.isLt.trans_le hk
  dsimp [difference]
  rw [scalar_increment lam k c σ i.val hiN,scalar_increment lam k c σ j.val hjN]
  have hval : i.val ≤ j.val := hij
  have hcr := hc (show (⟨i.val,hiN⟩ : Fin N) ≤ ⟨j.val,hjN⟩ from hval)
  have hreal : (i.val : ℝ) ≤ j.val := by exact_mod_cast hval
  have hp := mul_le_mul_of_nonneg_left hreal hlam
  nlinarith

theorem penalty_cardinality_interval (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (hk : k ≤ N)
    (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (hc : Monotone (fun i => c (σ i)))
    (m : ℕ) (hm : m ≤ k) :
    (∀ r : ℕ,r ≤ k → scalar lam k c σ m ≤ scalar lam k c σ r) ↔
      (Finset.univ.filter (fun i : Fin k => scalar lam k c σ (i.val+1)-scalar lam k c σ i.val < 0)).card ≤ m ∧
      m ≤ (Finset.univ.filter (fun i : Fin k => scalar lam k c σ (i.val+1)-scalar lam k c σ i.val ≤ 0)).card := by
  exact convex_scalar_cardinality_interval _ k m hm (penalty_difference_monotone lam hlam k hk c σ hc)

theorem positive_penalty_at_most_two_cardinalities (lam : ℝ) (hlam : 0 < lam)
    (k : ℕ) (hk : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) (m r : ℕ) (hm : m ≤ k) (hr : r ≤ k)
    (hminm : ∀ t : ℕ,t ≤ k → scalar lam k c σ m ≤ scalar lam k c σ t)
    (hminr : ∀ t : ℕ,t ≤ k → scalar lam k c σ r ≤ scalar lam k c σ t) :
    m ≤ r+1 ∧ r ≤ m+1 := by
  have one_direction (a b : ℕ) (ha : a ≤ k) (hb : b ≤ k)
      (hmina : ∀ t : ℕ,t ≤ k → scalar lam k c σ a ≤ scalar lam k c σ t)
      (hminb : ∀ t : ℕ,t ≤ k → scalar lam k c σ b ≤ scalar lam k c σ t) : b ≤ a+1 := by
    by_contra hbad
    have haN : a < N := by omega
    have hbN : b-1 < N := by omega
    have hleft := hmina (a+1) (by omega)
    have hright := hminb (b-1) (by omega)
    have hd1 := scalar_increment lam k c σ a haN
    have hd2 := scalar_increment lam k c σ (b-1) hbN
    have hsucc : b-1+1=b := by omega
    rw [hsucc] at hd2
    have hcr := hc (show (⟨a,haN⟩ : Fin N) ≤ ⟨b-1,hbN⟩ by exact_mod_cast (show a ≤ b-1 by omega))
    have hreal : (a : ℝ) < (b-1 : ℕ) := by exact_mod_cast (show a < b-1 by omega)
    have hp := mul_pos hlam (sub_pos.mpr hreal)
    nlinarith
  exact ⟨one_direction r m hr hm hminr hminm,one_direction m r hm hr hminm hminr⟩


end

end RematPenaltySelection

namespace RematAudit

theorem doubled_target_not_feasible (j : ℕ) :
    ¬ RematGrid.feasible ((2*11^j : ℕ) : ℤ) RematRefinement.target := by
  intro hf
  have hm : RematGrid.isMinimum ((2*11^j : ℕ) : ℤ) RematRefinement.target RematRefinement.target := by
    refine ⟨hf,?_⟩
    intro e he
    have hz : RematGrid.loss RematRefinement.target RematRefinement.target = 0 := by
      simp [RematGrid.loss]
    rw [hz]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hh := RematRefinement.doubled_eleven_permanent_identification j
  exact hh.2.2.2 ((hh.1 RematRefinement.target).mp hm).symm

theorem power_eventually_above (b : ℕ) (hb : 2 ≤ b) :
    ∀ B : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → B < b^j := by
  have hpow (j : ℕ) : j < b^j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      have hp : 0 < b^j := pow_pos (by omega) _
      nlinarith
  intro B
  exact ⟨B,fun j hj => lt_of_le_of_lt hj (hpow j)⟩

theorem all_three_eventually_above :
    (∀ B : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → B < 11^j) ∧
    (∀ B : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → B < 2*11^j) ∧
    (∀ B : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → B < 3^j) := by
  refine ⟨power_eventually_above 11 (by norm_num),?_,power_eventually_above 3 (by norm_num)⟩
  intro B
  obtain ⟨J,hJ⟩ := power_eventually_above 11 (by norm_num) B
  exact ⟨J,fun j hj => by have hh := hJ j hj; omega⟩

theorem doubled_lexical_positive (j : ℕ) (hj : 1 ≤ j) (i : Fin 4) :
    0 < RematRefinement.representative (2*11^j) i := by
  have hbound : 22 ≤ 2*(11 : ℕ)^j := by
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      rw [pow_succ]
      omega
  have hq : 1 ≤ (2*(11 : ℕ)^j)/10 := by omega
  have hn := RematRefinement.residue_point_lower ((2*(11 : ℕ)^j)/10)
    ⟨(2*11^j)%10,Nat.mod_lt _ (by norm_num)⟩ i
  have hpos : (0 : ℤ) < GridResidueCertificate.residuePoint ((2*(11 : ℕ)^j)/10)
      ⟨(2*11^j)%10,Nat.mod_lt _ (by norm_num)⟩ i := by omega
  unfold RematRefinement.representative RematGrid.point
  exact div_pos (by exact_mod_cast hpos) (by positivity)

theorem nonzero_support_eq_positive {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i,0 ≤ p i) :
    {i | p i ≠ 0} = {i | 0 < p i} := by
  ext i
  exact ⟨fun h => lt_of_le_of_ne (hp i) (Ne.symm h),fun h => ne_of_gt h⟩

end RematAudit

#print axioms integer_nearest
#print axioms integer_nearest_strict
#print axioms four_rounding_interior
#print axioms four_global_minimum
#print axioms four_unique_minimum
#print axioms four_grid_nonnegative
#print axioms four_grid_slack
#print axioms four_exact_loss
#print axioms four_completed_square
#print axioms GridResidueCertificate.nearest_integer
#print axioms GridResidueCertificate.nearest_integer_strict
#print axioms GridResidueCertificate.shifted_loss_difference
#print axioms GridResidueCertificate.multiplier_certificate
#print axioms GridResidueCertificate.strict_multiplier_certificate
#print axioms GridResidueCertificate.residue_feasible
#print axioms GridResidueCertificate.residue_multiplier_nonnegative
#print axioms GridResidueCertificate.residue_complementarity
#print axioms GridResidueCertificate.residue_rounding
#print axioms GridResidueCertificate.residue_rounding_strict
#print axioms GridResidueCertificate.residue_global_minimum
#print axioms GridResidueCertificate.residue_unique_minimum
#print axioms GridResidueCertificate.residue_slack
#print axioms GridResidueCertificate.residue_exact_loss
#print axioms GridResidueCertificate.adjacent_product_nonnegative
#print axioms GridResidueCertificate.half_point_one_feasible
#print axioms GridResidueCertificate.half_point_two_feasible
#print axioms GridResidueCertificate.half_point_one_loss
#print axioms GridResidueCertificate.half_point_two_loss
#print axioms GridResidueCertificate.residue_five_complete
#print axioms four_energy_loss
#print axioms four_energy_unique
#print axioms four_energy_gap
#print axioms four_terminal_value
#print axioms four_terminal_positive
#print axioms eleven_mesh_form
#print axioms eleven_mesh_nested
#print axioms ternary_residue_zero
#print axioms ternary_residue_one
#print axioms ternary_residue_two
#print axioms ternary_residue_three
#print axioms ternary_mesh_nested
#print axioms RematGeneral.sum_update
#print axioms RematGeneral.loss_update
#print axioms RematGeneral.coordinate_upper
#print axioms RematGeneral.coordinate_lower
#print axioms RematGeneral.coordinate_proximity
#print axioms RematGeneral.minimum_exists
#print axioms RematGeneral.loss_translation
#print axioms RematGeneral.feasible_translation
#print axioms RematGeneral.minimum_translation_down
#print axioms RematGeneral.minimum_translation_iff
#print axioms RematGeneral.rational_residue_reduction
#print axioms RematGeneral.rational_residue_slack
#print axioms RematGeneral.scaled_loss_identity
#print axioms RematGeneral.rational_residue_loss
#print axioms RematSelection.cost_terms
#print axioms RematSelection.negative_lower
#print axioms RematSelection.cost_eq_negative_iff
#print axioms RematSelection.minimum_iff_when_negative_fits
#print axioms RematSelection.negative_minimum
#print axioms RematSelection.saturated_when_many_negative
#print axioms RematSelection.selected_before_unselected
#print axioms RematSelection.negative_zero_disjoint
#print axioms RematSelection.zero_subset_minimum
#print axioms RematSelection.minimum_cardinality_exists
#print axioms RematSelection.minimum_cardinality_iff
#print axioms RematSelection.some_slack_iff
#print axioms RematSelection.minimum_exists
#print axioms RematSelection.all_slack_iff
#print axioms RematSelection.unique_minimum_with_slack_iff
#print axioms RematSelection.cost_shift
#print axioms RematSelection.minimum_iff_when_many_negative
#print axioms RematRounding.fraction_bounds
#print axioms RematRounding.capacity_cast
#print axioms RematRounding.fraction_sum
#print axioms RematRounding.rounded_sum
#print axioms RematRounding.rounded_slack
#print axioms RematRounding.rounded_loss
#print axioms RematRounding.base_loss
#print axioms RematRounding.rounded_feasible_iff
#print axioms RematRounding.rounded_injective
#print axioms RematRounding.minimum_rounded_representation
#print axioms RematRounding.rounded_minimum_iff
#print axioms RematRounding.all_integer_minima_iff
#print axioms RematRounding.negative_is_above_half
#print axioms RematRounding.zero_is_half
#print axioms RematRounding.highCount_eq_negative
#print axioms RematRounding.tieCount_eq_zero
#print axioms RematRounding.positive_slack_iff
#print axioms RematRounding.all_positive_slack_iff
#print axioms RematRounding.unique_global_minimum_with_slack_iff
#print axioms RematRounding.exact_slack_image
#print axioms RematRounding.saturated_classification
#print axioms RematRounding.unsaturated_classification
#print axioms RematGrid.point_sum
#print axioms RematGrid.point_injective
#print axioms RematGrid.point_feasible_iff
#print axioms RematGrid.loss_scaling
#print axioms RematGrid.minimum_point_iff
#print axioms RematGrid.minimum_iff_exists_integer
#print axioms RematGrid.slack_identity
#print axioms RematGrid.slack_positive_iff
#print axioms RematGrid.scaled_target_hypotheses
#print axioms RematPenalty.minimum_exists
#print axioms RematPenalty.coordinate_lower
#print axioms RematPenalty.coordinate_upper
#print axioms RematPenalty.coordinate_proximity
#print axioms RematPenalty.loss_translation
#print axioms RematPenalty.minimum_translation_down
#print axioms RematPenalty.minimum_translation_iff
#print axioms RematPenalty.rational_residue_reduction
#print axioms RematProbability.embed_lexical
#print axioms RematProbability.embed_residual
#print axioms RematProbability.embed_simplex_iff
#print axioms RematProbability.embed_injective
#print axioms RematProbability.simplex_inverse
#print axioms RematProbability.residual_support_iff
#print axioms RematProbability.full_euclidean_identity
#print axioms RematProbability.grid_embedding
#print axioms RematProbability.penalty_loss_identity
#print axioms RematProbability.zero_target_coordinate
#print axioms RematProbability.positive_target_coordinate
#print axioms RematPenaltySelection.fixed_cardinality_iff
#print axioms RematPenaltySelection.initial_card
#print axioms RematPenaltySelection.prefix_card
#print axioms RematPenaltySelection.mem_prefix
#print axioms RematPenaltySelection.prefix_cutoff
#print axioms RematPenaltySelection.cost_prefix
#print axioms RematPenaltySelection.cutoff_cost
#print axioms RematPenaltySelection.scalar_classification
#print axioms RematPenaltySelection.prefix_succ
#print axioms RematPenaltySelection.scalar_increment
#print axioms RematPenalty.minimum_rounded_representation
#print axioms RematPenalty.rounded_loss
#print axioms RematPenalty.rounded_minimum_iff
#print axioms RematPenalty.all_integer_minima_iff
#print axioms RematPenalty.capacity_le_dimension
#print axioms RematPenalty.all_minimizer_scalar_classification
#print axioms RematPenaltySelection.increment_le_last
#print axioms RematPenaltySelection.scalar_last_le
#print axioms RematPenaltySelection.scalar_last_lt
#print axioms RematPenaltySelection.scalar_last_increment
#print axioms RematPenaltySelection.saturated_minimum_iff
#print axioms RematPenaltySelection.minimum_exists
#print axioms RematPenaltySelection.last_two_tie
#print axioms RematPenaltySelection.all_saturated_iff
#print axioms RematPenaltySelection.all_unsaturated_iff
#print axioms RematPenaltySelection.coexistence_iff
#print axioms RematPenalty.saturated_exists_iff_selection
#print axioms RematPenalty.all_saturated_iff_selection
#print axioms RematPenalty.positive_slack_exists_iff_selection
#print axioms RematPenalty.all_positive_slack_iff_selection
#print axioms RematPenalty.exact_identification_threshold
#print axioms RematPenalty.zero_capacity_unique_minimum
#print axioms RematPenalty.uniform_identification
#print axioms RematPenalty.unit_sum
#print axioms RematPenalty.unit_feasible
#print axioms RematPenalty.capacity_one_feasible_iff
#print axioms RematPenalty.zero_loss
#print axioms RematPenalty.unit_loss
#print axioms RematPenalty.capacity_one_minimum_iff
#print axioms RematPenalty.uniform_sharpness_family
#print axioms RematRefinement.integer_residue_minimum_iff
#print axioms RematRefinement.real_residue_minimum_iff
#print axioms RematRefinement.mesh_minimum_iff
#print axioms RematRefinement.representative_slack
#print axioms RematRefinement.representative_loss
#print axioms RematRefinement.eleven_permanent_failure
#print axioms RematRefinement.doubled_eleven_permanent_identification
#print axioms RematRefinement.ternary_residue_classification
#print axioms RematRefinement.ternary_alternating_identification
#print axioms RematRefinement.three_refinement_regimes
#print axioms RematPenalty.four_capacity_one_minimum_iff
#print axioms RematPenalty.four_penalty_transition
#print axioms RematPenalty.four_penalty_errors
#print axioms RematPenalty.eleven_positive_penalty_failure
#print axioms RematPenaltyGrid.loss_scaling
#print axioms RematPenaltyGrid.minimum_point_iff
#print axioms RematPenaltyGrid.minimum_iff_exists_integer
#print axioms RematProbability.grid_embedding_iff
#print axioms RematProbability.lexical_support_preserved
#print axioms RematProbability.full_support_iff_saturated
#print axioms RematRefinement.grid_multiply_nested
#print axioms RematRefinement.eleven_nested
#print axioms RematRefinement.doubled_eleven_nested
#print axioms RematRefinement.ternary_nested
#print axioms RematRefinement.power_unbounded
#print axioms RematRefinement.doubled_eleven_unbounded
#print axioms RematRefinement.ternary_infinitely_many_each
#print axioms RematRefinement.nested_unbounded_refinements
#print axioms RematPenaltyGrid.uniform_identification
#print axioms RematPenaltyGrid.full_euclidean_identification
#print axioms RematRefinement.residue_point_lower
#print axioms RematRefinement.ternary_lexical_positive
#print axioms RematRefinement.exact_target_control
#print axioms RematPenalty.zero_penalty_minimum_iff
#print axioms RematPenaltySelection.sorted_permutation_exists
#print axioms RematPenalty.increment_inequality
#print axioms RematPenalty.equality_forces_uniform_fractions
#print axioms RematPenalty.equality_coexistence_iff
#print axioms RematPenalty.equality_otherwise_saturated
#print axioms RematProbability.embedding_affine
#print axioms RematProbability.target_embedding
#print axioms RematPenalty.zero_capacity_target_integral
#print axioms RematPenaltySelection.difference_sum
#print axioms RematPenaltySelection.scalar_minimum_iff_prefix
#print axioms RematPenaltySelection.minimum_cardinality_iff_scalar
#print axioms RematPenaltySelection.convex_scalar_cardinality_interval
#print axioms RematPenaltySelection.penalty_difference_monotone
#print axioms RematPenaltySelection.penalty_cardinality_interval
#print axioms RematPenaltySelection.positive_penalty_at_most_two_cardinalities

#print axioms RematAudit.doubled_target_not_feasible
#print axioms RematAudit.power_eventually_above
#print axioms RematAudit.all_three_eventually_above
#print axioms RematAudit.doubled_lexical_positive
#print axioms RematAudit.nonzero_support_eq_positive

namespace RematGeneralResidual

noncomputable section

open Finset

variable {N : ℕ}

def loss (G : ℤ → ℝ) (M : ℤ) (y : Fin N → ℝ) (n : Fin N → ℤ) : ℝ :=
  RematGeneral.loss y n + G (M - ∑ i, n i)

def isMinimum (G : ℤ → ℝ) (M : ℤ) (y : Fin N → ℝ) (n : Fin N → ℤ) : Prop :=
  RematGeneral.feasible M n ∧ ∀ z, RematGeneral.feasible M z → loss G M y n ≤ loss G M y z

theorem minimum_exists (G : ℤ → ℝ) (M : ℤ) (hM : 0 ≤ M) (y : Fin N → ℝ) :
    ∃ n, isMinimum G M y n := by
  classical
  let candidates := (Fintype.piFinset (fun _ : Fin N => Finset.Icc (0 : ℤ) M)).filter
    (fun n => ∑ i, n i ≤ M)
  have mem_iff (n : Fin N → ℤ) : n ∈ candidates ↔ RematGeneral.feasible M n := by
    simp only [candidates, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc,
      RematGeneral.feasible]
    constructor
    · intro h
      exact ⟨fun i => (h.1 i).1, h.2⟩
    · intro h
      refine ⟨?_, h.2⟩
      intro i
      exact ⟨h.1 i, (Finset.single_le_sum (fun j _ => h.1 j) (Finset.mem_univ i)).trans h.2⟩
  have hne : candidates.Nonempty := by
    refine ⟨fun _ => 0, (mem_iff _).mpr ⟨fun _ => le_refl _, ?_⟩⟩
    simpa using hM
  obtain ⟨n, hn, hmin⟩ := candidates.exists_min_image (loss G M y) hne
  exact ⟨n, (mem_iff n).mp hn, fun z hz => hmin z ((mem_iff z).mpr hz)⟩

theorem coordinate_lower (G : ℤ → ℝ) (M : ℤ) (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (n : Fin N → ℤ) (hn : isMinimum G M y n) (i : Fin N) : ⌊y i⌋ ≤ n i := by
  by_contra hi
  have hni : n i < ⌊y i⌋ := by omega
  have hyi : (n i : ℝ) + 1 ≤ y i := Int.lt_floor_iff.mp hni
  by_cases hslack : ∑ j, n j < M
  · have hz : RematGeneral.feasible M (Function.update n i (n i + 1)) := by
      constructor
      · intro j
        by_cases hji : j = i
        · subst j
          simpa using add_nonneg (hn.1.1 i) (show (0 : ℤ) ≤ 1 by omega)
        · simpa [Function.update_of_ne hji] using hn.1.1 j
      · rw [RematGeneral.sum_update]
        omega
    have hmin := hn.2 _ hz
    unfold loss at hmin
    rw [RematGeneral.loss_update, RematGeneral.sum_update] at hmin
    have hnnonneg : 0 ≤ ∑ j, n j := Finset.sum_nonneg (fun j _ => hn.1.1 j)
    have hp : G (M - ∑ j, n j - 1) ≤ G (M - ∑ j, n j) :=
      hG _ _ (by omega) (by omega) (by omega)
    have he : M - ((∑ j, n j) + (n i + 1) - n i) = M - ∑ j, n j - 1 := by ring
    rw [he] at hmin
    push_cast at hmin
    nlinarith
  · have heq : ∑ j, n j = M := le_antisymm hn.1.2 (by omega)
    have heqreal : ∑ j, (n j : ℝ) = (M : ℝ) := by exact_mod_cast heq
    have hex : ∃ j, y j < (n j : ℝ) := by
      by_contra h
      push Not at h
      have hlt : ∑ j, (n j : ℝ) < ∑ j, y j := by
        apply Finset.sum_lt_sum
        · intro j _
          exact h j
        · exact ⟨i, Finset.mem_univ i, by linarith⟩
      linarith
    obtain ⟨j, hj⟩ := hex
    have hji : j ≠ i := by intro h; subst j; linarith
    have hjpos : 0 < n j := by exact_mod_cast lt_of_le_of_lt (hy j) hj
    let z := Function.update (Function.update n j (n j - 1)) i (n i + 1)
    have hzsum : ∑ k, z k = ∑ k, n k := by
      dsimp [z]
      rw [RematGeneral.sum_update, RematGeneral.sum_update]
      simp only [Function.update_of_ne (Ne.symm hji)]
      omega
    have hz : RematGeneral.feasible M z := by
      constructor
      · intro k
        by_cases hki : k = i
        · subst k
          simp [z]
          have := hn.1.1 i
          omega
        · by_cases hkj : k = j
          · subst k
            simp [z, Function.update_of_ne hji]
            omega
          · simpa [z, Function.update_of_ne hki, Function.update_of_ne hkj] using hn.1.1 k
      · rw [hzsum]
        exact hn.1.2
    have hmin := hn.2 z hz
    unfold loss at hmin
    rw [hzsum] at hmin
    dsimp [z] at hmin
    rw [RematGeneral.loss_update, RematGeneral.loss_update] at hmin
    simp only [Function.update_of_ne (Ne.symm hji)] at hmin
    push_cast at hmin
    nlinarith

theorem coordinate_upper (G : ℤ → ℝ) (M : ℤ) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (n : Fin N → ℤ) (hn : isMinimum G M y n) (i : Fin N) : n i ≤ ⌈y i⌉ := by
  by_contra hi
  have hni : ⌈y i⌉ < n i := by omega
  have hyi : y i ≤ (n i : ℝ) - 1 := Int.ceil_lt_iff.mp hni
  have hipos : 0 < n i := by
    have hr : (0 : ℝ) < n i := by linarith [hy i]
    exact_mod_cast hr
  have hncap : ∑ j, (n j : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn.1.2
  have hex : ∃ j, (n j : ℝ) < y j := by
    by_contra h
    push Not at h
    have hlt : ∑ j, y j < ∑ j, (n j : ℝ) := by
      apply Finset.sum_lt_sum
      · intro j _
        exact h j
      · exact ⟨i, Finset.mem_univ i, by linarith⟩
    linarith
  obtain ⟨j, hj⟩ := hex
  have hji : j ≠ i := by intro h; subst j; linarith
  let z := Function.update (Function.update n i (n i - 1)) j (n j + 1)
  have hzsum : ∑ k, z k = ∑ k, n k := by
    dsimp [z]
    rw [RematGeneral.sum_update, RematGeneral.sum_update]
    simp only [Function.update_of_ne hji]
    omega
  have hz : RematGeneral.feasible M z := by
    constructor
    · intro k
      by_cases hkj : k = j
      · subst k
        simp [z]
        have := hn.1.1 j
        omega
      · by_cases hki : k = i
        · subst k
          simp [z, Function.update_of_ne (Ne.symm hji)]
          omega
        · simpa [z, Function.update_of_ne hki, Function.update_of_ne hkj] using hn.1.1 k
    · rw [hzsum]
      exact hn.1.2
  have hmin := hn.2 z hz
  unfold loss at hmin
  rw [hzsum] at hmin
  dsimp [z] at hmin
  rw [RematGeneral.loss_update, RematGeneral.loss_update] at hmin
  simp only [Function.update_of_ne hji] at hmin
  push_cast at hmin
  nlinarith

theorem coordinate_proximity (G : ℤ → ℝ) (M : ℤ) (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b) (y : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (n : Fin N → ℤ) (hn : isMinimum G M y n) :
    ∀ i, ⌊y i⌋ ≤ n i ∧ n i ≤ ⌈y i⌉ := by
  intro i
  exact ⟨coordinate_lower G M hG y hy hs n hn i, coordinate_upper G M y hy hs n hn i⟩


theorem minimum_rounded_representation (G : ℤ → ℝ) (M : ℤ)
    (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (n : Fin N → ℤ) (hn : isMinimum G M y n) :
    n = RematRounding.rounded y (RematRounding.selected y n) := by
  classical
  funext i
  obtain ⟨hlo,hhi⟩ := coordinate_proximity G M hG y hy hs n hn i
  have hceil := Int.ceil_le_floor_add_one (y i)
  by_cases h : RematRounding.base y i < n i
  · simp [RematRounding.rounded,RematRounding.selected,h]
    dsimp [RematRounding.base] at h ⊢
    omega
  · simp [RematRounding.rounded,RematRounding.selected,h]
    dsimp [RematRounding.base] at h ⊢
    omega

theorem capacity_one_loss (G : ℤ → ℝ) (M : ℤ) (y : Fin N → ℝ)
    (hs : ∑ i, y i = (M : ℝ)) (hk : RematRounding.capacity M y = 1)
    (E : Finset (Fin N)) (hE : RematGeneral.feasible M (RematRounding.rounded y E)) :
    loss G M y (RematRounding.rounded y E) =
      RematPenalty.loss (G 1-G 0) M y (RematRounding.rounded y E) + G 0 := by
  have hcap := RematRounding.capacity_cast M y hs
  rw [hk] at hcap
  have hsum := RematRounding.rounded_sum y E
  have hslack : M - ∑ i, RematRounding.rounded y E i = 0 ∨
      M - ∑ i, RematRounding.rounded y E i = 1 := by
    have hcard : (0 : ℤ) ≤ E.card := by exact_mod_cast Nat.zero_le E.card
    have hfeas := hE.2
    norm_num at hcap
    omega
  rcases hslack with hz | ho
  · simp [loss,RematPenalty.loss,hz]
  · simp [loss,RematPenalty.loss,ho]
    ring

theorem capacity_one_minimum_iff_quadratic (G : ℤ → ℝ) (M : ℤ)
    (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (hk : RematRounding.capacity M y = 1) (n : Fin N → ℤ) :
    isMinimum G M y n ↔ RematPenalty.isMinimum (G 1-G 0) M y n := by
  have hMpos : 1 ≤ M := by
    have hc := RematRounding.capacity_cast M y hs
    rw [hk] at hc
    have hb : 0 ≤ ∑ i, RematRounding.base y i :=
      Finset.sum_nonneg (fun i _ => Int.floor_nonneg.mpr (hy i))
    norm_num at hc
    omega
  have hlam : 0 ≤ G 1-G 0 := sub_nonneg.mpr (hG 0 1 (by norm_num) (by norm_num) hMpos)
  have hM : 0 ≤ M := by
    have hr : (0 : ℝ) ≤ M := by rw [← hs]; exact Finset.sum_nonneg (fun i _ => hy i)
    exact_mod_cast hr
  have hnloss (v : Fin N → ℤ) (hv : isMinimum G M y v) :
      loss G M y v = RematPenalty.loss (G 1-G 0) M y v+G 0 := by
    have he := minimum_rounded_representation G M hG y hy hs v hv
    rw [he]
    exact capacity_one_loss G M y hs hk _ (by rw [← he]; exact hv.1)
  have hvloss (v : Fin N → ℤ) (hv : RematPenalty.isMinimum (G 1-G 0) M y v) :
      loss G M y v = RematPenalty.loss (G 1-G 0) M y v+G 0 := by
    have he := RematPenalty.minimum_rounded_representation _ hlam M y hy hs v hv
    rw [he]
    exact capacity_one_loss G M y hs hk _ (by rw [← he]; exact hv.1)
  constructor
  · intro hn
    obtain ⟨v,hv⟩ := RematPenalty.minimum_exists (G 1-G 0) M hM y
    refine ⟨hn.1,fun z hz => ?_⟩
    have hcomp := hn.2 v hv.1
    rw [hnloss n hn,hvloss v hv] at hcomp
    exact (le_of_add_le_add_right hcomp).trans (hv.2 z hz)
  · intro hn
    obtain ⟨v,hv⟩ := minimum_exists G M hM y
    refine ⟨hn.1,fun z hz => ?_⟩
    have hcomp := hn.2 v hv.1
    have he1 := hvloss n hn
    have he2 := hnloss v hv
    have hh := hv.2 z hz
    linarith


theorem four_capacity (q : ℕ) :
    RematRounding.capacity (10*(q : ℤ)+1) (fourTarget q) = 1 := by
  have hb : RematRounding.base (fourTarget q) = fourGrid q := by
    funext i
    apply Int.floor_eq_iff.mpr
    fin_cases i <;> norm_num [fourTarget,fourGrid]
  unfold RematRounding.capacity
  rw [hb,four_grid_slack]
  norm_num

theorem four_minimum_iff (G : ℤ → ℝ) (q : ℕ)
    (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ 10*(q : ℤ)+1 → G a ≤ G b) (n : Fin 4 → ℤ) :
    isMinimum G (10*(q : ℤ)+1) (fourTarget q) n ↔
      (n = fourGrid q ∧ G 1-G 0 ≤ 1/5) ∨
      (n = (fun i => fourGrid q i + RematPenalty.unitVector 0 i) ∧ 1/5 ≤ G 1-G 0) := by
  have hy : ∀ i, 0 ≤ fourTarget q i := by
    intro i
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    fin_cases i <;> simp [fourTarget] <;> linarith
  have hs : ∑ i, fourTarget q i = ((10*(q : ℤ)+1 : ℤ) : ℝ) := by
    simp [fourTarget,Fin.sum_univ_succ]
    ring
  rw [capacity_one_minimum_iff_quadratic G _ hG _ hy hs (four_capacity q) n]
  exact RematPenalty.four_penalty_transition _ (sub_nonneg.mpr (hG 0 1 (by norm_num) (by norm_num) (by omega))) q n

def sampledPenalty (φ : ℝ → ℝ) (M : ℤ) (r : ℤ) : ℝ := (M : ℝ)^2 * φ ((r : ℝ)/M)

theorem sampledPenalty_monotone (φ : ℝ → ℝ) (hφ : MonotoneOn φ (Set.Icc 0 1))
    (M : ℤ) (hM : 0 < M) :
    ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → sampledPenalty φ M a ≤ sampledPenalty φ M b := by
  intro a b ha hab hbM
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbR : (0 : ℝ) ≤ b := haR.trans habR
  have hbm : (b : ℝ) ≤ M := by exact_mod_cast hbM
  apply mul_le_mul_of_nonneg_left
  · exact hφ ⟨div_nonneg haR hm.le,(div_le_one₀ hm).mpr (habR.trans hbm)⟩
      ⟨div_nonneg hbR hm.le,(div_le_one₀ hm).mpr hbm⟩ (div_le_div_of_nonneg_right habR hm.le)
  · positivity

theorem sampledPenalty_difference (φ : ℝ → ℝ) (hφ : φ 0 = 0) (M : ℤ) :
    sampledPenalty φ M 1-sampledPenalty φ M 0 = (M : ℝ)^2 * φ (1/M) := by
  simp [sampledPenalty,hφ]

theorem four_sampled_minimum_iff (φ : ℝ → ℝ) (hφ : MonotoneOn φ (Set.Icc 0 1))
    (hφ0 : φ 0=0) (q : ℕ) (n : Fin 4 → ℤ) :
    isMinimum (sampledPenalty φ (10*(q : ℤ)+1)) (10*(q : ℤ)+1) (fourTarget q) n ↔
      (n = fourGrid q ∧ (10*(q : ℝ)+1)^2 * φ (1/(10*(q : ℝ)+1)) ≤ 1/5) ∨
      (n = (fun i => fourGrid q i + RematPenalty.unitVector 0 i) ∧
        1/5 ≤ (10*(q : ℝ)+1)^2 * φ (1/(10*(q : ℝ)+1))) := by
  have hM : (0 : ℤ) < 10*(q : ℤ)+1 := by omega
  rw [four_minimum_iff _ q (sampledPenalty_monotone φ hφ _ hM) n,
    sampledPenalty_difference φ hφ0]
  push_cast
  rfl

theorem four_sampled_pattern (φ : ℝ → ℝ) (hφ : MonotoneOn φ (Set.Icc 0 1))
    (hφ0 : φ 0=0) (pattern : ℕ → Bool)
    (hsample : ∀ q : ℕ, 1 ≤ q → if pattern q then
      1/5 < (10*(q : ℝ)+1)^2 * φ (1/(10*(q : ℝ)+1)) else
      (10*(q : ℝ)+1)^2 * φ (1/(10*(q : ℝ)+1)) < 1/5) :
    ∀ q : ℕ, 1 ≤ q → ∀ n : Fin 4 → ℤ,
      isMinimum (sampledPenalty φ (10*(q : ℤ)+1)) (10*(q : ℤ)+1) (fourTarget q) n ↔
        n = if pattern q then (fun i => fourGrid q i + RematPenalty.unitVector 0 i)
          else fourGrid q := by
  intro q hq n
  rw [four_sampled_minimum_iff φ hφ hφ0 q n]
  have hh := hsample q hq
  cases hb : pattern q <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
  · have hnot : ¬ 1/5 ≤ (10*(q : ℝ)+1)^2 * φ (1/(10*(q : ℝ)+1)) := not_le.mpr hh
    simp only [hh.le,hnot,and_true,and_false,or_false]
  · have hnot : ¬ (10*(q : ℝ)+1)^2 * φ (1/(10*(q : ℝ)+1)) ≤ 1/5 := not_le.mpr hh
    simp only [hh.le,hnot,and_true,and_false,false_or]


def gridLoss (φ : ℝ → ℝ) (a d : Fin N → ℝ) : ℝ := RematGrid.loss a d + φ (1-∑ i,d i)

def gridMinimum (φ : ℝ → ℝ) (M : ℤ) (a d : Fin N → ℝ) : Prop :=
  RematGrid.feasible M d ∧ ∀ e, RematGrid.feasible M e → gridLoss φ a d ≤ gridLoss φ a e

theorem grid_loss_scaling (φ : ℝ → ℝ) (M : ℤ) (hM : 0 < M) (a : Fin N → ℝ) (n : Fin N → ℤ) :
    (M : ℝ)^2 * gridLoss φ a (RematGrid.point M n) =
      loss (sampledPenalty φ M) M (fun i => (M : ℝ)*a i) n := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  unfold gridLoss loss sampledPenalty
  rw [mul_add,RematGrid.loss_scaling M hM,RematGrid.point_sum]
  congr 2
  push_cast
  field_simp

theorem grid_minimum_point_iff (φ : ℝ → ℝ) (M : ℤ) (hM : 0 < M)
    (a : Fin N → ℝ) (n : Fin N → ℤ) :
    gridMinimum φ M a (RematGrid.point M n) ↔
      isMinimum (sampledPenalty φ M) M (fun i => (M : ℝ)*a i) n := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hp : (0 : ℝ) < (M : ℝ)^2 := sq_pos_of_pos hm
  constructor
  · rintro ⟨hf,ho⟩
    refine ⟨(RematGrid.point_feasible_iff M hM n).mp hf,?_⟩
    intro z hz
    rw [← grid_loss_scaling φ M hM a n,← grid_loss_scaling φ M hM a z]
    exact mul_le_mul_of_nonneg_left (ho (RematGrid.point M z)
      ((RematGrid.point_feasible_iff M hM z).mpr hz)) hp.le
  · rintro ⟨hf,ho⟩
    refine ⟨(RematGrid.point_feasible_iff M hM n).mpr hf,?_⟩
    intro e he
    obtain ⟨z,rfl⟩ := he.2.2
    have hi := ho z ((RematGrid.point_feasible_iff M hM z).mp he)
    rw [← grid_loss_scaling φ M hM a n,← grid_loss_scaling φ M hM a z] at hi
    exact le_of_mul_le_mul_left hi hp

theorem four_grid_sampled_minimum_iff (φ : ℝ → ℝ) (hφ : MonotoneOn φ (Set.Icc 0 1))
    (hφ0 : φ 0=0) (q : ℕ) (n : Fin 4 → ℤ) :
    gridMinimum φ (10*(q : ℤ)+1) RematRefinement.target (RematGrid.point (10*(q : ℤ)+1) n) ↔
      (n = fourGrid q ∧ (10*(q : ℝ)+1)^2 * φ (1/(10*(q : ℝ)+1)) ≤ 1/5) ∨
      (n = (fun i => fourGrid q i + RematPenalty.unitVector 0 i) ∧
        1/5 ≤ (10*(q : ℝ)+1)^2 * φ (1/(10*(q : ℝ)+1))) := by
  have hM : (0 : ℤ) < 10*(q : ℤ)+1 := by omega
  rw [grid_minimum_point_iff φ _ hM]
  have ht : (fun i => ((10*(q : ℤ)+1 : ℤ) : ℝ)*RematRefinement.target i) = fourTarget q := by
    funext i
    fin_cases i <;> simp [RematRefinement.target,GridResidueCertificate.weights,fourTarget] <;> ring
  rw [ht]
  exact four_sampled_minimum_iff φ hφ hφ0 q n


def selectionCost (G : ℤ → ℝ) (k : ℕ) (c : Fin N → ℝ) (E : Finset (Fin N)) : ℝ :=
  RematSelection.cost c E + G ((k : ℤ)-E.card)

def selectionMinimum (G : ℤ → ℝ) (k : ℕ) (c : Fin N → ℝ) (E : Finset (Fin N)) : Prop :=
  E.card ≤ k ∧ ∀ F : Finset (Fin N), F.card ≤ k → selectionCost G k c E ≤ selectionCost G k c F

def scalar (G : ℤ → ℝ) (k : ℕ) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (m : ℕ) : ℝ :=
  RematSelection.cost c (RematPenaltySelection.firstSet σ m) + G ((k : ℤ)-m)

theorem rounded_loss (G : ℤ → ℝ) (M : ℤ) (y : Fin N → ℝ)
    (hs : ∑ i, y i = (M : ℝ)) (E : Finset (Fin N)) :
    loss G M y (RematRounding.rounded y E) = RematGeneral.loss y (RematRounding.base y) +
      selectionCost G (RematRounding.capacity M y) (RematRounding.benefit y) E := by
  unfold loss selectionCost
  rw [RematRounding.rounded_loss,RematRounding.rounded_slack M y hs]
  ring

theorem rounded_minimum_iff (G : ℤ → ℝ) (M : ℤ)
    (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b)
    (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) (E : Finset (Fin N)) :
    isMinimum G M y (RematRounding.rounded y E) ↔
      selectionMinimum G (RematRounding.capacity M y) (RematRounding.benefit y) E := by
  constructor
  · intro h
    refine ⟨(RematRounding.rounded_feasible_iff M y hy hs E).mp h.1,?_⟩
    intro F hF
    have hcomp := h.2 (RematRounding.rounded y F) ((RematRounding.rounded_feasible_iff M y hy hs F).mpr hF)
    rw [rounded_loss G M y hs E,rounded_loss G M y hs F] at hcomp
    linarith
  · intro h
    refine ⟨(RematRounding.rounded_feasible_iff M y hy hs E).mpr h.1,?_⟩
    intro z hz
    have hM : 0 ≤ M := by
      have hh : (0 : ℝ) ≤ M := by rw [← hs]; exact Finset.sum_nonneg (fun i _ => hy i)
      exact_mod_cast hh
    obtain ⟨v,hv⟩ := minimum_exists G M hM y
    have hrep := minimum_rounded_representation G M hG y hy hs v hv
    have hvfeas : RematGeneral.feasible M (RematRounding.rounded y (RematRounding.selected y v)) := by
      rw [← hrep]; exact hv.1
    have hcomp := h.2 (RematRounding.selected y v) ((RematRounding.rounded_feasible_iff M y hy hs _).mp hvfeas)
    have hmin := hv.2 z hz
    rw [hrep,rounded_loss G M y hs] at hmin
    rw [rounded_loss G M y hs]
    linarith

theorem scalar_classification (G : ℤ → ℝ) (k : ℕ) (hk : k ≤ N)
    (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (hc : Monotone (fun i => c (σ i)))
    (E : Finset (Fin N)) :
    selectionMinimum G k c E ↔ E.card ≤ k ∧ RematPenaltySelection.cutoff c E ∧
      ∀ m : ℕ, m ≤ k → scalar G k c σ E.card ≤ scalar G k c σ m := by
  constructor
  · intro h
    have hcut : RematPenaltySelection.cutoff c E := by
      apply (RematPenaltySelection.fixed_cardinality_iff c E).mp
      intro F hF
      have hm := h.2 F (by rw [hF]; exact h.1)
      unfold selectionCost at hm
      rw [hF] at hm
      linarith
    refine ⟨h.1,hcut,?_⟩
    intro m hm
    have hmin := h.2 (RematPenaltySelection.firstSet σ m)
      (by rw [RematPenaltySelection.prefix_card σ m (hm.trans hk)]; exact hm)
    unfold selectionCost at hmin
    rw [RematPenaltySelection.prefix_card σ m (hm.trans hk),
      RematPenaltySelection.cutoff_cost c σ hc E hcut] at hmin
    exact hmin
  · rintro ⟨hcap,hcut,hscalar⟩
    refine ⟨hcap,fun F hF => ?_⟩
    have hbound := (RematPenaltySelection.fixed_cardinality_iff c (RematPenaltySelection.firstSet σ F.card)).mpr
      (RematPenaltySelection.prefix_cutoff c σ hc F.card) F
      (RematPenaltySelection.prefix_card σ F.card (hF.trans hk)).symm
    have hs := hscalar F.card hF
    unfold scalar at hs
    unfold selectionCost
    rw [RematPenaltySelection.cutoff_cost c σ hc E hcut]
    linarith

theorem all_minimizer_scalar_classification (G : ℤ → ℝ) (M : ℤ)
    (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b)
    (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (σ : Equiv.Perm (Fin N)) (hσ : Monotone (fun i => RematRounding.benefit y (σ i)))
    (n : Fin N → ℤ) :
    isMinimum G M y n ↔ ∃ E, n = RematRounding.rounded y E ∧
      E.card ≤ RematRounding.capacity M y ∧ RematPenaltySelection.cutoff (RematRounding.benefit y) E ∧
      ∀ m : ℕ, m ≤ RematRounding.capacity M y →
        scalar G (RematRounding.capacity M y) (RematRounding.benefit y) σ E.card ≤
        scalar G (RematRounding.capacity M y) (RematRounding.benefit y) σ m := by
  constructor
  · intro hn
    have hrep := minimum_rounded_representation G M hG y hy hs n hn
    refine ⟨RematRounding.selected y n,hrep,?_⟩
    apply (scalar_classification G _ (RematPenalty.capacity_le_dimension M y hs) _ σ hσ _).mp
    apply (rounded_minimum_iff G M hG y hy hs _).mp
    rwa [← hrep]
  · rintro ⟨E,rfl,hE⟩
    apply (rounded_minimum_iff G M hG y hy hs E).mpr
    exact (scalar_classification G _ (RematPenalty.capacity_le_dimension M y hs) _ σ hσ E).mpr hE

theorem scalar_increment (G : ℤ → ℝ) (k : ℕ) (c : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) (m : ℕ) (hm : m < N) :
    scalar G k c σ (m+1)-scalar G k c σ m =
      c (σ ⟨m,hm⟩)+G ((k : ℤ)-(m+1))-G ((k : ℤ)-m) := by
  have hnot : σ ⟨m,hm⟩ ∉ RematPenaltySelection.firstSet σ m := by
    simp [RematPenaltySelection.mem_prefix]
  unfold scalar
  rw [RematPenaltySelection.prefix_succ σ m hm]
  simp [RematSelection.cost,Finset.sum_insert hnot]
  ring

end

end RematGeneralResidual

#print axioms RematGeneralResidual.minimum_exists
#print axioms RematGeneralResidual.coordinate_lower
#print axioms RematGeneralResidual.coordinate_upper
#print axioms RematGeneralResidual.coordinate_proximity
#print axioms RematGeneralResidual.minimum_rounded_representation
#print axioms RematGeneralResidual.capacity_one_loss
#print axioms RematGeneralResidual.capacity_one_minimum_iff_quadratic

#print axioms RematGeneralResidual.four_capacity
#print axioms RematGeneralResidual.four_minimum_iff
#print axioms RematGeneralResidual.sampledPenalty_monotone
#print axioms RematGeneralResidual.sampledPenalty_difference
#print axioms RematGeneralResidual.four_sampled_minimum_iff
#print axioms RematGeneralResidual.four_sampled_pattern

namespace RematAnalyticStability

open Filter Set
open scoped Topology

noncomputable section

theorem analytic_eventual_sign (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) :
    (∀ᶠ x in 𝓝[>] (0 : ℝ), f x = 0) ∨
      (∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < f x) ∨
      (∀ᶠ x in 𝓝[>] (0 : ℝ), f x < 0) := by
  by_cases hz : ∀ᶠ x in 𝓝 (0 : ℝ), f x = 0
  · exact Or.inl (hz.filter_mono nhdsWithin_le_nhds)
  · obtain ⟨m,g,hg,hg0,heq⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz
    have hx : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
    rcases lt_or_gt_of_ne hg0 with hneg | hpos
    · right
      right
      have hgneg : ∀ᶠ x in 𝓝 (0 : ℝ), g x < 0 := hg.continuousAt.eventually_lt continuousAt_const hneg
      filter_upwards [heq.filter_mono nhdsWithin_le_nhds,hgneg.filter_mono nhdsWithin_le_nhds,hx] with x he hgx hx
      simp only [sub_zero,smul_eq_mul] at he
      rw [he]
      exact mul_neg_of_pos_of_neg (pow_pos hx m) hgx
    · right
      left
      have hgpos : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < g x := continuousAt_const.eventually_lt hg.continuousAt hpos
      filter_upwards [heq.filter_mono nhdsWithin_le_nhds,hgpos.filter_mono nhdsWithin_le_nhds,hx] with x he hgx hx
      simp only [sub_zero,smul_eq_mul] at he
      rw [he]
      exact mul_pos (pow_pos hx m) hgx

theorem analytic_eventual_nonpositive (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) :
    ∃ b : Bool, ∀ᶠ x in 𝓝[>] (0 : ℝ), f x ≤ 0 ↔ b = true := by
  rcases analytic_eventual_sign f hf with hz | hp | hn
  · refine ⟨true,hz.mono ?_⟩
    intro x hx
    simp [hx]
  · refine ⟨false,hp.mono ?_⟩
    intro x hx
    simp [not_le.mpr hx]
  · refine ⟨true,hn.mono ?_⟩
    intro x hx
    simp [hx.le]

theorem analytic_finite_argmin_stabilizes {I : Type*} [Fintype I]
    (F : I → ℝ → ℝ) (hF : ∀ i, AnalyticAt ℝ (F i) 0) :
    ∃ P : I → Prop, ∀ᶠ x in 𝓝[>] (0 : ℝ),
      ∀ i, (∀ j, F i x ≤ F j x) ↔ P i := by
  classical
  have hpair : ∀ i j : I, ∃ b : Bool, ∀ᶠ x in 𝓝[>] (0 : ℝ),
      F i x ≤ F j x ↔ b = true := by
    intro i j
    simpa only [sub_nonpos] using analytic_eventual_nonpositive (fun x => F i x-F j x) ((hF i).sub (hF j))
  choose b hb using hpair
  have hall : ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ i j : I, F i x ≤ F j x ↔ b i j = true := by
    simp only [Filter.eventually_all]
    exact hb
  refine ⟨fun i => ∀ j, b i j = true,hall.mono ?_⟩
  intro x hx i
  exact forall_congr' (fun j => hx i j)


theorem analytic_finite_argmin_sequence_stabilizes {I : Type*} [Fintype I]
    (F : I → ℝ → ℝ) (hF : ∀ i, AnalyticAt ℝ (F i) 0)
    (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝[>] (0 : ℝ))) :
    ∃ P : I → Prop, ∀ᶠ n in atTop, ∀ i, (∀ j, F i (x n) ≤ F j (x n)) ↔ P i := by
  obtain ⟨P,hP⟩ := analytic_finite_argmin_stabilizes F hF
  exact ⟨P,hx.eventually hP⟩

theorem analytic_residual_profiles_stabilize {I : Type*} [Fintype I]
    (φ : ℝ → ℝ) (hφ : AnalyticAt ℝ φ 0) (A s : I → ℝ) :
    ∃ P : I → Prop, ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ i,
      (∀ j, A i*x^2+φ (s i*x) ≤ A j*x^2+φ (s j*x)) ↔ P i := by
  apply analytic_finite_argmin_stabilizes
  intro i
  have hlinear : AnalyticAt ℝ (fun x : ℝ => s i*x) 0 := analyticAt_const.mul analyticAt_id
  have hcomp : AnalyticAt ℝ (fun x : ℝ => φ (s i*x)) 0 := by
    exact hφ.fun_comp_of_eq hlinear (by simp)
  exact (analyticAt_const.mul (analyticAt_id.pow 2)).add hcomp

theorem analytic_residue_argmin_periodic {I : Type*} [Fintype I]
    (D : ℕ) (hD : 0 < D) (F : Fin D → I → ℝ → ℝ)
    (hF : ∀ r i, AnalyticAt ℝ (F r i) 0)
    (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝[>] (0 : ℝ))) :
    ∃ Q : ℕ, ∀ n : ℕ, Q ≤ n → ∀ i,
      (∀ j, F ⟨n%D,Nat.mod_lt n hD⟩ i (x n) ≤ F ⟨n%D,Nat.mod_lt n hD⟩ j (x n)) ↔
      (∀ j, F ⟨(n+D)%D,Nat.mod_lt (n+D) hD⟩ i (x (n+D)) ≤
        F ⟨(n+D)%D,Nat.mod_lt (n+D) hD⟩ j (x (n+D))) := by
  classical
  have hstab : ∀ r : Fin D, ∃ P : I → Prop, ∀ᶠ n in atTop,
      ∀ i, (∀ j, F r i (x n) ≤ F r j (x n)) ↔ P i := by
    intro r
    exact analytic_finite_argmin_sequence_stabilizes (F r) (hF r) x hx
  choose P hP using hstab
  have hall : ∀ᶠ n in atTop, ∀ r : Fin D, ∀ i,
      (∀ j, F r i (x n) ≤ F r j (x n)) ↔ P r i := by
    simp only [Filter.eventually_all]
    intro r i
    exact (hP r).mono (fun n hn => hn i)
  obtain ⟨Q,hQ⟩ := Filter.eventually_atTop.mp hall
  refine ⟨Q,fun n hn i => ?_⟩
  have hindex : (⟨(n+D)%D,Nat.mod_lt (n+D) hD⟩ : Fin D) = ⟨n%D,Nat.mod_lt n hD⟩ := by
    apply Fin.ext
    simp
  rw [hindex]
  exact (hQ n hn _ i).trans (hQ (n+D) (by omega) _ i).symm


theorem analytic_nonempty_argmin_stabilizes {I : Type*} [Fintype I] [Nonempty I]
    (F : I → ℝ → ℝ) (hF : ∀ i, AnalyticAt ℝ (F i) 0) :
    ∃ P : I → Prop, (∃ i, P i) ∧ ∀ᶠ x in 𝓝[>] (0 : ℝ),
      ∀ i, (∀ j, F i x ≤ F j x) ↔ P i := by
  classical
  obtain ⟨P,hP⟩ := analytic_finite_argmin_stabilizes F hF
  obtain ⟨x,hx⟩ := hP.exists
  obtain ⟨i,hi,hmin⟩ := Finset.univ.exists_min_image (fun i => F i x) Finset.univ_nonempty
  exact ⟨P,⟨i,(hx i).mp (fun j => hmin j (Finset.mem_univ j))⟩,hP⟩

theorem analytic_finite_residue_argmin_stabilizes {R : Type*} [Fintype R]
    (I : R → Type*) [∀ r, Fintype (I r)] [∀ r, Nonempty (I r)]
    (F : ∀ r, I r → ℝ → ℝ) (hF : ∀ r i, AnalyticAt ℝ (F r i) 0) :
    ∃ P : ∀ r, I r → Prop, (∀ r, ∃ i, P r i) ∧
      ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ r i, (∀ j, F r i x ≤ F r j x) ↔ P r i := by
  classical
  have hstab : ∀ r, ∃ P : I r → Prop, (∃ i, P i) ∧
      ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ i, (∀ j, F r i x ≤ F r j x) ↔ P i := by
    intro r
    exact analytic_nonempty_argmin_stabilizes (F r) (hF r)
  choose P hn hP using hstab
  refine ⟨P,hn,?_⟩
  simp only [Filter.eventually_all]
  intro r i
  exact (hP r).mono (fun x hx => hx i)

end

end RematAnalyticStability

#print axioms RematAnalyticStability.analytic_eventual_sign
#print axioms RematAnalyticStability.analytic_eventual_nonpositive
#print axioms RematAnalyticStability.analytic_finite_argmin_stabilizes

#print axioms RematGeneralResidual.grid_loss_scaling
#print axioms RematGeneralResidual.grid_minimum_point_iff
#print axioms RematGeneralResidual.four_grid_sampled_minimum_iff

#print axioms RematAnalyticStability.analytic_finite_argmin_sequence_stabilizes
#print axioms RematAnalyticStability.analytic_residual_profiles_stabilize
#print axioms RematAnalyticStability.analytic_residue_argmin_periodic

#print axioms RematGeneralResidual.rounded_loss
#print axioms RematGeneralResidual.rounded_minimum_iff
#print axioms RematGeneralResidual.scalar_classification
#print axioms RematGeneralResidual.all_minimizer_scalar_classification
#print axioms RematGeneralResidual.scalar_increment

namespace RematSmoothBump

noncomputable section

def bump (u : ℝ) : ℝ := Real.exp 1 * expNegInvGlue (1-u^2)

theorem bump_contDiff (n : ℕ∞) : ContDiff ℝ n bump := by
  exact contDiff_const.mul (expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2)))

theorem bump_formula (u : ℝ) :
    bump u = if |u| < 1 then Real.exp (1-1/(1-u^2)) else 0 := by
  by_cases h : |u| < 1
  · have hp : 0 < 1-u^2 := by have := (sq_lt_one_iff_abs_lt_one u).mpr h; linarith
    simp only [bump,expNegInvGlue,not_le.mpr hp,ite_false,h,ite_true,← Real.exp_add]
    congr 1
    ring
  · have hn : 1-u^2 ≤ 0 := by
      have ha : 1 ≤ |u| := le_of_not_gt h
      have := (one_le_sq_iff_one_le_abs u).mpr ha
      linarith
    simp [bump,expNegInvGlue.zero_of_nonpos hn,h]

theorem bump_zero : bump 0 = 1 := by
  norm_num [bump_formula]

theorem bump_outside (u : ℝ) (hu : 1 ≤ |u|) : bump u = 0 := by
  simp [bump_formula,not_lt.mpr hu]

theorem bump_nonneg (u : ℝ) : 0 ≤ bump u :=
  mul_nonneg (Real.exp_pos 1).le (expNegInvGlue.nonneg _)

end

end RematSmoothBump

#print axioms RematSmoothBump.bump_contDiff
#print axioms RematSmoothBump.bump_formula
#print axioms RematSmoothBump.bump_zero
#print axioms RematSmoothBump.bump_outside
#print axioms RematSmoothBump.bump_nonneg

#print axioms RematAnalyticStability.analytic_nonempty_argmin_stabilizes
#print axioms RematAnalyticStability.analytic_finite_residue_argmin_stabilizes

namespace RematGeneralResidual

noncomputable section

open Finset RematPenaltySelection

variable {N : ℕ}

theorem sampled_increment_step (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Set.Icc 0 1) φ)
    (M : ℤ) (hM : 0 < M) (r : ℕ) (hr : ((r+2 : ℕ) : ℤ) ≤ M) :
    sampledPenalty φ M (r+1)-sampledPenalty φ M r ≤
      sampledPenalty φ M (r+2)-sampledPenalty φ M (r+1) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hrM : (r : ℝ)+2 ≤ M := by exact_mod_cast hr
  have hleft : (r : ℝ)/M ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hr0 hm.le,(div_le_one₀ hm).mpr (by linarith)⟩
  have hright : ((r : ℝ)+2)/M ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hm.le,(div_le_one₀ hm).mpr hrM⟩
  have hsl := hφ.slope_mono_adjacent hleft hright
    (show (r : ℝ)/M < ((r : ℝ)+1)/M from (div_lt_div_iff_of_pos_right hm).mpr (by linarith))
    (show ((r : ℝ)+1)/M < ((r : ℝ)+2)/M from (div_lt_div_iff_of_pos_right hm).mpr (by linarith))
  have hdiff1 : ((r : ℝ)+1)/M-(r : ℝ)/M = 1/M := by ring
  have hdiff2 : ((r : ℝ)+2)/M-((r : ℝ)+1)/M = 1/M := by ring
  rw [hdiff1,hdiff2] at hsl
  have hden : (0 : ℝ) < 1/M := one_div_pos.mpr hm
  have hbase := (div_le_div_iff_of_pos_right hden).mp hsl
  have hm2 : (0 : ℝ) ≤ (M : ℝ)^2 := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hbase hm2
  unfold sampledPenalty
  push_cast
  nlinarith

theorem sampled_increment_lower (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Set.Icc 0 1) φ)
    (M : ℤ) (hM : 0 < M) (r : ℕ) (hr : 1 ≤ r) (hrM : (r : ℤ) ≤ M) :
    sampledPenalty φ M 1-sampledPenalty φ M 0 ≤
      sampledPenalty φ M r-sampledPenalty φ M (r-1) := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hz : r=0
    · subst r
      norm_num
    · have hrpos : 1 ≤ r := by omega
      have hprev := ih hrpos (by exact_mod_cast (show (r : ℤ) ≤ M by omega))
      have hnext := sampled_increment_step φ hφ M hM (r-1) (by omega)
      have her : ((r-1 : ℕ) : ℤ)+1 = (r : ℤ) := by omega
      have her2 : ((r-1 : ℕ) : ℤ)+2 = (r : ℤ)+1 := by omega
      rw [her,her2] at hnext
      have hrc : ((r-1 : ℕ) : ℤ) = (r : ℤ)-1 := by omega
      rw [hrc] at hnext
      simpa using hprev.trans hnext

theorem increment_le_last (G : ℤ → ℝ) (k : ℕ)
    (hG : ∀ r : ℕ, 1 ≤ r → r ≤ k → G 1-G 0 ≤ G r-G ((r : ℤ)-1)) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) (m : ℕ) (hm : m < k) :
    scalar G k c σ (m+1) - scalar G k c σ m ≤ lastCost k hk hkN c σ - (G 1-G 0) := by
  rw [scalar_increment G k c σ m (by omega)]
  have horder : (⟨m,by omega⟩ : Fin N) ≤ ⟨k-1,by omega⟩ := by
    exact_mod_cast (show m ≤ k-1 by omega)
  have hv := hc horder
  have hd := hG (k-m) (by omega) (by omega)
  have hr1 : ((k-m : ℕ) : ℤ) = (k : ℤ)-m := by omega
  rw [hr1] at hd
  have hr2 : (k : ℤ)-m-1 = (k : ℤ)-(m+1) := by ring
  rw [hr2] at hd
  dsimp [lastCost]
  linarith


theorem scalar_last_le (G : ℤ → ℝ) (k : ℕ)
    (hG : ∀ r : ℕ, 1 ≤ r → r ≤ k → G 1-G 0 ≤ G r-G ((r : ℤ)-1)) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) (hth : lastCost k hk hkN c σ ≤ (G 1-G 0))
    (m : ℕ) (hm : m ≤ k) : scalar G k c σ k ≤ scalar G k c σ m := by
  have step (b : ℕ) (hb : b < k) : scalar G k c σ (b+1) ≤ scalar G k c σ b := by
    have hd := increment_le_last G k hG hk hkN c σ hc b hb
    linarith
  have chain : ∀ b, m ≤ b → b ≤ k → scalar G k c σ b ≤ scalar G k c σ m := by
    intro b hmb
    induction b, hmb using Nat.le_induction with
    | base => intro _; exact le_refl _
    | succ b hmb ih =>
      intro hb
      exact (step b (by omega)).trans (ih (by omega))
  exact chain k hm (le_refl _)

theorem scalar_last_lt (G : ℤ → ℝ) (k : ℕ)
    (hG : ∀ r : ℕ, 1 ≤ r → r ≤ k → G 1-G 0 ≤ G r-G ((r : ℤ)-1)) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) (hth : lastCost k hk hkN c σ < (G 1-G 0))
    (m : ℕ) (hm : m < k) : scalar G k c σ k < scalar G k c σ m := by
  have hle := scalar_last_le G k hG hk hkN c σ hc hth.le (m+1) (by omega)
  have hd := increment_le_last G k hG hk hkN c σ hc m hm
  linarith

theorem scalar_last_increment (G : ℤ → ℝ) (k : ℕ) (hk : 0 < k) (hkN : k ≤ N)
    (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    scalar G k c σ k - scalar G k c σ (k-1) = lastCost k hk hkN c σ - (G 1-G 0) := by
  have he : k-1+1=k := by omega
  have h := scalar_increment G k c σ (k-1) (by omega)
  rw [he] at h
  have hr0 : (k : ℤ)-(((k-1 : ℕ) : ℤ)+1)=0 := by omega
  have hr1 : (k : ℤ)-((k-1 : ℕ) : ℤ)=1 := by omega
  rw [hr0,hr1] at h
  dsimp [lastCost]
  linarith


theorem saturated_minimum_iff (G : ℤ → ℝ) (k : ℕ)
    (hG : ∀ r : ℕ, 1 ≤ r → r ≤ k → G 1-G 0 ≤ G r-G ((r : ℤ)-1)) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) :
    (∃ E, selectionMinimum G k c E ∧ E.card = k) ↔ lastCost k hk hkN c σ ≤ (G 1-G 0) := by
  constructor
  · rintro ⟨E,hE,hcard⟩
    obtain ⟨_, _, hs⟩ := (scalar_classification G k hkN c σ hc E).mp hE
    have hb := hs (k-1) (by omega)
    rw [hcard] at hb
    have hd := scalar_last_increment G k hk hkN c σ
    linarith
  · intro hth
    refine ⟨firstSet σ k, ?_, prefix_card σ k hkN⟩
    apply (scalar_classification G k hkN c σ hc _).mpr
    rw [prefix_card σ k hkN]
    exact ⟨le_refl _, prefix_cutoff c σ hc k, scalar_last_le G k hG hk hkN c σ hc hth⟩

theorem selection_minimum_exists (G : ℤ → ℝ) (k : ℕ) (c : Fin N → ℝ) :
    ∃ E, selectionMinimum G k c E := by
  classical
  let candidates := Finset.univ.filter (fun E : Finset (Fin N) => E.card ≤ k)
  have hne : candidates.Nonempty := by refine ⟨∅, ?_⟩; simp [candidates]
  obtain ⟨E,hE,hm⟩ := candidates.exists_min_image (selectionCost G k c) hne
  exact ⟨E,(Finset.mem_filter.mp hE).2,fun F hF => hm F (by simp [candidates,hF])⟩

theorem last_two_tie (G : ℤ → ℝ) (k : ℕ)
    (hG : ∀ r : ℕ, 1 ≤ r → r ≤ k → G 1-G 0 ≤ G r-G ((r : ℤ)-1)) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) (hth : (G 1-G 0) = lastCost k hk hkN c σ) :
    selectionMinimum G k c (firstSet σ (k-1)) ∧ selectionMinimum G k c (firstSet σ k) := by
  have hlast := scalar_last_le G k hG hk hkN c σ hc hth.ge
  have heq : scalar G k c σ (k-1) = scalar G k c σ k := by
    have hd := scalar_last_increment G k hk hkN c σ
    linarith
  constructor
  · apply (scalar_classification G k hkN c σ hc _).mpr
    rw [prefix_card σ (k-1) (by omega)]
    exact ⟨by omega, prefix_cutoff c σ hc (k-1), fun m hm => by rw [heq]; exact hlast m hm⟩
  · apply (scalar_classification G k hkN c σ hc _).mpr
    rw [prefix_card σ k hkN]
    exact ⟨le_refl _, prefix_cutoff c σ hc k, hlast⟩

theorem all_saturated_iff (G : ℤ → ℝ) (k : ℕ)
    (hG : ∀ r : ℕ, 1 ≤ r → r ≤ k → G 1-G 0 ≤ G r-G ((r : ℤ)-1)) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) :
    (∀ E, selectionMinimum G k c E → E.card = k) ↔ lastCost k hk hkN c σ < (G 1-G 0) := by
  constructor
  · intro hall
    obtain ⟨E,hE⟩ := selection_minimum_exists G k c
    have hle := (saturated_minimum_iff G k hG hk hkN c σ hc).mp ⟨E,hE,hall E hE⟩
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · have hmin := (last_two_tie G k hG hk hkN c σ hc h.symm).1
      have hcard := hall _ hmin
      rw [prefix_card σ (k-1) (by omega)] at hcard
      omega
  · intro hth E hE
    obtain ⟨hcap, _, hs⟩ := (scalar_classification G k hkN c σ hc E).mp hE
    by_contra hne
    have ht := scalar_last_lt G k hG hk hkN c σ hc hth E.card (by omega)
    exact (not_lt_of_ge (hs k (le_refl _))) ht

theorem all_unsaturated_iff (G : ℤ → ℝ) (k : ℕ)
    (hG : ∀ r : ℕ, 1 ≤ r → r ≤ k → G 1-G 0 ≤ G r-G ((r : ℤ)-1)) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) :
    (∀ E, selectionMinimum G k c E → E.card < k) ↔ (G 1-G 0) < lastCost k hk hkN c σ := by
  constructor
  · intro hall
    by_contra hn
    obtain ⟨E,hE,hcard⟩ := (saturated_minimum_iff G k hG hk hkN c σ hc).mpr (le_of_not_gt hn)
    have := hall E hE
    omega
  · intro hth E hE
    have hcap := hE.1
    by_contra hn
    have hcard : E.card = k := by omega
    have := (saturated_minimum_iff G k hG hk hkN c σ hc).mp ⟨E,hE,hcard⟩
    linarith

theorem coexistence_iff (G : ℤ → ℝ) (k : ℕ)
    (hG : ∀ r : ℕ, 1 ≤ r → r ≤ k → G 1-G 0 ≤ G r-G ((r : ℤ)-1)) (hk : 0 < k)
    (hkN : k ≤ N) (c : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hc : Monotone (fun i => c (σ i))) :
    ((∃ E, selectionMinimum G k c E ∧ E.card = k) ∧
      (∃ F, selectionMinimum G k c F ∧ F.card < k)) ↔ (G 1-G 0) = lastCost k hk hkN c σ := by
  constructor
  · rintro ⟨hsat, F, hF, hsl⟩
    have hle := (saturated_minimum_iff G k hG hk hkN c σ hc).mp hsat
    have hge : (G 1-G 0) ≤ lastCost k hk hkN c σ := by
      by_contra hn
      have hall := (all_saturated_iff G k hG hk hkN c σ hc).mpr (lt_of_not_ge hn)
      have := hall F hF
      omega
    exact le_antisymm hge hle
  · intro he
    obtain ⟨ha,hb⟩ := last_two_tie G k hG hk hkN c σ hc he
    exact ⟨⟨firstSet σ k,hb,prefix_card σ k hkN⟩,
      ⟨firstSet σ (k-1),ha,by rw [prefix_card σ (k-1) (by omega)]; omega⟩⟩



theorem all_integer_minima_iff (G : ℤ → ℝ) (M : ℤ)
    (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b)
    (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) (n : Fin N → ℤ) :
    isMinimum G M y n ↔ ∃ E, n = RematRounding.rounded y E ∧
      selectionMinimum G (RematRounding.capacity M y) (RematRounding.benefit y) E := by
  constructor
  · intro hn
    have he := minimum_rounded_representation G M hG y hy hs n hn
    refine ⟨RematRounding.selected y n,he,?_⟩
    apply (rounded_minimum_iff G M hG y hy hs _).mp
    rwa [← he]
  · rintro ⟨E,rfl,hE⟩
    exact (rounded_minimum_iff G M hG y hy hs E).mpr hE

theorem saturated_exists_iff_selection (G : ℤ → ℝ) (M : ℤ)
    (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) :
    (∃ n, isMinimum G M y n ∧ ∑ i, n i = M) ↔
    (∃ E, selectionMinimum G (RematRounding.capacity M y) (RematRounding.benefit y) E ∧
      E.card = RematRounding.capacity M y) := by
  constructor
  · rintro ⟨n,hn,hS⟩
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff G M hG y hy hs n).mp hn
    have hsl := RematRounding.rounded_slack M y hs E
    refine ⟨E,hE,?_⟩
    omega
  · rintro ⟨E,hE,hcard⟩
    refine ⟨RematRounding.rounded y E,(rounded_minimum_iff G M hG y hy hs E).mpr hE,?_⟩
    have hsl := RematRounding.rounded_slack M y hs E
    omega

theorem all_saturated_iff_selection (G : ℤ → ℝ) (M : ℤ)
    (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) :
    (∀ n, isMinimum G M y n → ∑ i, n i = M) ↔
    (∀ E, selectionMinimum G (RematRounding.capacity M y) (RematRounding.benefit y) E →
      E.card = RematRounding.capacity M y) := by
  constructor
  · intro h E hE
    have hsE := h _ ((rounded_minimum_iff G M hG y hy hs E).mpr hE)
    have hsl := RematRounding.rounded_slack M y hs E
    omega
  · intro h n hn
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff G M hG y hy hs n).mp hn
    have hsE := h E hE
    have hsl := RematRounding.rounded_slack M y hs E
    omega

theorem positive_slack_exists_iff_selection (G : ℤ → ℝ) (M : ℤ)
    (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) :
    (∃ n, isMinimum G M y n ∧ 0 < M - ∑ i, n i) ↔
    (∃ E, selectionMinimum G (RematRounding.capacity M y) (RematRounding.benefit y) E ∧
      E.card < RematRounding.capacity M y) := by
  constructor
  · rintro ⟨n,hn,hS⟩
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff G M hG y hy hs n).mp hn
    have hsl := RematRounding.rounded_slack M y hs E
    refine ⟨E,hE,?_⟩
    omega
  · rintro ⟨E,hE,hcard⟩
    refine ⟨RematRounding.rounded y E,(rounded_minimum_iff G M hG y hy hs E).mpr hE,?_⟩
    have hsl := RematRounding.rounded_slack M y hs E
    omega

theorem all_positive_slack_iff_selection (G : ℤ → ℝ) (M : ℤ)
    (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) :
    (∀ n, isMinimum G M y n → 0 < M - ∑ i, n i) ↔
    (∀ E, selectionMinimum G (RematRounding.capacity M y) (RematRounding.benefit y) E →
      E.card < RematRounding.capacity M y) := by
  constructor
  · intro h E hE
    have hsE := h _ ((rounded_minimum_iff G M hG y hy hs E).mpr hE)
    have hsl := RematRounding.rounded_slack M y hs E
    omega
  · intro h n hn
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff G M hG y hy hs n).mp hn
    have hsE := h E hE
    have hsl := RematRounding.rounded_slack M y hs E
    omega

theorem exact_identification_threshold (G : ℤ → ℝ) (M : ℤ)
    (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b)
    (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (hk : 0 < RematRounding.capacity M y)
    (σ : Equiv.Perm (Fin N)) (hσ : Monotone (fun i => RematRounding.benefit y (σ i)))
    (hdelta : ∀ r : ℕ, 1 ≤ r → r ≤ RematRounding.capacity M y → G 1-G 0 ≤ G r-G ((r : ℤ)-1)) :
    ((∀ n, isMinimum G M y n → ∑ i, n i = M) ↔ RematPenalty.threshold M y hs hk σ < G 1-G 0) ∧
    ((∃ n, isMinimum G M y n ∧ ∑ i, n i = M) ↔ RematPenalty.threshold M y hs hk σ ≤ G 1-G 0) ∧
    ((∀ n, isMinimum G M y n → 0 < M-∑ i, n i) ↔ G 1-G 0 < RematPenalty.threshold M y hs hk σ) ∧
    (((∃ n, isMinimum G M y n ∧ ∑ i, n i = M) ∧
      (∃ n, isMinimum G M y n ∧ 0 < M-∑ i,n i)) ↔ G 1-G 0 = RematPenalty.threshold M y hs hk σ) := by
  rw [all_saturated_iff_selection G M hG y hy hs,
    saturated_exists_iff_selection G M hG y hy hs,
    all_positive_slack_iff_selection G M hG y hy hs,
    positive_slack_exists_iff_selection G M hG y hy hs]
  exact ⟨all_saturated_iff G _ hdelta hk (RematPenalty.capacity_le_dimension M y hs) _ σ hσ,
    saturated_minimum_iff G _ hdelta hk (RematPenalty.capacity_le_dimension M y hs) _ σ hσ,
    all_unsaturated_iff G _ hdelta hk (RematPenalty.capacity_le_dimension M y hs) _ σ hσ,
    coexistence_iff G _ hdelta hk (RematPenalty.capacity_le_dimension M y hs) _ σ hσ⟩

theorem capacity_le_M (M : ℤ) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ)) :
    (RematRounding.capacity M y : ℤ) ≤ M := by
  have hc := RematRounding.capacity_cast M y hs
  have hb : 0 ≤ ∑ i, RematRounding.base y i :=
    Finset.sum_nonneg (fun i _ => Int.floor_nonneg.mpr (hy i))
  omega

theorem exact_convex_identification_threshold (φ : ℝ → ℝ)
    (hφ : MonotoneOn φ (Set.Icc 0 1)) (hcφ : ConvexOn ℝ (Set.Icc 0 1) φ) (hφ0 : φ 0=0)
    (M : ℤ) (hM : 0 < M) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (hk : 0 < RematRounding.capacity M y)
    (σ : Equiv.Perm (Fin N)) (hσ : Monotone (fun i => RematRounding.benefit y (σ i))) :
    ((∀ n, isMinimum (sampledPenalty φ M) M y n → ∑ i,n i=M) ↔
      RematPenalty.threshold M y hs hk σ < (M : ℝ)^2*φ (1/M)) ∧
    ((∃ n, isMinimum (sampledPenalty φ M) M y n ∧ ∑ i,n i=M) ↔
      RematPenalty.threshold M y hs hk σ ≤ (M : ℝ)^2*φ (1/M)) ∧
    ((∀ n, isMinimum (sampledPenalty φ M) M y n → 0<M-∑ i,n i) ↔
      (M : ℝ)^2*φ (1/M) < RematPenalty.threshold M y hs hk σ) ∧
    (((∃ n, isMinimum (sampledPenalty φ M) M y n ∧ ∑ i,n i=M) ∧
      (∃ n, isMinimum (sampledPenalty φ M) M y n ∧ 0<M-∑ i,n i)) ↔
      (M : ℝ)^2*φ (1/M) = RematPenalty.threshold M y hs hk σ) := by
  have hdelta : ∀ r : ℕ, 1 ≤ r → r ≤ RematRounding.capacity M y →
      sampledPenalty φ M 1-sampledPenalty φ M 0 ≤ sampledPenalty φ M r-sampledPenalty φ M ((r : ℤ)-1) := by
    intro r hr hrk
    have hrM : (r : ℤ) ≤ M := (by exact_mod_cast hrk : (r : ℤ) ≤ RematRounding.capacity M y).trans (capacity_le_M M y hy hs)
    exact sampled_increment_lower φ hcφ M hM r hr hrM
  have ht := exact_identification_threshold (sampledPenalty φ M) M (sampledPenalty_monotone φ hφ M hM)
    y hy hs hk σ hσ hdelta
  rwa [sampledPenalty_difference φ hφ0 M] at ht


theorem zero_capacity_unique_minimum (G : ℤ → ℝ) (M : ℤ)
    (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (hk : RematRounding.capacity M y = 0) (n : Fin N → ℤ) :
    isMinimum G M y n ↔ n = RematRounding.base y := by
  have hM : 0 ≤ M := by
    have hh : (0 : ℝ) ≤ M := by rw [← hs]; exact Finset.sum_nonneg (fun i _ => hy i)
    exact_mod_cast hh
  have unique (v : Fin N → ℤ) (hv : isMinimum G M y v) : v = RematRounding.base y := by
    obtain ⟨E,rfl,hE⟩ := (all_integer_minima_iff G M hG y hy hs v).mp hv
    have hcard := hE.1
    rw [hk] at hcard
    have he : E = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [he]
    funext i
    simp [RematRounding.rounded]
  constructor
  · exact unique n
  · intro hn
    obtain ⟨v,hv⟩ := minimum_exists G M hM y
    rwa [hn,← unique v hv]


theorem point_saturated_iff (M : ℤ) (hM : 0 < M) (n : Fin N → ℤ) :
    ∑ i,RematGrid.point M n i=1 ↔ ∑ i,n i=M := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  rw [RematGrid.point_sum,div_eq_one_iff_eq hm]
  constructor <;> intro h <;> exact_mod_cast h

theorem point_positive_slack_iff (M : ℤ) (hM : 0 < M) (n : Fin N → ℤ) :
    0<1-∑ i,RematGrid.point M n i ↔ 0<M-∑ i,n i := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  rw [RematGrid.point_sum,sub_pos,div_lt_iff₀ hm,one_mul]
  constructor
  · intro h
    have hi : ∑ i,n i<M := by exact_mod_cast h
    omega
  · intro h
    exact_mod_cast (show ∑ i,n i<M by omega)

theorem grid_saturation_correspondence (φ : ℝ → ℝ) (M : ℤ) (hM : 0 < M) (a : Fin N → ℝ) :
    ((∀ d,gridMinimum φ M a d → ∑ i,d i=1) ↔
      (∀ n,isMinimum (sampledPenalty φ M) M (fun i => (M : ℝ)*a i) n → ∑ i,n i=M)) ∧
    ((∃ d,gridMinimum φ M a d ∧ ∑ i,d i=1) ↔
      (∃ n,isMinimum (sampledPenalty φ M) M (fun i => (M : ℝ)*a i) n ∧ ∑ i,n i=M)) ∧
    ((∀ d,gridMinimum φ M a d → 0<1-∑ i,d i) ↔
      (∀ n,isMinimum (sampledPenalty φ M) M (fun i => (M : ℝ)*a i) n → 0<M-∑ i,n i)) ∧
    ((∃ d,gridMinimum φ M a d ∧ 0<1-∑ i,d i) ↔
      (∃ n,isMinimum (sampledPenalty φ M) M (fun i => (M : ℝ)*a i) n ∧ 0<M-∑ i,n i)) := by
  constructor
  · constructor
    · intro h n hn
      exact (point_saturated_iff M hM n).mp (h _ ((grid_minimum_point_iff φ M hM a n).mpr hn))
    · intro h d hd
      obtain ⟨n,rfl⟩ := hd.1.2.2
      exact (point_saturated_iff M hM n).mpr (h n ((grid_minimum_point_iff φ M hM a n).mp hd))
  constructor
  · constructor
    · rintro ⟨d,hd,hs⟩
      obtain ⟨n,rfl⟩ := hd.1.2.2
      exact ⟨n,(grid_minimum_point_iff φ M hM a n).mp hd,(point_saturated_iff M hM n).mp hs⟩
    · rintro ⟨n,hn,hs⟩
      exact ⟨RematGrid.point M n,(grid_minimum_point_iff φ M hM a n).mpr hn,(point_saturated_iff M hM n).mpr hs⟩
  constructor
  · constructor
    · intro h n hn
      exact (point_positive_slack_iff M hM n).mp (h _ ((grid_minimum_point_iff φ M hM a n).mpr hn))
    · intro h d hd
      obtain ⟨n,rfl⟩ := hd.1.2.2
      exact (point_positive_slack_iff M hM n).mpr (h n ((grid_minimum_point_iff φ M hM a n).mp hd))
  · constructor
    · rintro ⟨d,hd,hs⟩
      obtain ⟨n,rfl⟩ := hd.1.2.2
      exact ⟨n,(grid_minimum_point_iff φ M hM a n).mp hd,(point_positive_slack_iff M hM n).mp hs⟩
    · rintro ⟨n,hn,hs⟩
      exact ⟨RematGrid.point M n,(grid_minimum_point_iff φ M hM a n).mpr hn,(point_positive_slack_iff M hM n).mpr hs⟩

theorem exact_convex_grid_identification_threshold (φ : ℝ → ℝ)
    (hφ : MonotoneOn φ (Set.Icc 0 1)) (hcφ : ConvexOn ℝ (Set.Icc 0 1) φ) (hφ0 : φ 0=0)
    (M : ℤ) (hM : 0<M) (a : Fin N → ℝ) (ha : ∀ i,0≤a i) (haS : ∑ i,a i=1)
    (hk : 0<RematRounding.capacity M (fun i => (M : ℝ)*a i))
    (σ : Equiv.Perm (Fin N)) (hσ : Monotone (fun i => RematRounding.benefit (fun j => (M : ℝ)*a j) (σ i))) :
    let θ := RematPenalty.threshold M (fun i => (M : ℝ)*a i) (RematGrid.scaled_target_hypotheses M hM a ha haS).2 hk σ
    ((∀ d,gridMinimum φ M a d → ∑ i,d i=1) ↔ θ<(M : ℝ)^2*φ (1/M)) ∧
    ((∃ d,gridMinimum φ M a d ∧ ∑ i,d i=1) ↔ θ≤(M : ℝ)^2*φ (1/M)) ∧
    ((∀ d,gridMinimum φ M a d → 0<1-∑ i,d i) ↔ (M : ℝ)^2*φ (1/M)<θ) ∧
    (((∃ d,gridMinimum φ M a d ∧ ∑ i,d i=1) ∧
      (∃ d,gridMinimum φ M a d ∧ 0<1-∑ i,d i)) ↔ (M : ℝ)^2*φ (1/M)=θ) := by
  dsimp only
  have hcorr := grid_saturation_correspondence φ M hM a
  rw [hcorr.1,hcorr.2.1,hcorr.2.2.1,hcorr.2.2.2]
  obtain ⟨hy,hyS⟩ := RematGrid.scaled_target_hypotheses M hM a ha haS
  exact exact_convex_identification_threshold φ hφ hcφ hφ0 M hM _ hy hyS hk σ hσ


end

end RematGeneralResidual

#print axioms RematGeneralResidual.sampled_increment_step
#print axioms RematGeneralResidual.sampled_increment_lower

#print axioms RematGeneralResidual.increment_le_last
#print axioms RematGeneralResidual.scalar_last_le
#print axioms RematGeneralResidual.scalar_last_lt
#print axioms RematGeneralResidual.scalar_last_increment
#print axioms RematGeneralResidual.saturated_minimum_iff
#print axioms RematGeneralResidual.selection_minimum_exists
#print axioms RematGeneralResidual.last_two_tie
#print axioms RematGeneralResidual.all_saturated_iff
#print axioms RematGeneralResidual.all_unsaturated_iff
#print axioms RematGeneralResidual.coexistence_iff

#print axioms RematGeneralResidual.all_integer_minima_iff
#print axioms RematGeneralResidual.saturated_exists_iff_selection
#print axioms RematGeneralResidual.all_saturated_iff_selection
#print axioms RematGeneralResidual.positive_slack_exists_iff_selection
#print axioms RematGeneralResidual.all_positive_slack_iff_selection
#print axioms RematGeneralResidual.exact_identification_threshold
#print axioms RematGeneralResidual.capacity_le_M
#print axioms RematGeneralResidual.exact_convex_identification_threshold

#print axioms RematGeneralResidual.zero_capacity_unique_minimum
#print axioms RematGeneralResidual.point_saturated_iff
#print axioms RematGeneralResidual.point_positive_slack_iff
#print axioms RematGeneralResidual.grid_saturation_correspondence
#print axioms RematGeneralResidual.exact_convex_grid_identification_threshold


open Filter Set
open scoped Topology

namespace RematZeroCurvature

theorem zero_interval (φ : ℝ → ℝ)
    (hφ : MonotoneOn φ (Set.Icc 0 1)) (h0 : φ 0 = 0)
    {b s : ℝ} (hb : b ∈ Set.Icc 0 1) (hz : φ b = 0)
    (hs : s ∈ Set.Icc 0 b) : φ s = 0 := by
  have hs1 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans hb.2⟩
  have hlo := hφ (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num) hs1 hs.1
  have hhi := hφ hs1 hb hs.2
  rw [h0] at hlo
  rw [hz] at hhi
  exact le_antisymm hhi hlo

theorem zero_or_positive_interval (φ : ℝ → ℝ)
    (hφ : MonotoneOn φ (Set.Icc 0 1)) (h0 : φ 0 = 0) :
    (∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ ∀ s ∈ Set.Icc 0 b, φ s = 0) ∨
    (∀ s ∈ Set.Ioc (0 : ℝ) 1, 0 < φ s) := by
  by_cases hz : ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ φ b = 0
  · obtain ⟨b, hb, hb1, hzb⟩ := hz
    exact Or.inl ⟨b, hb, hb1, fun s hs ↦ zero_interval φ hφ h0 ⟨hb.le, hb1⟩ hzb hs⟩
  · right
    intro s hs
    have hlo := hφ (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num) ⟨hs.1.le, hs.2⟩ hs.1.le
    rw [h0] at hlo
    exact lt_of_le_of_ne hlo (fun he ↦ hz ⟨s, hs.1, hs.2, he.symm⟩)

theorem eventually_zero_or_positive (φ : ℝ → ℝ)
    (hφ : MonotoneOn φ (Set.Icc 0 1)) (h0 : φ 0 = 0) :
    (∀ᶠ s in 𝓝[>] (0 : ℝ), φ s = 0) ∨
    (∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < φ s) := by
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  rcases zero_or_positive_interval φ hφ h0 with ⟨b, hb, _, hz⟩ | hp
  · left
    have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < b :=
      nhdsWithin_le_nhds (Iio_mem_nhds hb)
    filter_upwards [hpos, hsmall] with s hs hs1
    exact hz s ⟨hs.le, hs1.le⟩
  · right
    have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hpos, hsmall] with s hs hs1
    exact hp s ⟨hs, hs1.le⟩

theorem sampled_eventually_zero_or_positive (φ : ℝ → ℝ)
    (hφ : MonotoneOn φ (Set.Icc 0 1)) (h0 : φ 0 = 0)
    (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝[>] (0 : ℝ))) :
    (∀ᶠ n in atTop, φ (x n) = 0) ∨
    (∀ᶠ n in atTop, 0 < φ (x n)) := by
  rcases eventually_zero_or_positive φ hφ h0 with hz | hp
  · exact Or.inl (hx.eventually hz)
  · exact Or.inr (hx.eventually hp)

end RematZeroCurvature

#print axioms RematZeroCurvature.zero_interval
#print axioms RematZeroCurvature.zero_or_positive_interval
#print axioms RematZeroCurvature.eventually_zero_or_positive
#print axioms RematZeroCurvature.sampled_eventually_zero_or_positive
end

section
set_option autoImplicit true
open scoped BigOperators

set_option autoImplicit false

namespace RematDilationSynthesis

theorem sum_divisible_reduced_modulus {ι : Type*} (s : Finset ι) (c w : ι → ℕ)
    (D r t : ℕ) (hD : 0 < D) (hc : ∀ i ∈ s, Nat.ModEq D (r * c i) (w i))
    (hw : ∑ i ∈ s, w i = D * t) : D / Nat.gcd D r ∣ ∑ i ∈ s, c i := by
  have hsum := Nat.ModEq.sum hc
  rw [hw, ← Finset.mul_sum] at hsum
  have hz : Nat.ModEq D (r * ∑ i ∈ s, c i) (r * 0) := by
    simpa only [mul_zero] using hsum.trans ((dvd_mul_right D t).modEq_zero_nat)
  exact Nat.modEq_zero_iff_dvd.mp (hz.cancel_left_div_gcd hD)

theorem reduced_modulus_multiple_preserves (D r p : ℕ)
    (hp : D / Nat.gcd D r ∣ p) : D ∣ r * p := by
  obtain ⟨u, hu⟩ := Nat.gcd_dvd_right D r
  obtain ⟨v, hv⟩ := hp
  refine ⟨u * v, ?_⟩
  rw [hu, hv]
  have hD : Nat.gcd D r * (D / Nat.gcd D r) = D :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left D r)
  calc
    Nat.gcd D r * u * (D / Nat.gcd D r * v) =
        (Nat.gcd D r * (D / Nat.gcd D r)) * (u * v) := by ring
    _ = D * (u * v) := by rw [hD]

theorem padding_divisible (D r H S : ℕ) (hS : D / Nat.gcd D r ∣ S) :
    D / Nat.gcd D r ∣ H * D - S := by
  apply Nat.dvd_sub _ hS
  exact dvd_mul_of_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left D r)) H

theorem sum_bounded_by_dimension {ι : Type*} (s : Finset ι) (c : ι → ℕ)
    (D : ℕ) (hc : ∀ i ∈ s, c i ≤ D) : ∑ i ∈ s, c i ≤ s.card * D := by
  calc
    ∑ i ∈ s, c i ≤ ∑ _i ∈ s, D := Finset.sum_le_sum hc
    _ = s.card * D := by simp

def padded {ι : Type*} [DecidableEq ι] (c : ι → ℕ) (i₀ : ι) (p : ℕ) (i : ι) : ℕ :=
  c i + if i = i₀ then p else 0

theorem padded_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℕ)
    (i₀ : ι) (hi₀ : i₀ ∈ s) (p : ℕ) :
    ∑ i ∈ s, padded c i₀ p i = (∑ i ∈ s, c i) + p := by
  simp [padded, Finset.sum_add_distrib, hi₀]

theorem common_padding {ι : Type*} [DecidableEq ι] (s : Finset ι) (c w : ι → ℕ)
    (i₀ : ι) (hi₀ : i₀ ∈ s) (D r t H : ℕ) (hD : 0 < D)
    (hcpos : ∀ i ∈ s, 0 < c i)
    (hcmod : ∀ i ∈ s, Nat.ModEq D (r * c i) (w i))
    (hwsum : ∑ i ∈ s, w i = D * t) (hS : ∑ i ∈ s, c i ≤ H * D) :
    let C := padded c i₀ (H * D - ∑ i ∈ s, c i)
    (∑ i ∈ s, C i = H * D) ∧ (∀ i ∈ s, 0 < C i) ∧
      ∀ i ∈ s, Nat.ModEq D (r * C i) (w i) := by
  dsimp
  have hp : D ∣ r * (H * D - ∑ i ∈ s, c i) :=
    reduced_modulus_multiple_preserves D r _ (padding_divisible D r H _
      (sum_divisible_reduced_modulus s c w D r t hD hcmod hwsum))
  refine ⟨?_, ?_, ?_⟩
  · rw [padded_sum s c i₀ hi₀, Nat.add_sub_of_le hS]
  · intro i hi
    exact lt_of_lt_of_le (hcpos i hi) (Nat.le_add_right _ _)
  · intro i hi
    unfold padded
    by_cases he : i = i₀
    · rw [if_pos he, Nat.mul_add]
      simpa only [add_zero] using (hcmod i hi).add hp.modEq_zero_nat
    · simpa only [if_neg he, add_zero] using hcmod i hi

theorem progression_fractional_part (D H r c w j : ℕ) (hD : 0 < D) (hH : 0 < H)
    (hw : w < D) (hc : Nat.ModEq D (r * c) w) :
    Int.fract (((H * (r + j * D) : ℕ) : ℚ) * ((c : ℚ) / (H * D : ℕ))) =
      (w : ℚ) / D := by
  have hHq : (H : ℚ) ≠ 0 := by exact_mod_cast hH.ne'
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have he : (((H * (r + j * D) : ℕ) : ℚ) * ((c : ℚ) / (H * D : ℕ))) =
      (((r + j * D) * c : ℕ) : ℚ) / D := by
    push_cast
    field_simp
  rw [he, Int.fract_div_natCast_eq_div_natCast_mod]
  have hn : Nat.ModEq D ((r + j * D) * c) w := by
    have hj : Nat.ModEq D (r + j * D) r := by simp [Nat.ModEq]
    exact (hj.mul_right c).trans hc
  rw [hn, Nat.mod_eq_of_lt hw]

def scalarCost (ell : ℝ) (t : ℕ) (f : ℕ → ℝ) (m : ℕ) : ℝ :=
  (∑ i ∈ Finset.range m, (1 - 2 * f i)) + ell * ((t : ℝ) - m) ^ 2

theorem scalar_increment (ell : ℝ) (t m : ℕ) (f : ℕ → ℝ) :
    scalarCost ell t f (m + 1) - scalarCost ell t f m =
      1 - 2 * f m + ell * (-2 * t + 2 * m + 1) := by
  simp only [scalarCost, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem scalar_increment_lower (ell : ℝ) (t m : ℕ) (f : ℕ → ℝ)
    (hf : f m ≤ (1 - ell * (2 * t - 1)) / 2) :
    2 * ell * m ≤ scalarCost ell t f (m + 1) - scalarCost ell t f m := by
  rw [scalar_increment]
  linarith

theorem scalar_first_tie (ell : ℝ) (t : ℕ) (f : ℕ → ℝ)
    (hf : f 0 = (1 - ell * (2 * t - 1)) / 2) :
    scalarCost ell t f 1 = scalarCost ell t f 0 := by
  have h := scalar_increment ell t 0 f
  rw [hf] at h
  norm_num at h
  linarith

theorem scalar_cumulative_gap (ell : ℝ) (t : ℕ) (f : ℕ → ℝ)
    (hf : ∀ m, m < t → f m ≤ (1 - ell * (2 * t - 1)) / 2) :
    ∀ m, m ≤ t → scalarCost ell t f 0 + ell * m * ((m : ℝ) - 1) ≤ scalarCost ell t f m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    have hi := ih (by omega)
    have hd := scalar_increment_lower ell t m f (hf m (by omega))
    push_cast
    nlinarith

theorem scalar_excluded_gap (ell : ℝ) (hell : 0 < ell) (t : ℕ) (f : ℕ → ℝ)
    (hf : ∀ m, m < t → f m ≤ (1 - ell * (2 * t - 1)) / 2)
    (m : ℕ) (hm : 2 ≤ m) (hmt : m ≤ t) :
    scalarCost ell t f 0 + 2 * ell ≤ scalarCost ell t f m := by
  have h := scalar_cumulative_gap ell t f hf m hmt
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 2 ≤ (m : ℝ) * (m - 1) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hp hell.le
  nlinarith

theorem scalar_minimizers_exact (ell : ℝ) (hell : 0 < ell) (t : ℕ) (_ht : 0 < t)
    (f : ℕ → ℝ) (hf : ∀ m, m < t → f m ≤ (1 - ell * (2 * t - 1)) / 2)
    (hf₀ : f 0 = (1 - ell * (2 * t - 1)) / 2) (m : ℕ) (hmt : m ≤ t) :
    (∀ n : ℕ, n ≤ t → scalarCost ell t f m ≤ scalarCost ell t f n) ↔ m = 0 ∨ m = 1 := by
  have htie := scalar_first_tie ell t f hf₀
  have hmin n (hn : n ≤ t) : scalarCost ell t f 0 ≤ scalarCost ell t f n := by
    by_cases h0 : n = 0
    · rw [h0]
    by_cases h1 : n = 1
    · rw [h1, htie]
    have hg := scalar_excluded_gap ell hell t f hf n (by omega) hn
    linarith
  constructor
  · intro h
    by_contra hh
    have hm : 2 ≤ m := by omega
    have hg := scalar_excluded_gap ell hell t f hf m hm hmt
    have h0 := h 0 (Nat.zero_le t)
    linarith
  · rintro (rfl | rfl) n hn
    · exact hmin n hn
    · rw [htie]
      exact hmin n hn

theorem ceil_dilation_iff (S D H : ℕ) (hD : 0 < D) :
    Nat.ceil ((S : ℚ) / D) ≤ H ↔ S ≤ H * D := by
  rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hD : (0 : ℚ) < D)]
  exact_mod_cast Iff.rfl

theorem local_dilation_bounds (S D N : ℕ) (hD : 0 < D) (hS : 0 < S)
    (hbound : S ≤ N * D) :
    0 < Nat.ceil ((S : ℚ) / D) ∧ Nat.ceil ((S : ℚ) / D) ≤ N ∧
      S ≤ Nat.ceil ((S : ℚ) / D) * D := by
  refine ⟨?_, (ceil_dilation_iff S D N hD).mpr hbound,
    (ceil_dilation_iff S D _ hD).mp le_rfl⟩
  exact Nat.one_le_ceil_iff.mpr (div_pos (by exact_mod_cast hS) (by exact_mod_cast hD))

theorem two_stage_padding (S D H : ℕ) (hD : 0 < D)
    (hH : Nat.ceil ((S : ℚ) / D) ≤ H) :
    (Nat.ceil ((S : ℚ) / D) * D - S) + (H - Nat.ceil ((S : ℚ) / D)) * D = H * D - S := by
  have hl : S ≤ Nat.ceil ((S : ℚ) / D) * D := (ceil_dilation_iff S D _ hD).mp le_rfl
  have hmul := Nat.mul_le_mul_right D hH
  rw [Nat.sub_mul]
  omega

theorem common_dilation_simplex {ι : Type*} [DecidableEq ι] (s : Finset ι) (c w : ι → ℕ)
    (i₀ : ι) (hi₀ : i₀ ∈ s) (D r t H : ℕ) (hD : 0 < D) (hHpos : 0 < H)
    (hcpos : ∀ i ∈ s, 0 < c i)
    (hcmod : ∀ i ∈ s, Nat.ModEq D (r * c i) (w i))
    (hw : ∀ i ∈ s, w i < D) (hwsum : ∑ i ∈ s, w i = D * t)
    (hH : Nat.ceil (((∑ i ∈ s, c i : ℕ) : ℚ) / D) ≤ H) :
    ∃ C : ι → ℕ, (∑ i ∈ s, C i = H * D) ∧
      (∀ i ∈ s, 0 < (C i : ℚ) / (H * D : ℕ)) ∧
      (∑ i ∈ s, (C i : ℚ) / (H * D : ℕ) = 1) ∧
      (∀ j : ℕ, ∀ i ∈ s,
        Int.fract (((H * (r + j * D) : ℕ) : ℚ) * ((C i : ℚ) / (H * D : ℕ))) = (w i : ℚ) / D) ∧
      ∀ j : ℕ, (∑ i ∈ s, Int.fract (((H * (r + j * D) : ℕ) : ℚ) *
        ((C i : ℚ) / (H * D : ℕ)))) = t := by
  let C := padded c i₀ (H * D - ∑ i ∈ s, c i)
  obtain ⟨hCsum, hCpos, hCmod⟩ := common_padding s c w i₀ hi₀ D r t H hD hcpos hcmod hwsum
    ((ceil_dilation_iff _ D H hD).mp hH)
  have hHD : ((H * D : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hHpos hD).ne'
  have hfract j i (hi : i ∈ s) :
      Int.fract (((H * (r + j * D) : ℕ) : ℚ) * ((C i : ℚ) / (H * D : ℕ))) = (w i : ℚ) / D :=
    progression_fractional_part D H r (C i) (w i) j hD hHpos (hw i hi) (hCmod i hi)
  refine ⟨C, hCsum, ?_, ?_, hfract, ?_⟩
  · intro i hi
    exact div_pos (by exact_mod_cast hCpos i hi) (by exact_mod_cast Nat.mul_pos hHpos hD)
  · simp only [div_eq_mul_inv, ← Finset.sum_mul]
    have hs : (∑ i ∈ s, (C i : ℚ)) = ((H * D : ℕ) : ℚ) := by exact_mod_cast hCsum
    rw [hs, mul_inv_cancel₀ hHD]
  · intro j
    calc
      _ = ∑ i ∈ s, (w i : ℚ) / D := Finset.sum_congr rfl (fun i hi => hfract j i hi)
      _ = ((D * t : ℕ) : ℚ) / D := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        congr 1
        exact_mod_cast hwsum
      _ = t := by push_cast; field_simp

theorem common_height_max {ρ : Type*} (R : Finset ρ) (localHeight dimension : ρ → ℕ)
    (hR : R.Nonempty) (hpos : ∀ a ∈ R, 0 < localHeight a)
    (hbound : ∀ a ∈ R, localHeight a ≤ dimension a) :
    0 < R.sup localHeight ∧ R.sup localHeight ≤ R.sup dimension ∧
      ∀ a ∈ R, localHeight a ≤ R.sup localHeight := by
  obtain ⟨a, ha⟩ := hR
  refine ⟨lt_of_lt_of_le (hpos a ha) (Finset.le_sup ha), ?_, fun _ hb => Finset.le_sup hb⟩
  exact Finset.sup_le (fun b hb => (hbound b hb).trans (Finset.le_sup hb))

theorem full_cost_minimizers_gap (B ell : ℝ) (hell : 0 < ell) (t : ℕ) (ht : 0 < t)
    (f : ℕ → ℝ) (hf : ∀ m, m < t → f m ≤ (1 - ell * (2 * t - 1)) / 2)
    (hf₀ : f 0 = (1 - ell * (2 * t - 1)) / 2) :
    (B + scalarCost ell t f 1 = B + scalarCost ell t f 0) ∧
      (∀ m : ℕ, m ≤ t → ((∀ n : ℕ, n ≤ t →
        B + scalarCost ell t f m ≤ B + scalarCost ell t f n) ↔ m = 0 ∨ m = 1)) ∧
      ∀ m : ℕ, 2 ≤ m → m ≤ t →
        B + scalarCost ell t f 0 + 2 * ell ≤ B + scalarCost ell t f m := by
  refine ⟨congrArg (fun x => B + x) (scalar_first_tie ell t f hf₀), ?_, ?_⟩
  · intro m hm
    simpa only [add_le_add_iff_left] using scalar_minimizers_exact ell hell t ht f hf hf₀ m hm
  · intro m hm hmt
    have h := scalar_excluded_gap ell hell t f hf m hm hmt
    linarith

theorem threshold_profile (t n : ℕ) (q : ℚ) (hn : 0 < n) (hq : 0 < q)
    (hlower : (n : ℚ) * q < t) (hupper : (t : ℚ) ≤ (n + 1 : ℕ) * q) :
    let f : ℕ → ℚ := fun i => if i < n then q else (t : ℚ) - n * q
    f 0 = q ∧ (∑ i ∈ Finset.range (n + 1), f i = t) ∧
      ∀ i, i < n + 1 → 0 < f i ∧ f i ≤ q := by
  dsimp
  have hr : 0 < (t : ℚ) - n * q ∧ (t : ℚ) - n * q ≤ q := by
    push_cast at hupper
    constructor <;> linarith
  refine ⟨if_pos hn, ?_, ?_⟩
  · rw [Finset.sum_range_succ]
    have he : (∑ i ∈ Finset.range n, if i < n then q else (t : ℚ) - n * q) = n * q := by
      calc
        _ = ∑ _i ∈ Finset.range n, q := Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))
        _ = n * q := by simp
    rw [he, if_neg (Nat.lt_irrefl n)]
    ring
  · intro i _
    split_ifs
    · exact ⟨hq, le_rfl⟩
    · exact hr

theorem ceil_profile_bounds (t : ℕ) (ht : 0 < t) (q : ℚ) (hq : 0 < q) (hq₁ : q < 1) :
    let N := Nat.ceil ((t : ℚ) / q)
    2 ≤ N ∧ ((N - 1 : ℕ) : ℚ) * q < t ∧ (t : ℚ) ≤ (N : ℚ) * q := by
  dsimp
  have htq : (1 : ℚ) ≤ t := by exact_mod_cast ht
  have hN : 2 ≤ Nat.ceil ((t : ℚ) / q) := by
    apply Nat.add_one_le_ceil_iff.mpr
    apply (lt_div_iff₀ hq).mpr
    simpa only [Nat.cast_one, one_mul] using hq₁.trans_le htq
  refine ⟨hN, ?_, ?_⟩
  · apply (lt_div_iff₀ hq).mp
    exact Nat.lt_ceil.mp (show Nat.ceil ((t : ℚ) / q) - 1 < Nat.ceil ((t : ℚ) / q) by omega)
  · exact (div_le_iff₀ hq).mp (Nat.le_ceil ((t : ℚ) / q))

theorem ceil_threshold_profile (t : ℕ) (ht : 0 < t) (q : ℚ) (hq : 0 < q) (hq₁ : q < 1) :
    let N := Nat.ceil ((t : ℚ) / q)
    let f : ℕ → ℚ := fun i => if i < N - 1 then q else (t : ℚ) - (N - 1 : ℕ) * q
    2 ≤ N ∧ f 0 = q ∧ (∑ i ∈ Finset.range N, f i = t) ∧
      ∀ i, i < N → 0 < f i ∧ f i ≤ q := by
  dsimp
  obtain ⟨hN, hl, hu⟩ := ceil_profile_bounds t ht q hq hq₁
  have he : Nat.ceil ((t : ℚ) / q) - 1 + 1 = Nat.ceil ((t : ℚ) / q) := by omega
  have h := threshold_profile t (Nat.ceil ((t : ℚ) / q) - 1) q (by omega) hq hl (by simpa only [he] using hu)
  exact ⟨hN, by simpa only [he] using h⟩

theorem ceil_dimension_lower_bound {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (t : ℕ) (q : ℚ) (hq : 0 < q) (hsum : ∑ i ∈ s, f i = t)
    (hf : ∀ i ∈ s, f i ≤ q) : Nat.ceil ((t : ℚ) / q) ≤ s.card := by
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ hq).mpr
  calc
    (t : ℚ) = ∑ i ∈ s, f i := hsum.symm
    _ ≤ ∑ _i ∈ s, q := Finset.sum_le_sum hf
    _ = (s.card : ℚ) * q := by simp

end RematDilationSynthesis

#print axioms RematDilationSynthesis.sum_divisible_reduced_modulus
#print axioms RematDilationSynthesis.reduced_modulus_multiple_preserves
#print axioms RematDilationSynthesis.padding_divisible
#print axioms RematDilationSynthesis.sum_bounded_by_dimension
#print axioms RematDilationSynthesis.padded_sum
#print axioms RematDilationSynthesis.common_padding
#print axioms RematDilationSynthesis.progression_fractional_part
#print axioms RematDilationSynthesis.scalar_increment
#print axioms RematDilationSynthesis.scalar_increment_lower
#print axioms RematDilationSynthesis.scalar_first_tie
#print axioms RematDilationSynthesis.scalar_cumulative_gap
#print axioms RematDilationSynthesis.scalar_excluded_gap
#print axioms RematDilationSynthesis.scalar_minimizers_exact
#print axioms RematDilationSynthesis.ceil_dilation_iff
#print axioms RematDilationSynthesis.local_dilation_bounds
#print axioms RematDilationSynthesis.two_stage_padding
#print axioms RematDilationSynthesis.common_dilation_simplex
#print axioms RematDilationSynthesis.common_height_max
#print axioms RematDilationSynthesis.full_cost_minimizers_gap
#print axioms RematDilationSynthesis.threshold_profile
#print axioms RematDilationSynthesis.ceil_profile_bounds
#print axioms RematDilationSynthesis.ceil_threshold_profile
#print axioms RematDilationSynthesis.ceil_dimension_lower_bound

namespace RematDilationArithmetic

open RematDilationSynthesis

theorem positive_congruence_representative (D r w : ℕ) (hD : 0 < D)
    (hwpos : 0 < w) (hwlt : w < D) (hgw : Nat.gcd D r ∣ w) :
    ∃ c : ℕ, 0 < c ∧ c < D / Nat.gcd D r ∧ Nat.ModEq D (r * c) w := by
  have hglt : Nat.gcd D r < D := (Nat.le_of_dvd hwpos hgw).trans_lt hwlt
  obtain ⟨u, _, hu⟩ := Nat.exists_mul_mod_eq_gcd (n := r) (k := D)
    (by simpa only [Nat.gcd_comm] using hglt)
  have humod : Nat.ModEq D (r * u) (Nat.gcd D r) := by
    change (r * u) % D = Nat.gcd D r % D
    rw [Nat.mod_eq_of_lt hglt, hu, Nat.gcd_comm]
  let d := D / Nat.gcd D r
  have hdpos : 0 < d := Nat.div_pos (Nat.le_of_dvd hD (Nat.gcd_dvd_left D r))
    (Nat.gcd_pos_of_pos_left r hD)
  let z := u * (w / Nat.gcd D r)
  have hzmod : Nat.ModEq D (r * z) w := by
    have h := humod.mul_right (w / Nat.gcd D r)
    simpa only [z, mul_assoc, Nat.mul_div_cancel' hgw] using h
  have hp : D ∣ r * (d * (z / d)) :=
    reduced_modulus_multiple_preserves D r _ (dvd_mul_right d (z / d))
  have hsame : Nat.ModEq D (r * (z % d)) (r * z) := by
    conv_rhs => rw [← Nat.mod_add_div z d, Nat.mul_add]
    simpa only [add_zero] using hp.zero_modEq_nat.add_left (r * (z % d))
  have hcmod : Nat.ModEq D (r * (z % d)) w := hsame.trans hzmod
  refine ⟨z % d, ?_, Nat.mod_lt z hdpos, hcmod⟩
  apply Nat.pos_of_ne_zero
  intro hc0
  have hw0 : w = 0 := by
    have h := hcmod
    rw [hc0, mul_zero] at h
    change 0 % D = w % D at h
    simpa only [Nat.zero_mod, Nat.mod_eq_of_lt hwlt] using h.symm
  exact hwpos.ne' hw0

theorem positive_congruence_vector {ι : Type*} (s : Finset ι) (D r : ℕ) (w : ι → ℕ)
    (hD : 0 < D) (hw : ∀ i ∈ s, 0 < w i ∧ w i < D ∧ Nat.gcd D r ∣ w i) :
    ∃ c : ι → ℕ, ∀ i ∈ s, 0 < c i ∧ c i < D / Nat.gcd D r ∧ Nat.ModEq D (r * c i) (w i) := by
  classical
  have hex i : ∃ c : ℕ, i ∈ s → 0 < c ∧ c < D / Nat.gcd D r ∧ Nat.ModEq D (r * c) (w i) := by
    by_cases hi : i ∈ s
    · obtain ⟨c, hc⟩ := positive_congruence_representative D r (w i) hD
        (hw i hi).1 (hw i hi).2.1 (hw i hi).2.2
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose c hc using hex
  exact ⟨c, hc⟩

theorem lattice_profile_all_heights {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (hs : s.Nonempty) (D r t : ℕ) (w : ι → ℕ) (hD : 0 < D)
    (hw : ∀ i ∈ s, 0 < w i ∧ w i < D ∧ Nat.gcd D r ∣ w i)
    (hsum : ∑ i ∈ s, w i = D * t) :
    ∃ c : ι → ℕ,
      (∀ i ∈ s, 0 < c i ∧ c i < D / Nat.gcd D r ∧ Nat.ModEq D (r * c i) (w i)) ∧
      (0 < Nat.ceil (((∑ i ∈ s, c i : ℕ) : ℚ) / D)) ∧
      (Nat.ceil (((∑ i ∈ s, c i : ℕ) : ℚ) / D) ≤ s.card) ∧
      ∀ H : ℕ, Nat.ceil (((∑ i ∈ s, c i : ℕ) : ℚ) / D) ≤ H →
        ∃ C : ι → ℕ, (∑ i ∈ s, C i = H * D) ∧
          (∀ i ∈ s, 0 < (C i : ℚ) / (H * D : ℕ)) ∧
          (∑ i ∈ s, (C i : ℚ) / (H * D : ℕ) = 1) ∧
          (∀ j : ℕ, ∀ i ∈ s,
            Int.fract (((H * (r + j * D) : ℕ) : ℚ) * ((C i : ℚ) / (H * D : ℕ))) = (w i : ℚ) / D) ∧
          ∀ j : ℕ, (∑ i ∈ s, Int.fract (((H * (r + j * D) : ℕ) : ℚ) *
            ((C i : ℚ) / (H * D : ℕ)))) = t := by
  obtain ⟨c, hc⟩ := positive_congruence_vector s D r w hD hw
  obtain ⟨i₀, hi₀⟩ := hs
  have hSpos : 0 < ∑ i ∈ s, c i :=
    (hc i₀ hi₀).1.trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi₀)
  have hSbound : ∑ i ∈ s, c i ≤ s.card * D := sum_bounded_by_dimension s c D
    (fun i hi => (hc i hi).2.1.le.trans (Nat.div_le_self D (Nat.gcd D r)))
  obtain ⟨hlpos, hlbound, _⟩ := local_dilation_bounds (∑ i ∈ s, c i) D s.card hD hSpos hSbound
  refine ⟨c, hc, hlpos, hlbound, fun H hH => ?_⟩
  exact common_dilation_simplex s c w i₀ hi₀ D r t H hD (hlpos.trans_le hH)
    (fun i hi => (hc i hi).1) (fun i hi => (hc i hi).2.2) (fun i hi => (hw i hi).2.1) hsum hH

theorem least_representative_le (D r w c C : ℕ) (hD : 0 < D)
    (hc : c < D / Nat.gcd D r) (hmod : Nat.ModEq D (r * c) w)
    (hCmod : Nat.ModEq D (r * C) w) : c ≤ C := by
  have h := (hmod.trans hCmod.symm).cancel_left_div_gcd hD
  change c % (D / Nat.gcd D r) = C % (D / Nat.gcd D r) at h
  rw [Nat.mod_eq_of_lt hc] at h
  rw [h]
  exact Nat.mod_le C _

theorem least_height_necessary {ι : Type*} (s : Finset ι) (D r H : ℕ) (w c C : ι → ℕ)
    (hD : 0 < D) (hc : ∀ i ∈ s, c i < D / Nat.gcd D r ∧ Nat.ModEq D (r * c i) (w i))
    (hC : ∀ i ∈ s, Nat.ModEq D (r * C i) (w i)) (hsum : ∑ i ∈ s, C i = H * D) :
    Nat.ceil (((∑ i ∈ s, c i : ℕ) : ℚ) / D) ≤ H := by
  apply (ceil_dilation_iff _ D H hD).mpr
  rw [← hsum]
  exact Finset.sum_le_sum (fun i hi => least_representative_le D r (w i) (c i) (C i) hD
    (hc i hi).1 (hc i hi).2 (hC i hi))

end RematDilationArithmetic

#print axioms RematDilationArithmetic.positive_congruence_representative
#print axioms RematDilationArithmetic.positive_congruence_vector
#print axioms RematDilationArithmetic.lattice_profile_all_heights
#print axioms RematDilationArithmetic.least_representative_le
#print axioms RematDilationArithmetic.least_height_necessary
end

section
set_option autoImplicit true
set_option autoImplicit false

namespace RematCofinalEmbedding

def rough (T M : ℕ) : ℕ := (M.primeFactorsList.filter fun p => T < p).prod

def smooth (T M : ℕ) : ℕ := (M.primeFactorsList.filter fun p => p ≤ T).prod

theorem rough_smooth (T : ℕ) {M : ℕ} (hM : 0 < M) :
    rough T M * smooth T M = M := by
  have h := List.prod_map_filter_mul_prod_map_filter_not (fun p : ℕ => T < p) id M.primeFactorsList
  simpa [rough, smooth, Nat.not_lt, Nat.prod_primeFactorsList hM.ne'] using h

theorem rough_pos (T M : ℕ) : 0 < rough T M := by
  apply Nat.pos_of_ne_zero
  apply List.prod_ne_zero
  intro h
  have hp := Nat.pos_of_mem_primeFactorsList (List.mem_of_mem_filter h)
  omega

theorem smooth_pos (T M : ℕ) : 0 < smooth T M := by
  apply Nat.pos_of_ne_zero
  apply List.prod_ne_zero
  intro h
  have hp := Nat.pos_of_mem_primeFactorsList (List.mem_of_mem_filter h)
  omega

theorem rough_mul (T : ℕ) {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    rough T (M * N) = rough T M * rough T N := by
  unfold rough
  have h := (Nat.perm_primeFactorsList_mul hM.ne' hN.ne').filter (fun p => decide (T < p))
  simpa using h.prod_eq

theorem rough_small {T t : ℕ} (ht : t ≤ T) : rough T t = 1 := by
  unfold rough
  suffices t.primeFactorsList.filter (fun p => T < p) = [] by simp [this]
  apply List.filter_eq_nil_iff.mpr
  intro p hp
  have hpt := Nat.le_of_mem_primeFactorsList hp
  simp only [decide_eq_true_eq, not_lt]
  omega

theorem rough_coprime (T M : ℕ) : (rough T M).Coprime T.factorial := by
  by_contra h
  obtain ⟨p, hp, hpr, hpf⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hmem := mem_list_primes_of_dvd_prod hp.prime
    (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime) hpr
  have hgt : T < p := by simpa using (List.mem_filter.mp hmem).2
  have hle : p ≤ T := (hp.dvd_factorial).mp hpf
  omega

theorem rough_of_coprime {T M : ℕ} (hM : 0 < M) (hcop : M.Coprime T.factorial) :
    rough T M = M := by
  unfold rough
  rw [List.filter_eq_self.mpr, Nat.prod_primeFactorsList hM.ne']
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactorsList hp
  have hdiv : p ∣ M := (Nat.mem_primeFactorsList hM.ne').mp hp |>.2
  simp only [decide_eq_true_eq]
  by_contra h
  have hf := Nat.dvd_factorial hprime.pos (Nat.le_of_not_gt h)
  exact hprime.ne_one (Nat.eq_one_of_dvd_coprimes hcop hdiv hf)

theorem smooth_coprime {T M Q : ℕ} (hQ : Q.Coprime T.factorial) :
    (smooth T M).Coprime Q := by
  by_contra h
  obtain ⟨p, hp, hps, hpQ⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hmem := mem_list_primes_of_dvd_prod hp.prime
    (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime) hps
  have hle : p ≤ T := by simpa using (List.mem_filter.mp hmem).2
  have hf := Nat.dvd_factorial hp.pos hle
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hQ hpQ hf)

theorem rough_smooth_eq_one (T M : ℕ) : rough T (smooth T M) = 1 := by
  unfold rough
  suffices (smooth T M).primeFactorsList.filter (fun p => T < p) = [] by simp [this]
  apply List.filter_eq_nil_iff.mpr
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactorsList hp
  have hdiv : p ∣ smooth T M := (Nat.mem_primeFactorsList (smooth_pos T M).ne').mp hp |>.2
  have hmem := mem_list_primes_of_dvd_prod hprime.prime
    (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime) hdiv
  have hle : p ≤ T := by simpa using (List.mem_filter.mp hmem).2
  simpa only [decide_eq_true_eq, not_lt] using hle

theorem representation_rough_unique {T t u M N : ℕ}
    (ht : 0 < t) (hu : 0 < u) (htT : t ≤ T) (huT : u ≤ T)
    (hM : 0 < M) (hN : 0 < N)
    (heq : (t : ℝ) / M = (u : ℝ) / N) : rough T M = rough T N := by
  have he : t * N = u * M := by
    exact_mod_cast (div_eq_div_iff (by positivity : (M : ℝ) ≠ 0)
      (by positivity : (N : ℝ) ≠ 0)).mp heq
  have hr := congrArg (rough T) he
  rw [rough_mul T ht hN, rough_mul T hu hM, rough_small htT, rough_small huT,
    one_mul, one_mul] at hr
  exact hr.symm

theorem modEq_coprime {a b n : ℕ} (h : a ≡ b [MOD n]) (hb : b.Coprime n) :
    a.Coprime n := by
  change a.gcd n = 1
  rw [Nat.gcd_comm a n, Nat.gcd_rec n a, h, ← Nat.gcd_rec n b, Nat.gcd_comm n b]
  exact hb

def replacement (D T Q : ℕ) (hcop : (D * T.factorial).Coprime Q) (q : ℕ) : ℕ :=
  (Nat.chineseRemainder hcop q 1).val + (D * T.factorial * Q) * (q + 1)

theorem replacement_properties {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) (q : ℕ) :
    q < replacement D T Q hcop q ∧
    replacement D T Q hcop q ≡ q [MOD D * T.factorial] ∧
    replacement D T Q hcop q ≡ 1 [MOD Q] := by
  have hL : 0 < D * T.factorial * Q := Nat.mul_pos (Nat.mul_pos hD (Nat.factorial_pos T)) hQ
  constructor
  · unfold replacement
    have hle : q + 1 ≤ (D * T.factorial * Q) * (q + 1) := by nlinarith
    omega
  constructor
  · exact (Nat.chineseRemainder hcop q 1).property.1.add
      (show (D * T.factorial * Q) * (q + 1) ≡ 0 [MOD D * T.factorial] from
        (dvd_mul_of_dvd_left (Nat.dvd_mul_right _ _) _).modEq_zero_nat) |>.trans (by simp only [Nat.add_zero]; rfl)
  · exact (Nat.chineseRemainder hcop q 1).property.2.add
      (show (D * T.factorial * Q) * (q + 1) ≡ 0 [MOD Q] from
        (dvd_mul_of_dvd_left (Nat.dvd_mul_left _ _) _).modEq_zero_nat) |>.trans (by simp only [Nat.add_zero]; rfl)

theorem replacement_strictMono {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) : StrictMono (replacement D T Q hcop) := by
  intro q r hqr
  have hL : 0 < D * T.factorial * Q := Nat.mul_pos (Nat.mul_pos hD (Nat.factorial_pos T)) hQ
  have hb := Nat.chineseRemainder_lt_mul hcop q 1
    (Nat.mul_pos hD (Nat.factorial_pos T)).ne' hQ.ne'
  unfold replacement
  have hqr' : q + 2 ≤ r + 1 := by omega
  have hmul := Nat.mul_le_mul_left (D * T.factorial * Q) hqr'
  nlinarith

theorem replacement_coprime {D T Q q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) (hq : q.Coprime T.factorial) :
    (replacement D T Q hcop q).Coprime T.factorial ∧
    (replacement D T Q hcop q).Coprime Q := by
  have hp := replacement_properties hD hQ hcop q
  exact ⟨modEq_coprime (hp.2.1.of_dvd (Nat.dvd_mul_left _ _)) hq,
    modEq_coprime hp.2.2 (Nat.coprime_one_left Q)⟩

def HasRep (T : ℕ) (x : ℝ) : Prop :=
  ∃ M t : ℕ, 0 < M ∧ 0 < t ∧ t ≤ T ∧ x = (t : ℝ) / M

noncomputable def core (T : ℕ) (x : ℝ) : ℕ := by
  classical
  exact if h : HasRep T x then rough T (Classical.choose h) else 1

theorem core_fraction {T t M : ℕ} (ht : 0 < t) (htT : t ≤ T) (hM : 0 < M) :
    core T ((t : ℝ) / M) = rough T M := by
  have h : HasRep T ((t : ℝ) / M) := ⟨M, t, hM, ht, htT, rfl⟩
  simp only [core, dif_pos h]
  obtain ⟨u, hN, hu, huT, heq⟩ := Classical.choose_spec h
  exact representation_rough_unique hu ht huT htT hN hM heq.symm

theorem core_pos (T : ℕ) (x : ℝ) : 0 < core T x := by
  unfold core
  split
  · exact rough_pos _ _
  · exact Nat.zero_lt_one

def newMesh (D T Q : ℕ) (hcop : (D * T.factorial).Coprime Q) (M : ℕ) : ℕ :=
  smooth T M * replacement D T Q hcop (rough T M)

theorem newMesh_properties {D T Q M : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) (hM : 0 < M) :
    M < newMesh D T Q hcop M ∧
    newMesh D T Q hcop M ≡ M [MOD D] ∧
    (newMesh D T Q hcop M).Coprime Q ∧
    rough T (newMesh D T Q hcop M) = replacement D T Q hcop (rough T M) := by
  have hp := replacement_properties hD hQ hcop (rough T M)
  have hc := replacement_coprime hD hQ hcop (rough_coprime T M)
  have hr : 0 < replacement D T Q hcop (rough T M) := lt_trans (rough_pos T M) hp.1
  have hQT : Q.Coprime T.factorial := hcop.symm.of_dvd_right (Nat.dvd_mul_left _ _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold newMesh
    nth_rw 1 [← rough_smooth T hM]
    rw [mul_comm (rough T M)]
    exact Nat.mul_lt_mul_of_pos_left hp.1 (smooth_pos T M)
  · have hh := (hp.2.1.of_dvd (Nat.dvd_mul_right D T.factorial)).mul_left (smooth T M)
    simpa [newMesh, mul_comm (smooth T M), rough_smooth T hM] using hh
  · exact (smooth_coprime (M := M) hQT).mul_left hc.2
  · rw [newMesh, rough_mul T (smooth_pos T M) hr, rough_smooth_eq_one,
      rough_of_coprime hr hc.1, one_mul]

noncomputable def embedding (D T Q : ℕ) (hcop : (D * T.factorial).Coprime Q)
    (x : ℝ) : ℝ := (core T x : ℝ) / replacement D T Q hcop (core T x) * x

theorem embedding_zero (D T Q : ℕ) (hcop : (D * T.factorial).Coprime Q) :
    embedding D T Q hcop 0 = 0 := by simp [embedding]

theorem embedding_fraction {D T Q t M : ℕ} (_hD : 0 < D) (_hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) (hM : 0 < M) (htT : t ≤ T) :
    embedding D T Q hcop ((t : ℝ) / M) = (t : ℝ) / newMesh D T Q hcop M := by
  by_cases ht : t = 0
  · simp [ht, embedding_zero]
  have htp : 0 < t := Nat.pos_of_ne_zero ht
  rw [embedding, core_fraction htp htT hM, newMesh, Nat.cast_mul]
  have hr : (rough T M : ℝ) ≠ 0 := by exact_mod_cast (rough_pos T M).ne'
  have hs : (smooth T M : ℝ) ≠ 0 := by exact_mod_cast (smooth_pos T M).ne'
  have he : (M : ℝ) = (rough T M : ℝ) * smooth T M := by
    exact_mod_cast (rough_smooth T hM).symm
  rw [he]
  field_simp

theorem embedding_scale_bounds {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) (x : ℝ) :
    0 < (core T x : ℝ) / replacement D T Q hcop (core T x) ∧
    (core T x : ℝ) / replacement D T Q hcop (core T x) < 1 := by
  have hc : (0 : ℝ) < core T x := by exact_mod_cast core_pos T x
  have hr : (core T x : ℝ) < replacement D T Q hcop (core T x) := by
    exact_mod_cast (replacement_properties hD hQ hcop (core T x)).1
  exact ⟨div_pos hc (lt_trans hc hr), (div_lt_one (lt_trans hc hr)).mpr hr⟩

theorem embedding_abs_bound {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) (x : ℝ) :
    |embedding D T Q hcop x| ≤ |x| := by
  have h := embedding_scale_bounds hD hQ hcop x
  rw [embedding, abs_mul, abs_of_pos h.1]
  exact mul_le_of_le_one_left (abs_nonneg x) h.2.le

theorem embedding_pos {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) {x : ℝ} (hx : 0 < x) :
    0 < embedding D T Q hcop x :=
  mul_pos (embedding_scale_bounds hD hQ hcop x).1 hx

theorem embedding_injective_reps {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) {x y : ℝ}
    (hx : HasRep T x) (hy : HasRep T y)
    (he : embedding D T Q hcop x = embedding D T Q hcop y) : x = y := by
  obtain ⟨M, t, hM, ht, htT, rfl⟩ := hx
  obtain ⟨N, u, hN, hu, huT, rfl⟩ := hy
  have hpM := newMesh_properties hD hQ hcop hM
  have hpN := newMesh_properties hD hQ hcop hN
  have he' := he
  rw [embedding_fraction hD hQ hcop hM htT, embedding_fraction hD hQ hcop hN huT] at he'
  have hr := representation_rough_unique ht hu htT huT (lt_trans hM hpM.1)
    (lt_trans hN hpN.1) he'
  rw [hpM.2.2.2, hpN.2.2.2] at hr
  have hc := (replacement_strictMono hD hQ hcop).injective hr
  have hscale := (embedding_scale_bounds hD hQ hcop ((t : ℝ) / M)).1.ne'
  rw [core_fraction ht htT hM] at hscale
  rw [embedding, embedding, core_fraction ht htT hM, core_fraction hu huT hN, ← hc] at he
  exact mul_left_cancel₀ hscale he

theorem embedding_injOn {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) :
    Set.InjOn (embedding D T Q hcop) {x | x = 0 ∨ HasRep T x} := by
  intro x hx y hy he
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · rfl
    · obtain ⟨M, t, hM, ht, _, rfl⟩ := hy
      have hp := embedding_pos hD hQ hcop
        (div_pos (Nat.cast_pos.mpr ht) (Nat.cast_pos.mpr hM))
      rw [embedding_zero] at he
      linarith
  · rcases hy with rfl | hy
    · obtain ⟨M, t, hM, ht, _, rfl⟩ := hx
      have hp := embedding_pos hD hQ hcop
        (div_pos (Nat.cast_pos.mpr ht) (Nat.cast_pos.mpr hM))
      rw [embedding_zero] at he
      linarith
    · exact embedding_injective_reps hD hQ hcop hx hy he

theorem embedding_continuousAt_zero {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) : ContinuousAt (embedding D T Q hcop) 0 := by
  rw [Metric.continuousAt_iff]
  intro e he
  refine ⟨e, he, ?_⟩
  intro x hx
  rw [embedding_zero, Real.dist_eq, sub_zero]
  rw [Real.dist_eq, sub_zero] at hx
  exact lt_of_le_of_lt (embedding_abs_bound hD hQ hcop x) hx

def Samples (T : ℕ) : Set ℝ := {x | x = 0 ∨ (HasRep T x ∧ x ≤ 1)}

def RestrictedSamples (T Q : ℕ) : Set ℝ :=
  {x | x = 0 ∨ ∃ M t : ℕ, 0 < t ∧ t ≤ T ∧ t ≤ M ∧ M.Coprime Q ∧ x = (t : ℝ) / M}

theorem embedding_nonneg_le {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ embedding D T Q hcop x ∧ embedding D T Q hcop x ≤ x := by
  have h := embedding_scale_bounds hD hQ hcop x
  exact ⟨mul_nonneg h.1.le hx, mul_le_of_le_one_left hx h.2.le⟩

theorem embedding_maps_samples {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) :
    Set.MapsTo (embedding D T Q hcop) (Samples T) (RestrictedSamples T Q) := by
  intro x hx
  rcases hx with rfl | ⟨⟨M, t, hM, ht, htT, rfl⟩, hx1⟩
  · exact Or.inl (embedding_zero D T Q hcop)
  have htM : t ≤ M := by
    have hh := (div_le_one (Nat.cast_pos.mpr hM : (0 : ℝ) < M)).mp hx1
    exact_mod_cast hh
  have hp := newMesh_properties hD hQ hcop hM
  exact Or.inr ⟨newMesh D T Q hcop M, t, ht, htT, le_trans htM hp.1.le,
    hp.2.2.1, embedding_fraction hD hQ hcop hM htT⟩

theorem adjacent_record_image {D T Q t M r : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) (ht : 0 < t) (htT : t ≤ T)
    (htM : t ≤ M) (hMr : M ≡ r [MOD D]) :
    ∃ M' : ℕ, M < M' ∧ t ≤ M' ∧ M'.Coprime Q ∧ M' ≡ r [MOD D] ∧
      embedding D T Q hcop ((t : ℝ) / M) = (t : ℝ) / M' ∧
      embedding D T Q hcop (((t - 1 : ℕ) : ℝ) / M) = ((t - 1 : ℕ) : ℝ) / M' := by
  have hM := lt_of_lt_of_le ht htM
  have hp := newMesh_properties hD hQ hcop hM
  exact ⟨newMesh D T Q hcop M, hp.1, le_trans htM hp.1.le, hp.2.2.1,
    hp.2.1.trans hMr, embedding_fraction hD hQ hcop hM htT,
    embedding_fraction hD hQ hcop hM (le_trans (Nat.sub_le t 1) htT)⟩

theorem cofinal_arithmetic_embedding {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) :
    ∃ (F : ℝ → ℝ) (L : ℕ → ℕ), F 0 = 0 ∧ Set.InjOn F (Samples T) ∧
      ContinuousAt F 0 ∧ Set.MapsTo F (Samples T) (RestrictedSamples T Q) ∧
      (∀ x : ℝ, |F x| ≤ |x|) ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ F x ∧ F x ≤ x) ∧
      (∀ M : ℕ, 0 < M → M < L M ∧ L M ≡ M [MOD D] ∧ (L M).Coprime Q ∧
        ∀ t : ℕ, t ≤ T → F ((t : ℝ) / M) = (t : ℝ) / L M) := by
  refine ⟨embedding D T Q hcop, newMesh D T Q hcop, embedding_zero D T Q hcop,
    ?_, embedding_continuousAt_zero hD hQ hcop,
    embedding_maps_samples hD hQ hcop, embedding_abs_bound hD hQ hcop,
    fun _ hx => embedding_nonneg_le hD hQ hcop hx, ?_⟩
  · exact (embedding_injOn hD hQ hcop).mono (fun _ hx => hx.imp_right And.left)
  · intro M hM
    have hp := newMesh_properties hD hQ hcop hM
    exact ⟨hp.1, hp.2.1, hp.2.2.1, fun t ht => embedding_fraction hD hQ hcop hM ht⟩

theorem adjacent_relation_pullback {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) (u : ℝ → ℝ) (R : ℕ → ℕ → ℝ → ℝ → Prop)
    (hR : ∀ t r M : ℕ, 0 < t → t ≤ T → t ≤ M → M ≡ r [MOD D] → M.Coprime Q →
      R t r (u ((t : ℝ) / M)) (u (((t - 1 : ℕ) : ℝ) / M))) :
    ∀ t r M : ℕ, 0 < t → t ≤ T → t ≤ M → M ≡ r [MOD D] →
      R t r ((u ∘ embedding D T Q hcop) ((t : ℝ) / M))
        ((u ∘ embedding D T Q hcop) (((t - 1 : ℕ) : ℝ) / M)) := by
  intro t r M ht htT htM hMr
  obtain ⟨M', _, htM', hMc, hMr', he1, he2⟩ := adjacent_record_image hD hQ hcop ht htT htM hMr
  simpa only [Function.comp_apply, he1, he2] using hR t r M' ht htT htM' hMr' hMc

theorem continuous_potential_pullback_zero {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) {u : ℝ → ℝ} (hu : ContinuousAt u 0) :
    ContinuousAt (u ∘ embedding D T Q hcop) 0 := by
  apply ContinuousAt.comp _ (embedding_continuousAt_zero hD hQ hcop)
  simpa only [embedding_zero] using hu

theorem finite_residue_refinement {D Q r M : ℕ} (hD : 0 < D) (hQ : 0 < Q) :
    (M ≡ r [MOD D] ∧ M.Coprime Q) ↔
    ∃ r' : ℕ, r' < D * Q ∧ r' ≡ r [MOD D] ∧ r'.Coprime Q ∧ M ≡ r' [MOD D * Q] := by
  constructor
  · rintro ⟨hMr, hMQ⟩
    have hr := Nat.mod_modEq M (D * Q)
    exact ⟨M % (D * Q), Nat.mod_lt M (Nat.mul_pos hD hQ),
      (hr.of_dvd (Nat.dvd_mul_right D Q)).trans hMr,
      modEq_coprime (hr.of_dvd (Nat.dvd_mul_left Q D)) hMQ, hr.symm⟩
  · rintro ⟨r', _, hrr, hrQ, hMr⟩
    exact ⟨(hMr.of_dvd (Nat.dvd_mul_right D Q)).trans hrr,
      modEq_coprime (hMr.of_dvd (Nat.dvd_mul_left Q D)) hrQ⟩

theorem continuous_adjacent_feasibility_iff {D T Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    (hcop : (D * T.factorial).Coprime Q) (R : ℕ → ℕ → ℝ → ℝ → Prop) :
    (∃ u : ℝ → ℝ, ContinuousAt u 0 ∧ u 0 = 0 ∧
      ∀ t r M : ℕ, 0 < t → t ≤ T → t ≤ M → M ≡ r [MOD D] →
        R t r (u ((t : ℝ) / M)) (u (((t - 1 : ℕ) : ℝ) / M))) ↔
    (∃ u : ℝ → ℝ, ContinuousAt u 0 ∧ u 0 = 0 ∧
      ∀ t r M : ℕ, 0 < t → t ≤ T → t ≤ M → M ≡ r [MOD D] → M.Coprime Q →
        R t r (u ((t : ℝ) / M)) (u (((t - 1 : ℕ) : ℝ) / M))) := by
  constructor
  · rintro ⟨u, hu, hz, hR⟩
    exact ⟨u, hu, hz, fun t r M ht htT htM hMr _ => hR t r M ht htT htM hMr⟩
  · rintro ⟨u, hu, hz, hR⟩
    exact ⟨u ∘ embedding D T Q hcop, continuous_potential_pullback_zero hD hQ hcop hu,
      by simpa only [Function.comp_apply, embedding_zero] using hz,
      adjacent_relation_pullback hD hQ hcop u R hR⟩

end RematCofinalEmbedding

#print axioms RematCofinalEmbedding.rough_smooth
#print axioms RematCofinalEmbedding.rough_pos
#print axioms RematCofinalEmbedding.smooth_pos
#print axioms RematCofinalEmbedding.rough_mul
#print axioms RematCofinalEmbedding.rough_small
#print axioms RematCofinalEmbedding.rough_coprime
#print axioms RematCofinalEmbedding.rough_of_coprime
#print axioms RematCofinalEmbedding.smooth_coprime
#print axioms RematCofinalEmbedding.rough_smooth_eq_one
#print axioms RematCofinalEmbedding.representation_rough_unique
#print axioms RematCofinalEmbedding.modEq_coprime
#print axioms RematCofinalEmbedding.replacement_properties
#print axioms RematCofinalEmbedding.replacement_strictMono
#print axioms RematCofinalEmbedding.replacement_coprime
#print axioms RematCofinalEmbedding.core_fraction
#print axioms RematCofinalEmbedding.core_pos
#print axioms RematCofinalEmbedding.newMesh_properties
#print axioms RematCofinalEmbedding.embedding_zero
#print axioms RematCofinalEmbedding.embedding_fraction
#print axioms RematCofinalEmbedding.embedding_scale_bounds
#print axioms RematCofinalEmbedding.embedding_abs_bound
#print axioms RematCofinalEmbedding.embedding_pos
#print axioms RematCofinalEmbedding.embedding_injective_reps
#print axioms RematCofinalEmbedding.embedding_injOn
#print axioms RematCofinalEmbedding.embedding_continuousAt_zero
#print axioms RematCofinalEmbedding.embedding_nonneg_le
#print axioms RematCofinalEmbedding.embedding_maps_samples
#print axioms RematCofinalEmbedding.adjacent_record_image
#print axioms RematCofinalEmbedding.cofinal_arithmetic_embedding
#print axioms RematCofinalEmbedding.adjacent_relation_pullback
#print axioms RematCofinalEmbedding.continuous_potential_pullback_zero
#print axioms RematCofinalEmbedding.finite_residue_refinement
#print axioms RematCofinalEmbedding.continuous_adjacent_feasibility_iff
end

section
set_option autoImplicit true
namespace RematUniformTargets

open RematDilationSynthesis RematDilationArithmetic

def denominator (K : ℕ) : ℕ := 2 * K + 1

def topNumerator (K t : ℕ) : ℕ := K + 1 - t

def threshold (K t : ℕ) : ℚ := (topNumerator K t : ℚ) / denominator K

def dimension (K t : ℕ) : ℕ := Nat.ceil ((t : ℚ) / threshold K t)

def profileNumerator (K t i : ℕ) : ℕ :=
  if i < dimension K t - 1 then topNumerator K t
  else denominator K * t - (dimension K t - 1) * topNumerator K t

def profile (K t i : ℕ) : ℚ := (profileNumerator K t i : ℚ) / denominator K

theorem threshold_bounds {K T t : ℕ} (hK : 2 * T ≤ K) (ht : 0 < t) (htT : t ≤ T) :
    (1 : ℚ) / 4 < threshold K t ∧ threshold K t < 1 / 2 ∧
    threshold K t = (1 - (1 / (denominator K : ℚ)) * (2 * t - 1)) / 2 := by
  have htk : t ≤ K + 1 := by omega
  have hQ : (0 : ℚ) < denominator K := by simp [denominator]; positivity
  have htq : (1 : ℚ) ≤ t := by exact_mod_cast ht
  have hKq : (2 : ℚ) * T ≤ K := by exact_mod_cast hK
  have htTq : (t : ℚ) ≤ T := by exact_mod_cast htT
  have he : (topNumerator K t : ℚ) = (K : ℚ) + 1 - t := by
    simp [topNumerator, Nat.cast_sub htk]
  have hden : (denominator K : ℚ) = 2 * K + 1 := by simp [denominator]
  unfold threshold
  rw [he]
  refine ⟨?_, ?_, ?_⟩
  · apply (lt_div_iff₀ hQ).mpr
    rw [hden]
    nlinarith
  · apply (div_lt_iff₀ hQ).mpr
    rw [hden]
    nlinarith
  · rw [hden]
    field_simp
    ring

theorem dimension_bounds {K T t : ℕ} (hK : 2 * T ≤ K) (ht : 0 < t) (htT : t ≤ T) :
    2 ≤ dimension K t ∧ t < dimension K t ∧ dimension K t ≤ 4 * T := by
  have hb := threshold_bounds hK ht htT
  have hq : 0 < threshold K t := lt_trans (by norm_num) hb.1
  obtain ⟨hN, hl, hu⟩ := ceil_profile_bounds t ht (threshold K t) hq (by linarith [hb.2.1])
  have hNq : (0 : ℚ) < dimension K t := by exact_mod_cast (show 0 < dimension K t by exact lt_of_lt_of_le (by omega) hN)
  refine ⟨hN, ?_, ?_⟩
  · have he : (t : ℚ) < dimension K t := by
      calc
        _ ≤ (dimension K t : ℚ) * threshold K t := hu
        _ < (dimension K t : ℚ) * 1 := mul_lt_mul_of_pos_left (by linarith [hb.2.1]) hNq
        _ = dimension K t := mul_one _
    exact_mod_cast he
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hq).mpr
    have hT : (0 : ℚ) < T := by exact_mod_cast (lt_of_lt_of_le ht htT)
    have htq : (t : ℚ) ≤ T := by exact_mod_cast htT
    push_cast
    nlinarith [hb.1]

theorem profile_formula {K T t : ℕ} (hK : 2 * T ≤ K) (ht : 0 < t) (htT : t ≤ T) (i : ℕ) :
    profile K t i = if i < dimension K t - 1 then threshold K t
      else (t : ℚ) - (dimension K t - 1 : ℕ) * threshold K t := by
  have hb := threshold_bounds hK ht htT
  have hq : 0 < threshold K t := lt_trans (by norm_num) hb.1
  have hQ : (0 : ℚ) < denominator K := by simp [denominator]; positivity
  obtain ⟨hN, hl, hu⟩ := ceil_profile_bounds t ht (threshold K t) hq (by linarith [hb.2.1])
  change ((dimension K t - 1 : ℕ) : ℚ) * threshold K t < t at hl
  have hprod : (dimension K t - 1) * topNumerator K t ≤ denominator K * t := by
    have hh : ((dimension K t - 1 : ℕ) : ℚ) * topNumerator K t < (t : ℚ) * denominator K := by
      apply (div_lt_iff₀ hQ).mp
      simpa [threshold, div_eq_mul_inv, mul_assoc] using hl
    have hh' : (dimension K t - 1) * topNumerator K t < t * denominator K := by exact_mod_cast hh
    simpa only [mul_comm (denominator K)] using hh'.le
  unfold profile profileNumerator
  split_ifs
  · rfl
  · rw [Nat.cast_sub hprod]
    push_cast
    unfold threshold
    field_simp

theorem profile_properties {K T t : ℕ} (hK : 2 * T ≤ K) (ht : 0 < t) (htT : t ≤ T) :
    profile K t 0 = threshold K t ∧
    (∑ i ∈ Finset.range (dimension K t), profile K t i = t) ∧
    (∀ i, i < dimension K t → 0 < profile K t i ∧ profile K t i ≤ threshold K t) ∧
    (∑ i ∈ Finset.range (dimension K t), profileNumerator K t i = denominator K * t) ∧
    ∀ i, i < dimension K t → 0 < profileNumerator K t i ∧ profileNumerator K t i < denominator K := by
  have hb := threshold_bounds hK ht htT
  have hq : 0 < threshold K t := lt_trans (by norm_num) hb.1
  have hh := ceil_threshold_profile t ht (threshold K t) hq (by linarith [hb.2.1])
  change 2 ≤ dimension K t ∧ _ at hh
  have he (i : ℕ) := profile_formula hK ht htT i
  have hzero : profile K t 0 = threshold K t := by rw [he]; exact hh.2.1
  have hsum : ∑ i ∈ Finset.range (dimension K t), profile K t i = t := by
    simp_rw [he]
    exact hh.2.2.1
  have hbounds (i : ℕ) (hi : i < dimension K t) :
      0 < profile K t i ∧ profile K t i ≤ threshold K t := by rw [he]; exact hh.2.2.2 i hi
  have hQ : (0 : ℚ) < denominator K := by simp [denominator]; positivity
  refine ⟨hzero, hsum, hbounds, ?_, ?_⟩
  · have hs : (∑ i ∈ Finset.range (dimension K t), (profileNumerator K t i : ℚ)) /
        denominator K = t := by simpa only [profile, div_eq_mul_inv, ← Finset.sum_mul] using hsum
    have hs' := (div_eq_iff hQ.ne').mp hs
    have hs'' : (∑ i ∈ Finset.range (dimension K t), profileNumerator K t i) = t * denominator K := by
      exact_mod_cast hs'
    simpa only [mul_comm] using hs''
  · intro i hi
    have h := hbounds i hi
    have hp : (0 : ℚ) < profileNumerator K t i := (div_pos_iff.mp h.1).elim And.left (fun h => (not_lt_of_ge hQ.le h.2).elim)
    have hl : (profileNumerator K t i : ℚ) < denominator K := by
      apply (div_lt_one hQ).mp
      exact h.2.trans_lt (by linarith [hb.2.1])
    exact ⟨by exact_mod_cast hp, by exact_mod_cast hl⟩

theorem lattice_guard {D Q r : ℕ} (hr : r.Coprime Q) : Nat.gcd (D * Q) r ∣ D := by
  rw [hr.symm.gcd_mul_right_cancel D]
  exact Nat.gcd_dvd_left D r

theorem scaled_profile_lattice {D K T t r : ℕ} (hD : 0 < D) (hK : 2 * T ≤ K)
    (ht : 0 < t) (htT : t ≤ T) (hr : r.Coprime (denominator K)) :
    (∀ i ∈ Finset.range (dimension K t),
      0 < D * profileNumerator K t i ∧ D * profileNumerator K t i < D * denominator K ∧
        Nat.gcd (D * denominator K) r ∣ D * profileNumerator K t i) ∧
    (∑ i ∈ Finset.range (dimension K t), D * profileNumerator K t i = (D * denominator K) * t) := by
  have hp := profile_properties hK ht htT
  constructor
  · intro i hi
    have h := hp.2.2.2.2 i (Finset.mem_range.mp hi)
    exact ⟨Nat.mul_pos hD h.1, Nat.mul_lt_mul_of_pos_left h.2 hD,
      dvd_mul_of_dvd_left (lattice_guard hr) _⟩
  · rw [← Finset.mul_sum, hp.2.2.2.1]
    ring

theorem scaled_fraction {D Q v : ℕ} (hD : 0 < D) :
    ((D * v : ℕ) : ℚ) / (D * Q : ℕ) = (v : ℚ) / Q := by
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast
  field_simp

theorem residue_fractional_part {D H r m c : ℕ} (hD : 0 < D) (hH : 0 < H)
    (hm : m ≡ r [MOD D]) :
    Int.fract (((H * m : ℕ) : ℚ) * ((c : ℚ) / (H * D : ℕ))) =
    Int.fract (((H * r : ℕ) : ℚ) * ((c : ℚ) / (H * D : ℕ))) := by
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hh : (H : ℚ) ≠ 0 := by exact_mod_cast hH.ne'
  have he (n : ℕ) : (((H * n : ℕ) : ℚ) * ((c : ℚ) / (H * D : ℕ))) = ((n * c : ℕ) : ℚ) / D := by
    push_cast
    field_simp
  rw [he m, he r, Int.fract_div_natCast_eq_div_natCast_mod,
    Int.fract_div_natCast_eq_div_natCast_mod, hm.mul_right c]

def TargetAt (D K H t r : ℕ) : Prop :=
  ∃ C : ℕ → ℕ,
    (∑ i ∈ Finset.range (dimension K t), C i = H * (D * denominator K)) ∧
    (∀ i, i < dimension K t → 0 < (C i : ℚ) / (H * (D * denominator K) : ℕ)) ∧
    (∑ i ∈ Finset.range (dimension K t), (C i : ℚ) / (H * (D * denominator K) : ℕ) = 1) ∧
    (∀ m : ℕ, m ≡ r [MOD D * denominator K] → ∀ i, i < dimension K t →
      Int.fract (((H * m : ℕ) : ℚ) * ((C i : ℚ) / (H * (D * denominator K) : ℕ))) = profile K t i) ∧
    (∀ m : ℕ, m ≡ r [MOD D * denominator K] →
      ∑ i ∈ Finset.range (dimension K t),
        Int.fract (((H * m : ℕ) : ℚ) * ((C i : ℚ) / (H * (D * denominator K) : ℕ))) = t)

theorem target_all_heights {D K T t r : ℕ} (hD : 0 < D) (hK : 2 * T ≤ K)
    (ht : 0 < t) (htT : t ≤ T) (hr : r.Coprime (denominator K)) :
    ∃ L : ℕ, 0 < L ∧ L ≤ dimension K t ∧ ∀ H, L ≤ H → TargetAt D K H t r := by
  have hQ : 0 < denominator K := by simp [denominator]
  have hDQ := Nat.mul_pos hD hQ
  have hN := dimension_bounds hK ht htT
  have hnon : (Finset.range (dimension K t)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hlattice := scaled_profile_lattice hD hK ht htT hr
  obtain ⟨c, _, hLpos, hLbound, hall⟩ := lattice_profile_all_heights
    (Finset.range (dimension K t)) hnon (D * denominator K) r t
    (fun i => D * profileNumerator K t i) hDQ hlattice.1 hlattice.2
  refine ⟨Nat.ceil (((∑ i ∈ Finset.range (dimension K t), c i : ℕ) : ℚ) / ((D * denominator K : ℕ) : ℚ)),
    hLpos, by simpa using hLbound, ?_⟩
  intro H hH
  obtain ⟨C, hsum, hpos, hone, hfract, hmass⟩ := hall H hH
  have hHp := hLpos.trans_le hH
  refine ⟨C, hsum, fun i hi => hpos i (Finset.mem_range.mpr hi), hone, ?_, ?_⟩
  · intro m hm i hi
    rw [residue_fractional_part hDQ hHp hm]
    have hh := hfract 0 i (Finset.mem_range.mpr hi)
    simpa only [Nat.zero_mul, Nat.add_zero, scaled_fraction hD, profile] using hh
  · intro m hm
    have he i (hi : i ∈ Finset.range (dimension K t)) :
        Int.fract (((H * m : ℕ) : ℚ) * ((C i : ℚ) / (H * (D * denominator K) : ℕ))) =
        Int.fract (((H * r : ℕ) : ℚ) * ((C i : ℚ) / (H * (D * denominator K) : ℕ))) :=
      residue_fractional_part hDQ hHp hm
    rw [Finset.sum_congr rfl he]
    simpa only [Nat.zero_mul, Nat.add_zero] using hmass 0

theorem common_target_family {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    {D K T : ℕ} (hD : 0 < D) (hT : 0 < T) (hK : 2 * T ≤ K)
    (ht : ∀ a ∈ A, 0 < t a ∧ t a ≤ T)
    (hr : ∀ a ∈ A, (r a).Coprime (denominator K)) :
    ∃ H : ℕ, 0 < H ∧ H ≤ 4 * T ∧
      ∀ a ∈ A, 2 ≤ dimension K (t a) ∧ dimension K (t a) ≤ 4 * T ∧ TargetAt D K H (t a) (r a) := by
  classical
  have hex a : ∃ L : ℕ, a ∈ A → 0 < L ∧ L ≤ dimension K (t a) ∧
      ∀ H, L ≤ H → TargetAt D K H (t a) (r a) := by
    by_cases ha : a ∈ A
    · obtain ⟨L, hL⟩ := target_all_heights hD hK (ht a ha).1 (ht a ha).2 (hr a ha)
      exact ⟨L, fun _ => hL⟩
    · exact ⟨1, fun hh => (ha hh).elim⟩
  choose L hL using hex
  let H := max 1 (A.sup L)
  have hpos : 0 < H := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hbound : H ≤ 4 * T := by
    apply max_le
    · omega
    · exact Finset.sup_le (fun a ha => (hL a ha).2.1.trans (dimension_bounds hK (ht a ha).1 (ht a ha).2).2.2)
  refine ⟨H, hpos, hbound, ?_⟩
  intro a ha
  have hb := dimension_bounds hK (ht a ha).1 (ht a ha).2
  exact ⟨hb.1, hb.2.2, (hL a ha).2.2 H ((Finset.le_sup ha).trans (le_max_right _ _))⟩

theorem profile_scalar_gap {K T t : ℕ} (hK : 2 * T ≤ K) (ht : 0 < t) (htT : t ≤ T)
    (B : ℝ) :
    let ell : ℝ := 1 / denominator K
    let f : ℕ → ℝ := fun i => (profile K t i : ℝ)
    (B + scalarCost ell t f 1 = B + scalarCost ell t f 0) ∧
      (∀ m : ℕ, m ≤ t → ((∀ n : ℕ, n ≤ t →
        B + scalarCost ell t f m ≤ B + scalarCost ell t f n) ↔ m = 0 ∨ m = 1)) ∧
      ∀ m : ℕ, 2 ≤ m → m ≤ t →
        B + scalarCost ell t f 0 + 2 * ell ≤ B + scalarCost ell t f m := by
  dsimp
  have hQ : (0 : ℝ) < denominator K := by simp [denominator]; positivity
  have hp := profile_properties hK ht htT
  have hb := threshold_bounds hK ht htT
  have hform : ((threshold K t : ℚ) : ℝ) =
      (1 - (1 / (denominator K : ℝ)) * (2 * t - 1)) / 2 := by
    have hh := congrArg (fun x : ℚ => (x : ℝ)) hb.2.2
    push_cast at hh
    exact hh
  apply full_cost_minimizers_gap B (1 / denominator K) (one_div_pos.mpr hQ) t ht
  · intro m hm
    rw [← hform]
    exact_mod_cast (hp.2.2.1 m (hm.trans (dimension_bounds hK ht htT).2.1)).2
  · rw [hp.1, hform]

def auxiliaryHalf (D T : ℕ) : ℕ := 2 * D * T.factorial

theorem auxiliary_properties {D T : ℕ} (hD : 0 < D) :
    2 * T ≤ auxiliaryHalf D T ∧
    4 * T < denominator (auxiliaryHalf D T) ∧
    (D * T.factorial).Coprime (denominator (auxiliaryHalf D T)) ∧
    denominator (auxiliaryHalf D T) = 4 * D * T.factorial + 1 := by
  have hself := Nat.self_le_factorial T
  have hfac := Nat.factorial_pos T
  have hD1 : 1 ≤ D := hD
  have hK : 2 * T ≤ auxiliaryHalf D T := by unfold auxiliaryHalf; nlinarith
  have he : denominator (auxiliaryHalf D T) = 4 * D * T.factorial + 1 := by
    unfold denominator auxiliaryHalf
    ring
  refine ⟨hK, ?_, ?_, he⟩
  · unfold denominator
    omega
  · rw [he]
    have hm : 4 * D * T.factorial + 1 ≡ 1 [MOD D * T.factorial] := by
      change (4 * D * T.factorial + 1) % (D * T.factorial) = 1 % (D * T.factorial)
      rw [mul_assoc 4 D T.factorial, Nat.add_mod]
      simp
    exact (RematCofinalEmbedding.modEq_coprime hm (Nat.coprime_one_left _)).symm

noncomputable def refined {ι : Type*} [DecidableEq ι] (A : Finset ι) (r : ι → ℕ) (D Q : ℕ) : Finset (ι × ℕ) :=
  (A ×ˢ Finset.range (D * Q)).filter (fun e => e.2 ≡ r e.1 [MOD D] ∧ e.2.Coprime Q)

theorem mem_refined {ι : Type*} [DecidableEq ι] (A : Finset ι) (r : ι → ℕ) (D Q : ℕ)
    (a : ι) (s : ℕ) :
    (a, s) ∈ refined A r D Q ↔ a ∈ A ∧ s < D * Q ∧ s ≡ r a [MOD D] ∧ s.Coprime Q := by
  simp only [refined, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  tauto

theorem refined_empty {ι : Type*} [DecidableEq ι] (r : ι → ℕ) (D Q : ℕ) :
    refined (∅ : Finset ι) r D Q = ∅ := by simp [refined]

theorem refined_record_exists {ι : Type*} [DecidableEq ι] (A : Finset ι) (r : ι → ℕ)
    {D Q : ℕ} (hD : 0 < D) (hQ : 0 < Q) (hcop : D.Coprime Q)
    (a : ι) (ha : a ∈ A) : ∃ s : ℕ, (a, s) ∈ refined A r D Q := by
  let b := Nat.chineseRemainder hcop (r a) 1
  refine ⟨b.val, (mem_refined A r D Q a b.val).mpr ⟨ha,
    Nat.chineseRemainder_lt_mul hcop (r a) 1 hD.ne' hQ.ne', b.property.1, ?_⟩⟩
  exact RematCofinalEmbedding.modEq_coprime b.property.2 (Nat.coprime_one_left Q)

theorem refined_family {ι : Type*} [DecidableEq ι] (A : Finset ι) (t r : ι → ℕ)
    {D T : ℕ} (hD : 0 < D) (hT : 0 < T)
    (ht : ∀ a ∈ A, 0 < t a ∧ t a ≤ T) :
    ∃ H : ℕ, 0 < H ∧ H ≤ 4 * T ∧
      ∀ e ∈ refined A r D (denominator (auxiliaryHalf D T)),
        2 ≤ dimension (auxiliaryHalf D T) (t e.1) ∧
        dimension (auxiliaryHalf D T) (t e.1) ≤ 4 * T ∧
        TargetAt D (auxiliaryHalf D T) H (t e.1) e.2 := by
  have hp := auxiliary_properties (T := T) hD
  apply common_target_family (refined A r D (denominator (auxiliaryHalf D T)))
    (fun e => t e.1) (fun e => e.2) hD hT hp.1
  · intro e he
    exact ht e.1 ((mem_refined A r D _ e.1 e.2).mp he).1
  · intro e he
    exact ((mem_refined A r D _ e.1 e.2).mp he).2.2.2

def Comparison (forward strict : Bool) (x y : ℝ) : Prop :=
  if forward then (if strict then x < y else x ≤ y)
  else (if strict then y < x else y ≤ x)

def Realizes {ι : Type*} (A : Finset ι) (t r : ι → ℕ) (forward strict : ι → Bool)
    (D : ℕ) (u : ℝ → ℝ) : Prop :=
  ∀ a ∈ A, ∀ m : ℕ, t a ≤ m → m ≡ r a [MOD D] →
    Comparison (forward a) (strict a) (u ((t a : ℝ) / m)) (u (((t a - 1 : ℕ) : ℝ) / m))

def RealizesScaled {ι : Type*} (A : Finset ι) (t r : ι → ℕ) (forward strict : ι → Bool)
    (D H : ℕ) (u : ℝ → ℝ) : Prop :=
  ∀ a ∈ A, ∀ m : ℕ, t a ≤ m → m ≡ r a [MOD D] →
    Comparison (forward a) (strict a) (u ((t a : ℝ) / (H * m : ℕ)))
      (u (((t a - 1 : ℕ) : ℝ) / (H * m : ℕ)))

theorem refinement_feasibility_iff {ι : Type*} [DecidableEq ι] (A : Finset ι)
    (t r : ι → ℕ) (forward strict : ι → Bool) {D T Q : ℕ}
    (hD : 0 < D) (hQ : 0 < Q) (hcop : (D * T.factorial).Coprime Q)
    (ht : ∀ a ∈ A, 0 < t a ∧ t a ≤ T) :
    (∃ u : ℝ → ℝ, ContinuousAt u 0 ∧ u 0 = 0 ∧ Realizes A t r forward strict D u) ↔
    (∃ u : ℝ → ℝ, ContinuousAt u 0 ∧ u 0 = 0 ∧
      Realizes (refined A r D Q) (fun e => t e.1) (fun e => e.2)
        (fun e => forward e.1) (fun e => strict e.1) (D * Q) u) := by
  constructor
  · rintro ⟨u, hu, hz, hR⟩
    refine ⟨u, hu, hz, ?_⟩
    intro e he m htm hmr
    have hmem := (mem_refined A r D Q e.1 e.2).mp he
    exact hR e.1 hmem.1 m htm ((hmr.of_dvd (Nat.dvd_mul_right D Q)).trans hmem.2.2.1)
  · rintro ⟨u, hu, hz, hR⟩
    refine ⟨u ∘ RematCofinalEmbedding.embedding D T Q hcop,
      RematCofinalEmbedding.continuous_potential_pullback_zero hD hQ hcop hu,
      by simpa only [Function.comp_apply, RematCofinalEmbedding.embedding_zero] using hz, ?_⟩
    intro a ha m htm hmr
    obtain ⟨m', _, htM', hmQ, hmr', he1, he2⟩ :=
      RematCofinalEmbedding.adjacent_record_image hD hQ hcop (ht a ha).1 (ht a ha).2 htm hmr
    obtain ⟨r', hrbound, hrr, hrQ, hMr⟩ :=
      (RematCofinalEmbedding.finite_residue_refinement hD hQ).mp ⟨hmr', hmQ⟩
    have hmem : (a, r') ∈ refined A r D Q := (mem_refined A r D Q a r').mpr ⟨ha, hrbound, hrr, hrQ⟩
    have hh := hR (a, r') hmem m' htM' hMr
    simpa only [Function.comp_apply, he1, he2] using hh

theorem dilation_feasibility_iff {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) (D H : ℕ) (hH : 0 < H) :
    (∃ u : ℝ → ℝ, ContinuousAt u 0 ∧ u 0 = 0 ∧ Realizes A t r forward strict D u) ↔
    (∃ u : ℝ → ℝ, ContinuousAt u 0 ∧ u 0 = 0 ∧ RealizesScaled A t r forward strict D H u) := by
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  constructor
  · rintro ⟨u, hu, hz, hR⟩
    have hc : ContinuousAt (fun x : ℝ => u ((H : ℝ) * x)) 0 := by
      have hh : ContinuousAt u ((H : ℝ) * 0) := by simpa using hu
      exact hh.comp (continuousAt_const.mul continuousAt_id)
    refine ⟨fun x => u ((H : ℝ) * x), hc, by simpa using hz, ?_⟩
    have he (n m : ℕ) : (H : ℝ) * ((n : ℝ) / (H * m : ℕ)) = (n : ℝ) / m := by
      push_cast
      field_simp
    intro a ha m htm hmr
    simpa only [he] using hR a ha m htm hmr
  · rintro ⟨u, hu, hz, hR⟩
    have hc : ContinuousAt (fun x : ℝ => u (x / H)) 0 := by
      have hh : ContinuousAt u ((0 : ℝ) / H) := by simpa using hu
      exact ContinuousAt.comp (f := fun x : ℝ => x / (H : ℝ)) hh
        (continuousAt_id.div_const (H : ℝ))
    refine ⟨fun x => u (x / H), hc, by simpa using hz, ?_⟩
    have he (n m : ℕ) : ((n : ℝ) / m) / H = (n : ℝ) / (H * m : ℕ) := by
      push_cast
      rw [div_div, mul_comm (m : ℝ)]
    intro a ha m htm hmr
    simpa only [he] using hR a ha m htm hmr

theorem uniform_arithmetic_representation {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (t r : ι → ℕ) {D T : ℕ} (hD : 0 < D) (hT : 0 < T)
    (ht : ∀ a ∈ A, 0 < t a ∧ t a ≤ T) :
    ∃ H : ℕ, 0 < H ∧ H ≤ 4 * T ∧
      (∀ e ∈ refined A r D (denominator (auxiliaryHalf D T)),
        2 ≤ dimension (auxiliaryHalf D T) (t e.1) ∧
        dimension (auxiliaryHalf D T) (t e.1) ≤ 4 * T ∧
        TargetAt D (auxiliaryHalf D T) H (t e.1) e.2) ∧
      ∀ forward strict : ι → Bool,
        (∃ u : ℝ → ℝ, ContinuousAt u 0 ∧ u 0 = 0 ∧ Realizes A t r forward strict D u) ↔
        (∃ u : ℝ → ℝ, ContinuousAt u 0 ∧ u 0 = 0 ∧
          RealizesScaled (refined A r D (denominator (auxiliaryHalf D T)))
            (fun e => t e.1) (fun e => e.2) (fun e => forward e.1) (fun e => strict e.1)
            (D * denominator (auxiliaryHalf D T)) H u) := by
  obtain ⟨H, hH, hHb, htargets⟩ := refined_family A t r hD hT ht
  refine ⟨H, hH, hHb, htargets, ?_⟩
  intro forward strict
  have hQ : 0 < denominator (auxiliaryHalf D T) := by simp [denominator]
  exact (refinement_feasibility_iff A t r forward strict hD hQ
    (auxiliary_properties hD).2.2.1 ht).trans
    (dilation_feasibility_iff _ _ _ _ _ _ H hH)

theorem target_fin_coordinates {D K H t r : ℕ} (h : TargetAt D K H t r) :
    ∃ a : Fin (dimension K t) → ℚ,
      (∀ i, 0 < a i) ∧ (∑ i, a i = 1) ∧
      (∀ m : ℕ, m ≡ r [MOD D * denominator K] → ∀ i,
        Int.fract (((H * m : ℕ) : ℚ) * a i) = profile K t i.val) ∧
      (∀ m : ℕ, m ≡ r [MOD D * denominator K] →
        ∑ i, Int.fract (((H * m : ℕ) : ℚ) * a i) = t) ∧
      ∃ C : Fin (dimension K t) → ℕ,
        ∀ i, a i = (C i : ℚ) / (H * (D * denominator K) : ℕ) := by
  obtain ⟨C, _, hpos, hsum, hfract, hmass⟩ := h
  let a : Fin (dimension K t) → ℚ := fun i => (C i.val : ℚ) / (H * (D * denominator K) : ℕ)
  refine ⟨a, fun i => hpos i.val i.isLt, ?_, ?_, ?_, fun i => C i.val, fun _ => rfl⟩
  · change (∑ i : Fin (dimension K t), (C i.val : ℚ) / (H * (D * denominator K) : ℕ)) = 1
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (C i : ℚ) / (H * (D * denominator K) : ℕ))]
    exact hsum
  · intro m hm i
    exact hfract m hm i.val i.isLt
  · intro m hm
    change (∑ i : Fin (dimension K t), Int.fract (((H * m : ℕ) : ℚ) * ((C i.val : ℚ) / (H * (D * denominator K) : ℕ)))) = t
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => Int.fract (((H * m : ℕ) : ℚ) * ((C i : ℚ) / (H * (D * denominator K) : ℕ))))]
    exact hmass m hm

theorem rat_fract_cast (x : ℚ) : Int.fract (x : ℝ) = ((Int.fract x : ℚ) : ℝ) := by
  exact Int.map_fract (Rat.castHom ℝ) Rat.cast_strictMono x

theorem target_real_coordinates {D K H t r : ℕ} (h : TargetAt D K H t r) :
    ∃ a : Fin (dimension K t) → ℚ,
      (∀ i, 0 < (a i : ℝ)) ∧ (∑ i, (a i : ℝ) = 1) ∧
      (∀ m : ℕ, m ≡ r [MOD D * denominator K] → ∀ i,
        Int.fract (((H * m : ℕ) : ℝ) * (a i : ℝ)) = ((profile K t i.val : ℚ) : ℝ)) ∧
      (∀ m : ℕ, m ≡ r [MOD D * denominator K] →
        ∑ i, Int.fract (((H * m : ℕ) : ℝ) * (a i : ℝ)) = t) := by
  obtain ⟨a, hpos, hsum, hfract, hmass, _⟩ := target_fin_coordinates h
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · intro i
    exact_mod_cast hpos i
  · exact_mod_cast hsum
  · intro m hm i
    have he : (((H * m : ℕ) : ℝ) * (a i : ℝ)) = ((((H * m : ℕ) : ℚ) * a i : ℚ) : ℝ) := by push_cast; rfl
    rw [he, rat_fract_cast, hfract m hm i]
  · intro m hm
    have he (i : Fin (dimension K t)) :
        Int.fract (((H * m : ℕ) : ℝ) * (a i : ℝ)) =
        ((Int.fract (((H * m : ℕ) : ℚ) * a i) : ℚ) : ℝ) := by
      have hh : (((H * m : ℕ) : ℝ) * (a i : ℝ)) = ((((H * m : ℕ) : ℚ) * a i : ℚ) : ℝ) := by push_cast; rfl
      rw [hh, rat_fract_cast]
    simp_rw [he]
    exact_mod_cast hmass m hm

theorem denominator_odd (K : ℕ) : Odd (denominator K) := by
  exact ⟨K, by unfold denominator; omega⟩

end RematUniformTargets

#print axioms RematUniformTargets.threshold_bounds
#print axioms RematUniformTargets.dimension_bounds
#print axioms RematUniformTargets.profile_formula
#print axioms RematUniformTargets.profile_properties
#print axioms RematUniformTargets.lattice_guard
#print axioms RematUniformTargets.scaled_profile_lattice
#print axioms RematUniformTargets.scaled_fraction
#print axioms RematUniformTargets.residue_fractional_part
#print axioms RematUniformTargets.target_all_heights
#print axioms RematUniformTargets.common_target_family
#print axioms RematUniformTargets.profile_scalar_gap
#print axioms RematUniformTargets.auxiliary_properties
#print axioms RematUniformTargets.mem_refined
#print axioms RematUniformTargets.refined_empty
#print axioms RematUniformTargets.refined_record_exists
#print axioms RematUniformTargets.refined_family
#print axioms RematUniformTargets.refinement_feasibility_iff
#print axioms RematUniformTargets.dilation_feasibility_iff
#print axioms RematUniformTargets.uniform_arithmetic_representation
#print axioms RematUniformTargets.target_fin_coordinates
#print axioms RematUniformTargets.rat_fract_cast
#print axioms RematUniformTargets.target_real_coordinates
#print axioms RematUniformTargets.denominator_odd
end

section
set_option autoImplicit true
set_option autoImplicit false

open scoped BigOperators

namespace RematElegance

open RematUniformTargets RematDilationSynthesis

theorem prefix_scalar_identity (ell : ℝ) (t j : ℕ) (f : ℕ → ℝ)
    (hf : ∀ i < j, f i = (1 - ell * (2 * t - 1)) / 2) :
    scalarCost ell t f j - scalarCost ell t f 0 = ell * j * ((j : ℝ) - 1) := by
  have hs : (∑ i ∈ Finset.range j, (1 - 2 * f i)) = (j : ℝ) * (ell * (2 * t - 1)) := by
    calc
      _ = ∑ _i ∈ Finset.range j, ell * (2 * t - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hf i (Finset.mem_range.mp hi)]
        ring
      _ = (j : ℝ) * (ell * (2 * t - 1)) := by simp
  simp only [scalarCost, hs, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, sub_zero, zero_add]
  ring

theorem dimension_gt_twice_capacity {K T t : ℕ} (hK : 2 * T ≤ K) (ht : 0 < t) (htT : t ≤ T) :
    2 * t < dimension K t := by
  have hb := threshold_bounds hK ht htT
  have hq : 0 < threshold K t := lt_trans (by norm_num) hb.1
  change 2 * t < Nat.ceil ((t : ℚ) / threshold K t)
  apply Nat.lt_ceil.mpr
  apply (lt_div_iff₀ hq).mpr
  push_cast
  have htq : (0 : ℚ) < t := by exact_mod_cast ht
  nlinarith [mul_pos htq (sub_pos.mpr hb.2.1)]

theorem constructed_profile_prefix {K T t : ℕ} (hK : 2 * T ≤ K) (ht : 0 < t) (htT : t ≤ T) :
    t ≤ dimension K t - 1 ∧ ∀ i < t, profile K t i = threshold K t := by
  have hn := (dimension_bounds hK ht htT).2.1
  refine ⟨by omega, ?_⟩
  intro i hi
  have hiN : i < dimension K t - 1 := by omega
  simp only [profile, profileNumerator, if_pos hiN, threshold]

theorem constructed_scalar_identity {K T t : ℕ} (hK : 2 * T ≤ K) (ht : 0 < t) (htT : t ≤ T)
    (j : ℕ) (hj : j ≤ t) :
    scalarCost (1 / (denominator K : ℝ)) t (fun i => (profile K t i : ℝ)) j -
      scalarCost (1 / (denominator K : ℝ)) t (fun i => (profile K t i : ℝ)) 0 =
      (1 / (denominator K : ℝ)) * j * ((j : ℝ) - 1) := by
  apply prefix_scalar_identity
  intro i hi
  rw [(constructed_profile_prefix hK ht htT).2 i (hi.trans_le hj)]
  have hh := congrArg (fun q : ℚ => (q : ℝ)) (threshold_bounds hK ht htT).2.2
  push_cast at hh
  exact hh

theorem constructed_full_cost_identity {K T t : ℕ} (hK : 2 * T ≤ K) (ht : 0 < t) (htT : t ≤ T)
    (B : ℝ) (j : ℕ) (hj : j ≤ t) :
    (B + scalarCost (1 / (denominator K : ℝ)) t (fun i => (profile K t i : ℝ)) j) -
      (B + scalarCost (1 / (denominator K : ℝ)) t (fun i => (profile K t i : ℝ)) 0) =
      (1 / (denominator K : ℝ)) * j * ((j : ℝ) - 1) := by
  simpa only [add_sub_add_left_eq_sub] using constructed_scalar_identity hK ht htT j hj

theorem constructed_excluded_gap {K T t : ℕ} (hK : 2 * T ≤ K) (ht : 0 < t) (htT : t ≤ T)
    (j : ℕ) (hj : j ≤ t) (hj2 : 2 ≤ j) :
    2 / (denominator K : ℝ) ≤
      scalarCost (1 / (denominator K : ℝ)) t (fun i => (profile K t i : ℝ)) j -
        scalarCost (1 / (denominator K : ℝ)) t (fun i => (profile K t i : ℝ)) 0 := by
  rw [constructed_scalar_identity hK ht htT j hj]
  have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj2
  have hp : 2 ≤ (j : ℝ) * ((j : ℝ) - 1) := by nlinarith
  have he : 0 ≤ 1 / (denominator K : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hp he
  calc
    2 / (denominator K : ℝ) = (1 / (denominator K : ℝ)) * 2 := by ring
    _ ≤ (1 / (denominator K : ℝ)) * ((j : ℝ) * ((j : ℝ) - 1)) := hh
    _ = (1 / (denominator K : ℝ)) * j * ((j : ℝ) - 1) := by ring


theorem constructed_minimizers_iff {K T t : ℕ} (hK : 2 * T ≤ K) (ht : 0 < t) (htT : t ≤ T)
    (j : ℕ) (hj : j ≤ t) :
    (∀ m : ℕ, m ≤ t →
      scalarCost (1 / (denominator K : ℝ)) t (fun i => (profile K t i : ℝ)) j ≤
      scalarCost (1 / (denominator K : ℝ)) t (fun i => (profile K t i : ℝ)) m) ↔
      j = 0 ∨ j = 1 := by
  let C := scalarCost (1 / (denominator K : ℝ)) t (fun i => (profile K t i : ℝ))
  change (∀ m : ℕ, m ≤ t → C j ≤ C m) ↔ _
  have hnonneg (m : ℕ) (hm : m ≤ t) : 0 ≤ C m - C 0 := by
    rw [constructed_scalar_identity hK ht htT m hm]
    by_cases hz : m = 0
    · simp [hz]
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      exact mul_nonneg (by positivity) (by linarith)
  have htie : C 1 = C 0 := by
    have hh := constructed_scalar_identity hK ht htT 1 (by omega)
    simpa only [Nat.cast_one, sub_self, mul_zero, sub_eq_zero] using hh
  constructor
  · intro hh
    by_contra hn
    have hj2 : 2 ≤ j := by omega
    have hg := constructed_excluded_gap hK ht htT j hj hj2
    have hp : (0 : ℝ) < 2 / (denominator K : ℝ) := by apply div_pos (by norm_num); simp [denominator]; positivity
    have h0 := hh 0 (Nat.zero_le _)
    change _ ≤ C j - C 0 at hg
    linarith
  · rintro (rfl | rfl) m hm
    · linarith [hnonneg m hm]
    · rw [htie]
      linarith [hnonneg m hm]

end RematElegance

#print axioms RematElegance.prefix_scalar_identity
#print axioms RematElegance.dimension_gt_twice_capacity
#print axioms RematElegance.constructed_profile_prefix
#print axioms RematElegance.constructed_scalar_identity
#print axioms RematElegance.constructed_full_cost_identity
#print axioms RematElegance.constructed_excluded_gap
#print axioms RematElegance.constructed_minimizers_iff
end

section
set_option autoImplicit true
open scoped BigOperators

namespace RematAnchoredCuts

variable {V : Type*} [Preorder V]

noncomputable def lowerCut (x v : V) : ℝ := by
  classical
  exact if v ≤ x then -1 else 0

noncomputable def upperCut (y v : V) : ℝ := by
  classical
  exact if y ≤ v then 1 else 0

theorem lowerCut_monotone (x : V) : Monotone (lowerCut x) := by
  classical
  intro a b hab
  by_cases ha : a ≤ x <;> by_cases hb : b ≤ x
  · simp [lowerCut, ha, hb]
  · simp [lowerCut, ha, hb]
  · exact (ha (hab.trans hb)).elim
  · simp [lowerCut, ha, hb]

theorem upperCut_monotone (y : V) : Monotone (upperCut y) := by
  classical
  intro a b hab
  by_cases ha : y ≤ a <;> by_cases hb : y ≤ b
  · simp [upperCut, ha, hb]
  · exact (hb (ha.trans hab)).elim
  · simp [upperCut, ha, hb]
  · simp [upperCut, ha, hb]

theorem lowerCut_support (x : V) : Function.support (lowerCut x) = Set.Iic x := by
  classical
  ext v
  simp only [Function.mem_support, Set.mem_Iic, lowerCut]
  split_ifs <;> simp_all

theorem upperCut_support (y : V) : Function.support (upperCut y) = Set.Ici y := by
  classical
  ext v
  simp only [Function.mem_support, Set.mem_Ici, upperCut]
  split_ifs <;> simp_all

theorem lowerCut_abs (x v : V) : |lowerCut x v| ≤ 1 := by
  classical
  unfold lowerCut
  split_ifs <;> norm_num

theorem upperCut_abs (y v : V) : |upperCut y v| ≤ 1 := by
  classical
  unfold upperCut
  split_ifs <;> norm_num

theorem finite_anchored_cut_exists (o x y : V) (hrev : ¬y ≤ x)
    (hfin : ((Set.Iic x).Finite ∧ ¬o ≤ x) ∨ ((Set.Ici y).Finite ∧ ¬y ≤ o)) :
    ∃ f : V → ℝ, Monotone f ∧ (Function.support f).Finite ∧
      (∀ v, |f v| ≤ 1) ∧ f o = 0 ∧ f x < f y := by
  classical
  rcases hfin with ⟨hx, ho⟩ | ⟨hy, ho⟩
  · exact ⟨lowerCut x, lowerCut_monotone x, by simpa [lowerCut_support] using hx,
      lowerCut_abs x, by simp [lowerCut, ho], by simp [lowerCut, hrev]⟩
  · exact ⟨upperCut y, upperCut_monotone y, by simpa [upperCut_support] using hy,
      upperCut_abs y, by simp [upperCut, ho], by simp [upperCut, hrev]⟩

theorem finite_positive_lower_bound_on (s : Finset V) (η : V → ℝ)
    (hη : ∀ v ∈ s, 0 < η v) : ∃ c : ℝ, 0 < c ∧ ∀ v ∈ s, c ≤ η v := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    rcases ih (fun v hv => hη v (Finset.mem_insert_of_mem hv)) with ⟨c, hc, hcs⟩
    refine ⟨min (η a) c, lt_min (hη a (Finset.mem_insert_self _ _)) hc, ?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hcs v hv)

theorem positive_anchored_coefficients (o : V) (f : ℕ → V → ℝ) (η : V → ℝ)
    (hfin : ∀ n, (Function.support (f n)).Finite) (hzero : ∀ n, f n o = 0)
    (hη : ∀ v, v ≠ o → 0 < η v) :
    ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧
      ∀ n v, f n v ≠ 0 → c n ≤ η v / 2 / 2 ^ n := by
  classical
  have h n : ∃ c : ℝ, 0 < c ∧
      ∀ v ∈ (hfin n).toFinset, c ≤ η v / 2 / 2 ^ n := by
    apply finite_positive_lower_bound_on
    intro v hv
    have hv' : f n v ≠ 0 := by
      simpa only [Set.Finite.mem_toFinset, Function.mem_support] using hv
    have hvo : v ≠ o := by rintro rfl; exact hv' (hzero n)
    have := hη v hvo
    positivity
  choose c hc hb using h
  refine ⟨c, hc, ?_⟩
  intro n v hv
  exact hb n v (by simpa only [Set.Finite.mem_toFinset, Function.mem_support] using hv)

theorem anchored_series_envelope (o : V) (f : ℕ → V → ℝ) (η : V → ℝ) (c : ℕ → ℝ)
    (hm : ∀ n, Monotone (f n)) (hb : ∀ n v, |f n v| ≤ 1)
    (hz : ∀ n, f n o = 0) (hη : ∀ v, 0 ≤ η v) (hc : ∀ n, 0 < c n)
    (hcb : ∀ n v, f n v ≠ 0 → c n ≤ η v / 2 / 2 ^ n) :
    (∀ v, Summable (fun n => c n * f n v)) ∧
      (∀ v, |∑' n, c n * f n v| ≤ η v) ∧
      (∑' n, c n * f n o) = 0 ∧
      Monotone (fun v => ∑' n, c n * f n v) ∧
      ∀ x y, x ≤ y → (∃ n, f n x < f n y) →
        (∑' n, c n * f n x) < ∑' n, c n * f n y := by
  have hdom n v : ‖c n * f n v‖ ≤ η v / 2 / 2 ^ n := by
    by_cases hzero : f n v = 0
    · simp only [hzero, mul_zero, norm_zero]
      have := hη v
      positivity
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hc n)]
      exact (mul_le_of_le_one_right (hc n).le (hb n v)).trans (hcb n v hzero)
  have hs v : Summable (fun n => c n * f n v) :=
    (summable_geometric_two' (η v)).of_norm_bounded (fun n => hdom n v)
  refine ⟨hs, ?_, ?_, ?_, ?_⟩
  · intro v
    simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded
      (hasSum_geometric_two' (η v)) (fun n => hdom n v)
  · simp [hz]
  · intro x y hxy
    exact (hs x).tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_left (hm n hxy) (hc n).le) (hs y)
  · intro x y hxy hn
    rcases hn with ⟨n, hn⟩
    exact (hs x).tsum_lt_tsum (i := n)
      (fun k => mul_le_mul_of_nonneg_left (hm k hxy) (hc k).le)
      (mul_lt_mul_of_pos_left hn (hc n)) (hs y)

theorem exists_anchored_selected_potential [Countable V] (o : V) (E : V → V → Prop)
    (hE : ∀ x y, E x y → x ≤ y) (η : V → ℝ)
    (hηzero : η o = 0) (hηpos : ∀ v, v ≠ o → 0 < η v)
    (hcut : ∀ x y, E x y → ¬y ≤ x ∧
      (((Set.Iic x).Finite ∧ ¬o ≤ x) ∨ ((Set.Ici y).Finite ∧ ¬y ≤ o))) :
    ∃ u : V → ℝ, Monotone u ∧ u o = 0 ∧
      (∀ v, |u v| ≤ η v) ∧ ∀ x y, E x y → u x < u y := by
  classical
  letI : Nonempty V := ⟨o⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (V × V)
  have hex n : ∃ f : V → ℝ, Monotone f ∧ (Function.support f).Finite ∧
      (∀ v, |f v| ≤ 1) ∧ f o = 0 ∧
      (E (e n).1 (e n).2 → f (e n).1 < f (e n).2) := by
    by_cases hn : E (e n).1 (e n).2
    · rcases finite_anchored_cut_exists o (e n).1 (e n).2
        (hcut _ _ hn).1 (hcut _ _ hn).2 with ⟨f, hm, hf, hb, hz, hs⟩
      exact ⟨f, hm, hf, hb, hz, fun _ => hs⟩
    · exact ⟨fun _ => 0, monotone_const, by simp, by norm_num, rfl, fun h => (hn h).elim⟩
  choose f hm hf hb hz hs using hex
  obtain ⟨c, hc, hcb⟩ := positive_anchored_coefficients o f η hf hz hηpos
  have hη v : 0 ≤ η v := by
    by_cases hv : v = o
    · simp [hv, hηzero]
    · exact (hηpos v hv).le
  obtain ⟨_, hbound, hzero, hmono, hstrict⟩ :=
    anchored_series_envelope o f η c hm hb hz hη hc hcb
  refine ⟨fun v => ∑' n, c n * f n v, hmono, hzero, hbound, ?_⟩
  intro x y hxy
  obtain ⟨n, hn⟩ := he (x, y)
  apply hstrict x y (hE x y hxy)
  refine ⟨n, ?_⟩
  simpa only [hn, Prod.fst, Prod.snd] using hs n (by simpa [hn] using hxy)

theorem infinite_ideal_nonnegative (u : V → ℝ) (hu : Monotone u)
    (hlim : Filter.Tendsto u Filter.cofinite (nhds 0)) {x : V}
    (hx : (Set.Iic x).Infinite) : 0 ≤ u x := by
  by_contra hn
  have he := (tendsto_order.mp hlim).1 (u x) (lt_of_not_ge hn)
  have hfinite := Filter.eventually_cofinite.mp he
  exact hx (hfinite.subset (fun v hv => by
    simp only [Set.mem_setOf_eq]
    exact not_lt.mpr (hu hv)))

theorem infinite_filter_nonpositive (u : V → ℝ) (hu : Monotone u)
    (hlim : Filter.Tendsto u Filter.cofinite (nhds 0)) {y : V}
    (hy : (Set.Ici y).Infinite) : u y ≤ 0 := by
  by_contra hn
  have he := (tendsto_order.mp hlim).2 (u y) (lt_of_not_ge hn)
  have hfinite := Filter.eventually_cofinite.mp he
  exact hy (hfinite.subset (fun v hv => by
    simp only [Set.mem_setOf_eq]
    exact not_lt.mpr (hu hv)))

theorem necessary_anchored_cut (o : V) (u : V → ℝ) (hu : Monotone u) (hzero : u o = 0)
    (hlim : Filter.Tendsto u Filter.cofinite (nhds 0)) {x y : V} (hxy : u x < u y) :
    ¬y ≤ x ∧ (((Set.Iic x).Finite ∧ ¬o ≤ x) ∨ ((Set.Ici y).Finite ∧ ¬y ≤ o)) := by
  constructor
  · intro hyx
    exact (not_le.mpr hxy) (hu hyx)
  · by_contra hn
    have hxnone : ¬((Set.Iic x).Finite ∧ ¬o ≤ x) := fun hx => hn (Or.inl hx)
    have hynone : ¬((Set.Ici y).Finite ∧ ¬y ≤ o) := fun hy => hn (Or.inr hy)
    have hx : 0 ≤ u x := by
      by_cases hox : o ≤ x
      · simpa only [hzero] using hu hox
      · exact infinite_ideal_nonnegative u hu hlim (fun hf => hxnone ⟨hf, hox⟩)
    have hy : u y ≤ 0 := by
      by_cases hyo : y ≤ o
      · simpa only [hzero] using hu hyo
      · exact infinite_filter_nonpositive u hu hlim (fun hf => hynone ⟨hf, hyo⟩)
    linarith

theorem bounded_tendsto_zero {η u : V → ℝ}
    (hbound : ∀ v, |u v| ≤ η v)
    (hlim : Filter.Tendsto η Filter.cofinite (nhds 0)) :
    Filter.Tendsto u Filter.cofinite (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero u).mpr
  exact squeeze_zero (fun v => abs_nonneg (u v)) hbound hlim

theorem anchored_finite_cut_iff [Countable V] (o : V) (E : V → V → Prop)
    (hE : ∀ x y, E x y → x ≤ y) (η : V → ℝ)
    (hηzero : η o = 0) (hηpos : ∀ v, v ≠ o → 0 < η v)
    (hlim : Filter.Tendsto η Filter.cofinite (nhds 0)) :
    (∀ x y, E x y → ¬y ≤ x ∧
      (((Set.Iic x).Finite ∧ ¬o ≤ x) ∨ ((Set.Ici y).Finite ∧ ¬y ≤ o))) ↔
      ∃ u : V → ℝ, Monotone u ∧ u o = 0 ∧
        (∀ v, |u v| ≤ η v) ∧ ∀ x y, E x y → u x < u y := by
  constructor
  · exact exists_anchored_selected_potential o E hE η hηzero hηpos
  · rintro ⟨u, hm, hz, hb, hs⟩ x y hxy
    exact necessary_anchored_cut o u hm hz (bounded_tendsto_zero hb hlim) (hs x y hxy)

theorem finite_levels_tendsto_zero (η : V → ℝ) (hη : ∀ v, 0 ≤ η v)
    (hfinite : ∀ ε : ℝ, 0 < ε → {v : V | ε ≤ η v}.Finite) :
    Filter.Tendsto η Filter.cofinite (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun v => ha.trans_le (hη v))
  · intro a ha
    apply Filter.eventually_cofinite.mpr
    simpa only [not_lt] using hfinite a ha

theorem anchored_finite_cut_iff_finite_levels [Countable V]
    (o : V) (E : V → V → Prop) (hE : ∀ x y, E x y → x ≤ y) (η : V → ℝ)
    (hηzero : η o = 0) (hηpos : ∀ v, v ≠ o → 0 < η v)
    (hfinite : ∀ ε : ℝ, 0 < ε → {v : V | ε ≤ η v}.Finite) :
    (∀ x y, E x y → ¬y ≤ x ∧
      (((Set.Iic x).Finite ∧ ¬o ≤ x) ∨ ((Set.Ici y).Finite ∧ ¬y ≤ o))) ↔
      ∃ u : V → ℝ, Monotone u ∧ u o = 0 ∧
        (∀ v, |u v| ≤ η v) ∧ ∀ x y, E x y → u x < u y := by
  have hη v : 0 ≤ η v := by
    by_cases hv : v = o
    · simp [hv, hηzero]
    · exact (hηpos v hv).le
  exact anchored_finite_cut_iff o E hE η hηzero hηpos
    (finite_levels_tendsto_zero η hη hfinite)

end RematAnchoredCuts

#print axioms RematAnchoredCuts.lowerCut_monotone
#print axioms RematAnchoredCuts.upperCut_monotone
#print axioms RematAnchoredCuts.lowerCut_support
#print axioms RematAnchoredCuts.upperCut_support
#print axioms RematAnchoredCuts.lowerCut_abs
#print axioms RematAnchoredCuts.upperCut_abs
#print axioms RematAnchoredCuts.finite_anchored_cut_exists
#print axioms RematAnchoredCuts.finite_positive_lower_bound_on
#print axioms RematAnchoredCuts.positive_anchored_coefficients
#print axioms RematAnchoredCuts.anchored_series_envelope
#print axioms RematAnchoredCuts.exists_anchored_selected_potential
#print axioms RematAnchoredCuts.infinite_ideal_nonnegative
#print axioms RematAnchoredCuts.infinite_filter_nonpositive
#print axioms RematAnchoredCuts.necessary_anchored_cut
#print axioms RematAnchoredCuts.bounded_tendsto_zero
#print axioms RematAnchoredCuts.anchored_finite_cut_iff
#print axioms RematAnchoredCuts.finite_levels_tendsto_zero
#print axioms RematAnchoredCuts.anchored_finite_cut_iff_finite_levels

namespace RematSampleIsolation

theorem isolation_cleared {x y T : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hy : y ≤ 1) (hT : 1 ≤ T) (hsep : x * y ≤ (y - x) * T ^ 2) :
    x ^ 2 + y ^ 2 < 16 * T ^ 2 * (y - x) := by
  have hypos : 0 < y := hx.trans_le hxy
  have hT2 : 1 ≤ T ^ 2 := by nlinarith
  have hxypos : 0 < x * y := mul_pos hx hypos
  have hx2 : x ^ 2 ≤ x * y := by nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hxy)]
  by_cases hnear : y ≤ 2 * x
  · have hy2 : y ^ 2 ≤ 2 * (x * y) := by
      nlinarith [mul_nonneg hypos.le (sub_nonneg.mpr hnear)]
    nlinarith
  · have hfar : 2 * x < y := lt_of_not_ge hnear
    have hy2 : y ^ 2 ≤ y := by nlinarith
    have hxyle : x * y ≤ y := by nlinarith
    have hgap : y / 2 < y - x := by linarith
    have hprod : y / 2 < T ^ 2 * (y - x) :=
      hgap.trans_le (le_mul_of_one_le_left (by linarith) hT2)
    nlinarith

theorem disjoint_radius_ordered {x y T : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hy : y ≤ 1) (hT : 1 ≤ T) (hsep : x * y / T ^ 2 ≤ y - x) :
    x ^ 2 / (16 * T ^ 2) + y ^ 2 / (16 * T ^ 2) < y - x := by
  have hTpos : 0 < T := by linarith
  have hsep' : x * y ≤ (y - x) * T ^ 2 := (div_le_iff₀ (sq_pos_of_pos hTpos)).mp hsep
  have h := isolation_cleared hx hxy hy hT hsep'
  rw [← add_div]
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith

theorem rational_cross_difference (t s M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    (((t : ℝ) / M - (s : ℝ) / N) * ((M : ℝ) * N)) =
      ((t : ℤ) * N - (s : ℤ) * M : ℤ) := by
  push_cast
  have hMr : (M : ℝ) ≠ 0 := by positivity
  have hNr : (N : ℝ) ≠ 0 := by positivity
  field_simp

theorem rational_separation (t s M N T : ℕ)
    (ht : 0 < t) (hs : 0 < s) (hM : 0 < M) (hN : 0 < N)
    (htT : t ≤ T) (hsT : s ≤ T)
    (hne : (t : ℝ) / M ≠ (s : ℝ) / N) :
    ((t : ℝ) / M) * ((s : ℝ) / N) / (T : ℝ) ^ 2 ≤
      |(t : ℝ) / M - (s : ℝ) / N| := by
  have hMr : 0 < (M : ℝ) := by positivity
  have hNr : 0 < (N : ℝ) := by positivity
  have hTr : 0 < (T : ℝ) := by exact_mod_cast ht.trans_le htT
  have hid := rational_cross_difference t s M N hM hN
  have hd : (t : ℤ) * N - (s : ℤ) * M ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero] at hid
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_right (ne_of_gt (mul_pos hMr hNr))))
  have hab : (1 : ℝ) ≤ |(((t : ℤ) * N - (s : ℤ) * M : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hd
  rw [← hid, abs_mul, abs_of_pos (mul_pos hMr hNr)] at hab
  have hprod : (t : ℝ) * s ≤ (T : ℝ) ^ 2 := by
    have htTr : (t : ℝ) ≤ T := by exact_mod_cast htT
    have hsTr : (s : ℝ) ≤ T := by exact_mod_cast hsT
    nlinarith [mul_nonneg (sub_nonneg.mpr htTr) (sub_nonneg.mpr hsTr),
      mul_nonneg (show (0 : ℝ) ≤ s by positivity) (sub_nonneg.mpr htTr),
      mul_nonneg (show (0 : ℝ) ≤ T by positivity) (sub_nonneg.mpr hsTr)]
  have hid2 : ((t : ℝ) / M * ((s : ℝ) / N)) * ((M : ℝ) * N) = (t : ℝ) * s := by
    field_simp
  apply (div_le_iff₀ (sq_pos_of_pos hTr)).mpr
  apply le_of_mul_le_mul_right (a := (M : ℝ) * N) _ (mul_pos hMr hNr)
  rw [hid2]
  calc
    (t : ℝ) * s ≤ (T : ℝ) ^ 2 := hprod
    _ ≤ (|(t : ℝ) / M - (s : ℝ) / N| * ((M : ℝ) * N)) * (T : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (T : ℝ)) (sub_nonneg.mpr hab)]
    _ = _ := by ring

theorem rational_radius_disjoint_ordered (t s M N T : ℕ)
    (ht : 0 < t) (hs : 0 < s) (hM : 0 < M) (hN : 0 < N)
    (htT : t ≤ T) (hsT : s ≤ T) (hsN : s ≤ N)
    (hlt : (t : ℝ) / M < (s : ℝ) / N) :
    ((t : ℝ) / M) ^ 2 / (16 * (T : ℝ) ^ 2) +
      ((s : ℝ) / N) ^ 2 / (16 * (T : ℝ) ^ 2) <
        (s : ℝ) / N - (t : ℝ) / M := by
  apply disjoint_radius_ordered (by positivity) hlt.le
    ((div_le_one (by positivity : (0 : ℝ) < N)).mpr (by exact_mod_cast hsN))
    (by exact_mod_cast ht.trans_le htT)
  have h := rational_separation t s M N T ht hs hM hN htT hsT (ne_of_lt hlt)
  rwa [abs_of_neg (sub_neg.mpr hlt), neg_sub] at h

end RematSampleIsolation

#print axioms RematSampleIsolation.isolation_cleared
#print axioms RematSampleIsolation.disjoint_radius_ordered
#print axioms RematSampleIsolation.rational_cross_difference
#print axioms RematSampleIsolation.rational_separation
#print axioms RematSampleIsolation.rational_radius_disjoint_ordered

open scoped BigOperators Topology ContDiff
open Filter

namespace RematDiagonalSmooth

noncomputable def coefficient (ε : ℝ) (d : ℕ → ℝ) (K : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  min (d n) ((ε / 2 / 2 ^ n) / (1 + ∑ k ∈ Finset.range (n + 3), K k n))

theorem coefficient_pos {ε : ℝ} (hε : 0 < ε) {d : ℕ → ℝ} (hd : ∀ n, 0 < d n)
    {K : ℕ → ℕ → ℝ} (hK : ∀ k n, 0 ≤ K k n) (n : ℕ) :
    0 < coefficient ε d K n := by
  unfold coefficient
  have hs : 0 ≤ ∑ k ∈ Finset.range (n + 3), K k n := Finset.sum_nonneg (fun k _ => hK k n)
  exact lt_min (hd n) (by positivity)

theorem coefficient_le (ε : ℝ) (d : ℕ → ℝ) (K : ℕ → ℕ → ℝ) (n : ℕ) :
    coefficient ε d K n ≤ d n := min_le_left _ _

theorem coefficient_derivative_budget {ε : ℝ} (hε : 0 < ε) {d : ℕ → ℝ}
    (hd : ∀ n, 0 < d n) {K : ℕ → ℕ → ℝ} (hK : ∀ k n, 0 ≤ K k n)
    (k n : ℕ) (hk : k ≤ n + 2) :
    coefficient ε d K n * K k n ≤ ε / 2 / 2 ^ n := by
  have hs : 0 ≤ ∑ j ∈ Finset.range (n + 3), K j n := Finset.sum_nonneg (fun j _ => hK j n)
  have hsum : K k n ≤ ∑ j ∈ Finset.range (n + 3), K j n :=
    Finset.single_le_sum (fun j _ => hK j n) (Finset.mem_range.mpr (by omega))
  have hden : 0 < 1 + ∑ j ∈ Finset.range (n + 3), K j n := by linarith
  have hc := (le_div_iff₀ hden).mp
    (show coefficient ε d K n ≤ (ε / 2 / 2 ^ n) /
      (1 + ∑ j ∈ Finset.range (n + 3), K j n) from min_le_right _ _)
  have hpos := coefficient_pos hε hd hK n
  nlinarith

theorem diagonal_majorant_summable {ε : ℝ} (hε : 0 < ε) {d : ℕ → ℝ}
    (hd : ∀ n, 0 < d n) {K : ℕ → ℕ → ℝ} (hK : ∀ k n, 0 ≤ K k n) (k : ℕ) :
    Summable (fun n => coefficient ε d K n * K k n) := by
  apply (summable_geometric_two' ε).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop k] with n hn
  rw [Real.norm_of_nonneg (mul_nonneg (coefficient_pos hε hd hK n).le (hK k n))]
  exact coefficient_derivative_budget hε hd hK k n (by omega)

theorem compact_derivative_bounds (g : ℕ → ℝ → ℝ)
    (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hc : ∀ n, HasCompactSupport (g n)) :
    ∃ K : ℕ → ℕ → ℝ, (∀ k n, 0 ≤ K k n) ∧
      ∀ k n x, ‖iteratedFDeriv ℝ k (g n) x‖ ≤ K k n := by
  have hex k n : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ k (g n) x‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((hc n).iteratedFDeriv (𝕜 := ℝ) k).exists_bound_of_continuous
      ((hg n).continuous_iteratedFDeriv (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
  choose K hK hb using hex
  exact ⟨K, hK, hb⟩

theorem zero_germ_zero_jet (g : ℝ → ℝ) (hg : g =ᶠ[𝓝 0] 0) (k : ℕ) :
    iteratedFDeriv ℝ k g 0 = 0 := by
  simpa using (hg.iteratedFDeriv ℝ k).self_of_nhds

theorem diagonal_smooth_series (g : ℕ → ℝ → ℝ)
    (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hcompact : ∀ n, HasCompactSupport (g n))
    (hzero : ∀ n, g n =ᶠ[𝓝 0] 0) (ε : ℝ) (hε : 0 < ε)
    (d : ℕ → ℝ) (hd : ∀ n, 0 < d n) :
    ∃ c : ℕ → ℝ, (∀ n, 0 < c n ∧ c n ≤ d n) ∧
      (∀ x, Summable (fun n => c n * g n x)) ∧
      ContDiff ℝ ∞ (fun x => ∑' n, c n * g n x) ∧
      (∀ k, iteratedDeriv k (fun x => ∑' n, c n * g n x) 0 = 0) ∧
      ∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k (fun x => ∑' n, c n * g n x) x| ≤ ε := by
  obtain ⟨K, hK, hbound⟩ := compact_derivative_bounds g hg hcompact
  let c := coefficient ε d K
  have hcpos n : 0 < c n := coefficient_pos hε hd hK n
  have hscaled k n x : ‖iteratedFDeriv ℝ k (fun x => c n * g n x) x‖ ≤ c n * K k n := by
    rw [show (fun x => c n * g n x) = c n • g n from rfl,
      iteratedFDeriv_const_smul_apply ((hg n).contDiffAt.of_le
        (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))),
      norm_smul, Real.norm_of_nonneg (hcpos n).le]
    exact mul_le_mul_of_nonneg_left (hbound k n x) (hcpos n).le
  have hs k : Summable (fun n => c n * K k n) := diagonal_majorant_summable hε hd hK k
  have hsmooth n : ContDiff ℝ ∞ (fun x => c n * g n x) := by
    simpa only [smul_eq_mul] using (hg n).const_smul (c n)
  have hsum : ContDiff ℝ ∞ (fun x => ∑' n, c n * g n x) :=
    contDiff_tsum hsmooth (fun k _ => hs k) (fun k n x _ => hscaled k n x)
  have hderiv k x : iteratedFDeriv ℝ k (fun x => ∑' n, c n * g n x) x =
      ∑' n, iteratedFDeriv ℝ k (fun x => c n * g n x) x :=
    iteratedFDeriv_tsum_apply hsmooth (fun j _ => hs j)
      (fun j n y _ => hscaled j n y) (by simp) x
  refine ⟨c, fun n => ⟨hcpos n, coefficient_le ε d K n⟩, ?_, hsum, ?_, ?_⟩
  · intro x
    apply (hs 0).of_norm_bounded
    intro n
    simpa only [norm_iteratedFDeriv_zero] using hscaled 0 n x
  · intro k
    have hz : iteratedFDeriv ℝ k (fun x => ∑' n, c n * g n x) 0 = 0 := by
      rw [hderiv]
      have hzterm n : iteratedFDeriv ℝ k (fun x => c n * g n x) 0 = 0 := by
        apply zero_germ_zero_jet
        filter_upwards [hzero n] with x hx
        simp only [hx, Pi.zero_apply, mul_zero]
      simp only [hzterm, tsum_zero]
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hz, norm_zero]
  · intro k hk x
    rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hderiv]
    apply tsum_of_norm_bounded (hasSum_geometric_two' ε)
    intro n
    exact (hscaled k n x).trans (coefficient_derivative_budget hε hd hK k n (by omega))

end RematDiagonalSmooth

#print axioms RematDiagonalSmooth.coefficient_pos
#print axioms RematDiagonalSmooth.coefficient_le
#print axioms RematDiagonalSmooth.coefficient_derivative_budget
#print axioms RematDiagonalSmooth.diagonal_majorant_summable
#print axioms RematDiagonalSmooth.compact_derivative_bounds
#print axioms RematDiagonalSmooth.zero_germ_zero_jet
#print axioms RematDiagonalSmooth.diagonal_smooth_series

open scoped BigOperators Topology ContDiff
open Filter

namespace RematCutLift

theorem finite_lift {V : Type*} [DecidableEq V] (o : V) (a : V → ℝ) (b : V → ℝ → ℝ)
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hc : ∀ i, HasCompactSupport (b i))
    (hz : ∀ i, b i =ᶠ[𝓝 0] 0)
    (hi : ∀ i, i ≠ o → ∀ j, b i (a j) = if i = j then 1 else 0)
    (f : V → ℝ) (hf : (Function.support f).Finite) (hfo : f o = 0) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      g =ᶠ[𝓝 0] 0 ∧ ∀ i, g (a i) = f i := by
  classical
  let s := hf.toFinset
  let g : ℝ → ℝ := fun x => ∑ i ∈ s, f i * b i x
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · apply ContDiff.sum
    intro i _
    simpa only [smul_eq_mul] using (hb i).const_smul (f i)
  · have hh : HasCompactSupport (∑ i ∈ s, fun x => f i * b i x) :=
      HasCompactSupport.finset_sum (fun i _ => (hc i).mul_left)
    have hfun : g = ∑ i ∈ s, fun x => f i * b i x := by
      funext x
      simp only [g, Finset.sum_apply]
    rw [hfun]
    exact hh
  · have he : ∀ᶠ x in 𝓝 (0 : ℝ), ∀ i ∈ s, b i x = 0 :=
      (s.eventually_all).mpr (fun i _ => hz i)
    filter_upwards [he] with x hx
    change (∑ i ∈ s, f i * b i x) = 0
    apply Finset.sum_eq_zero
    intro i his
    rw [hx i his, mul_zero]
  · intro j
    change (∑ i ∈ s, f i * b i (a j)) = f j
    have hcalc : (∑ i ∈ s, f i * b i (a j)) = ∑ i ∈ s, if i = j then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i his
      have hfi : f i ≠ 0 := by simpa only [s, Set.Finite.mem_toFinset, Function.mem_support] using his
      have hio : i ≠ o := by rintro rfl; exact hfi hfo
      rw [hi i hio j]
      split_ifs <;> simp
    rw [hcalc]
    by_cases hj : j ∈ s
    · simp [hj]
    · have hfj : f j = 0 := by
        simpa only [s, Set.Finite.mem_toFinset, Function.mem_support, not_not] using hj
      simp [hj, hfj]

theorem bump_at_isolated_sample (x δ : ℝ) (hδ : 0 < δ) (hx : δ < |x|) :
    ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      b =ᶠ[𝓝 0] 0 ∧ b x = 1 ∧ ∀ y, δ ≤ |y - x| → b y = 0 := by
  let b : ContDiffBump x :=
    { rIn := δ / 2
      rOut := δ
      rIn_pos := half_pos hδ
      rIn_lt_rOut := half_lt_self hδ }
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_, ?_, ?_⟩
  · apply notMem_tsupport_iff_eventuallyEq.mp
    rw [b.tsupport_eq]
    simpa only [Metric.mem_closedBall, Real.dist_eq, zero_sub, abs_neg, b, not_le] using hx
  · exact b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hδ).le)
  · intro y hy
    apply b.zero_of_le_dist
    simpa only [Real.dist_eq, b] using hy

theorem sample_bump_family {V : Type*} [DecidableEq V] (o : V) (a δ : V → ℝ)
    (hδ : ∀ i, i ≠ o → 0 < δ i) (ha : ∀ i, i ≠ o → δ i < |a i|)
    (hsep : ∀ i, i ≠ o → ∀ j, i ≠ j → δ i ≤ |a j - a i|) :
    ∃ b : V → ℝ → ℝ, (∀ i, ContDiff ℝ ∞ (b i)) ∧
      (∀ i, HasCompactSupport (b i)) ∧ (∀ i, b i =ᶠ[𝓝 0] 0) ∧
      ∀ i, i ≠ o → ∀ j, b i (a j) = if i = j then 1 else 0 := by
  classical
  have hex i : ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      b =ᶠ[𝓝 0] 0 ∧ (i ≠ o → ∀ j, b (a j) = if i = j then 1 else 0) := by
    by_cases hio : i = o
    · exact ⟨0, contDiff_const, HasCompactSupport.zero, Filter.EventuallyEq.rfl,
        fun h => (h hio).elim⟩
    · obtain ⟨b, hb, hc, hz, hat, hoff⟩ := bump_at_isolated_sample (a i) (δ i) (hδ i hio) (ha i hio)
      refine ⟨b, hb, hc, hz, fun _ j => ?_⟩
      by_cases hij : i = j
      · subst j
        simpa using hat
      · simpa only [if_neg hij] using hoff (a j) (hsep i hio j hij)
  choose b hb hc hz hi using hex
  exact ⟨b, hb, hc, hz, hi⟩

end RematCutLift

#print axioms RematCutLift.finite_lift
#print axioms RematCutLift.bump_at_isolated_sample
#print axioms RematCutLift.sample_bump_family

open scoped BigOperators Topology ContDiff
open Filter

namespace RematSmoothRealization

theorem radius_positive_lt (x U : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (hU : 1 ≤ U) :
    0 < x ^ 2 / (16 * U ^ 2) ∧ x ^ 2 / (16 * U ^ 2) < |x| := by
  have hUpos : 0 < U := by linarith
  have hU2 : 1 ≤ U ^ 2 := by nlinarith
  constructor
  · positivity
  · rw [abs_of_pos hx]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hU2),
      mul_nonneg hx.le (sub_nonneg.mpr hx1)]

theorem rational_sample_radii {V : Type*} (o : V) (a : V → ℝ)
    (t m : V → ℕ) (U : ℕ) (hU : 0 < U) (hao : a o = 0)
    (hinj : Function.Injective a)
    (hdata : ∀ i, i ≠ o → 0 < t i ∧ t i ≤ U ∧ t i ≤ m i ∧ a i = (t i : ℝ) / m i) :
    (∀ i, i ≠ o → 0 < (a i) ^ 2 / (16 * (U : ℝ) ^ 2)) ∧
      (∀ i, i ≠ o → (a i) ^ 2 / (16 * (U : ℝ) ^ 2) < |a i|) ∧
      ∀ i, i ≠ o → ∀ j, i ≠ j → (a i) ^ 2 / (16 * (U : ℝ) ^ 2) ≤ |a j - a i| := by
  have hUr : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hm i (hi : i ≠ o) : 0 < m i := (hdata i hi).1.trans_le (hdata i hi).2.2.1
  have hr i (hi : i ≠ o) :
      0 < (a i) ^ 2 / (16 * (U : ℝ) ^ 2) ∧
        (a i) ^ 2 / (16 * (U : ℝ) ^ 2) < |a i| := by
    apply radius_positive_lt _ _ _ _ hUr
    · rw [(hdata i hi).2.2.2]
      exact div_pos (by exact_mod_cast (hdata i hi).1) (by exact_mod_cast hm i hi)
    · rw [(hdata i hi).2.2.2]
      apply (div_le_one (by exact_mod_cast hm i hi : (0 : ℝ) < m i)).mpr
      exact_mod_cast (hdata i hi).2.2.1
  refine ⟨fun i hi => (hr i hi).1, fun i hi => (hr i hi).2, ?_⟩
  intro i hi j hij
  by_cases hj : j = o
  · simpa only [hj, hao, zero_sub, abs_neg] using (hr i hi).2.le
  · have hne : a i ≠ a j := fun heq => hij (hinj heq)
    have hgap : (a i) ^ 2 / (16 * (U : ℝ) ^ 2) +
        (a j) ^ 2 / (16 * (U : ℝ) ^ 2) < |a j - a i| := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h := RematSampleIsolation.rational_radius_disjoint_ordered
          (t i) (t j) (m i) (m j) U (hdata i hi).1 (hdata j hj).1
          (hm i hi) (hm j hj) (hdata i hi).2.1 (hdata j hj).2.1 (hdata j hj).2.2.1
          (by simpa only [← (hdata i hi).2.2.2, ← (hdata j hj).2.2.2] using hlt)
        simpa only [← (hdata i hi).2.2.2, ← (hdata j hj).2.2.2,
          abs_of_pos (sub_pos.mpr hlt)] using h
      · have h := RematSampleIsolation.rational_radius_disjoint_ordered
          (t j) (t i) (m j) (m i) U (hdata j hj).1 (hdata i hi).1
          (hm j hj) (hm i hi) (hdata j hj).2.1 (hdata i hi).2.1 (hdata i hi).2.2.1
          (by simpa only [← (hdata j hj).2.2.2, ← (hdata i hi).2.2.2] using hgt)
        rw [← (hdata j hj).2.2.2, ← (hdata i hi).2.2.2] at h
        rw [abs_of_neg (sub_neg.mpr hgt), neg_sub]
        linarith
    linarith [(hr j hj).1]

theorem smooth_realization {V : Type*} [Preorder V] [Countable V]
    (o : V) (E : V → V → Prop) (hE : ∀ x y, E x y → x ≤ y)
    (a δ : V → ℝ) (hδ : ∀ i, i ≠ o → 0 < δ i)
    (ha : ∀ i, i ≠ o → δ i < |a i|)
    (hsep : ∀ i, i ≠ o → ∀ j, i ≠ j → δ i ≤ |a j - a i|)
    (η : V → ℝ) (hηzero : η o = 0) (hηpos : ∀ v, v ≠ o → 0 < η v)
    (ε : ℝ) (hε : 0 < ε)
    (hcut : ∀ x y, E x y → ¬y ≤ x ∧
      (((Set.Iic x).Finite ∧ ¬o ≤ x) ∨ ((Set.Ici y).Finite ∧ ¬y ≤ o))) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
      (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ ε) ∧
      (∀ v, |h (a v)| ≤ η v) ∧ Monotone (fun v => h (a v)) ∧
      ∀ x y, E x y → h (a x) < h (a y) := by
  classical
  letI : Nonempty V := ⟨o⟩
  obtain ⟨b, hb, hbc, hbz, hbi⟩ := RematCutLift.sample_bump_family o a δ hδ ha hsep
  obtain ⟨e, he⟩ := exists_surjective_nat (V × V)
  have hex n : ∃ f : V → ℝ, Monotone f ∧ (Function.support f).Finite ∧
      (∀ v, |f v| ≤ 1) ∧ f o = 0 ∧
      (E (e n).1 (e n).2 → f (e n).1 < f (e n).2) := by
    by_cases hn : E (e n).1 (e n).2
    · rcases RematAnchoredCuts.finite_anchored_cut_exists o (e n).1 (e n).2
        (hcut _ _ hn).1 (hcut _ _ hn).2 with ⟨f, hm, hf, hbound, hz, hs⟩
      exact ⟨f, hm, hf, hbound, hz, fun _ => hs⟩
    · exact ⟨fun _ => 0, monotone_const, by simp, by norm_num, rfl, fun h => (hn h).elim⟩
  choose f hm hf hbound hfz hfs using hex
  have hgex n : ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      g =ᶠ[𝓝 0] 0 ∧ ∀ v, g (a v) = f n v :=
    RematCutLift.finite_lift o a b hb hbc hbz hbi (f n) (hf n) (hfz n)
  choose g hg hgc hgz hgi using hgex
  obtain ⟨d, hdpos, hdb⟩ := RematAnchoredCuts.positive_anchored_coefficients o f η hf hfz hηpos
  obtain ⟨c, hc, _, hsmooth, hjet, hnorm⟩ :=
    RematDiagonalSmooth.diagonal_smooth_series g hg hgc hgz ε hε d hdpos
  have hcb n v (hv : f n v ≠ 0) : c n ≤ η v / 2 / 2 ^ n :=
    (hc n).2.trans (hdb n v hv)
  have hη v : 0 ≤ η v := by
    by_cases hv : v = o
    · simp [hv, hηzero]
    · exact (hηpos v hv).le
  obtain ⟨_, hub, _, hum, hus⟩ := RematAnchoredCuts.anchored_series_envelope o f η c hm hbound
    hfz hη (fun n => (hc n).1) hcb
  have hu v : (∑' n, c n * g n (a v)) = ∑' n, c n * f n v := by
    apply tsum_congr
    intro n
    rw [hgi]
  refine ⟨fun x => ∑' n, c n * g n x, hsmooth, ?_, hjet, hnorm, ?_, ?_, ?_⟩
  · simpa only [iteratedDeriv_zero] using hjet 0
  · intro v
    change |∑' n, c n * g n (a v)| ≤ η v
    rw [hu]
    exact hub v
  · intro x y hxy
    change (∑' n, c n * g n (a x)) ≤ ∑' n, c n * g n (a y)
    rw [hu, hu]
    exact hum hxy
  · intro x y hxy
    change (∑' n, c n * g n (a x)) < ∑' n, c n * g n (a y)
    rw [hu, hu]
    apply hus x y (hE x y hxy)
    obtain ⟨n, hn⟩ := he (x, y)
    refine ⟨n, ?_⟩
    simpa only [hn, Prod.fst, Prod.snd] using hfs n (by simpa [hn] using hxy)

theorem smooth_realization_iff {V : Type*} [Preorder V] [Countable V]
    (o : V) (E : V → V → Prop) (hE : ∀ x y, E x y → x ≤ y)
    (a δ : V → ℝ) (hao : a o = 0) (hδ : ∀ i, i ≠ o → 0 < δ i)
    (ha : ∀ i, i ≠ o → δ i < |a i|)
    (hsep : ∀ i, i ≠ o → ∀ j, i ≠ j → δ i ≤ |a j - a i|)
    (η : V → ℝ) (hηzero : η o = 0) (hηpos : ∀ v, v ≠ o → 0 < η v)
    (hfinite : ∀ r : ℝ, 0 < r → {v : V | r ≤ η v}.Finite) (ε : ℝ) (hε : 0 < ε) :
    (∀ x y, E x y → ¬y ≤ x ∧
      (((Set.Iic x).Finite ∧ ¬o ≤ x) ∨ ((Set.Ici y).Finite ∧ ¬y ≤ o))) ↔
      ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
        (∀ k, iteratedDeriv k h 0 = 0) ∧
        (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ ε) ∧
        (∀ v, |h (a v)| ≤ η v) ∧ Monotone (fun v => h (a v)) ∧
        ∀ x y, E x y → h (a x) < h (a y) := by
  constructor
  · exact smooth_realization o E hE a δ hδ ha hsep η hηzero hηpos ε hε
  · rintro ⟨h, _, hz, _, _, hb, hm, hs⟩
    apply (RematAnchoredCuts.anchored_finite_cut_iff_finite_levels o E hE η hηzero hηpos hfinite).mpr
    exact ⟨fun v => h (a v), hm, by simpa only [hao] using hz, hb, hs⟩

theorem rational_smooth_realization_iff {V : Type*} [Preorder V] [Countable V]
    (o : V) (E : V → V → Prop) (hE : ∀ x y, E x y → x ≤ y)
    (a : V → ℝ) (t m : V → ℕ) (U : ℕ) (hU : 0 < U) (hao : a o = 0)
    (hinj : Function.Injective a)
    (hdata : ∀ i, i ≠ o → 0 < t i ∧ t i ≤ U ∧ t i ≤ m i ∧ a i = (t i : ℝ) / m i)
    (η : V → ℝ) (hηzero : η o = 0) (hηpos : ∀ v, v ≠ o → 0 < η v)
    (hfinite : ∀ r : ℝ, 0 < r → {v : V | r ≤ η v}.Finite) (ε : ℝ) (hε : 0 < ε) :
    (∀ x y, E x y → ¬y ≤ x ∧
      (((Set.Iic x).Finite ∧ ¬o ≤ x) ∨ ((Set.Ici y).Finite ∧ ¬y ≤ o))) ↔
      ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
        (∀ k, iteratedDeriv k h 0 = 0) ∧
        (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ ε) ∧
        (∀ v, |h (a v)| ≤ η v) ∧ Monotone (fun v => h (a v)) ∧
        ∀ x y, E x y → h (a x) < h (a y) := by
  obtain ⟨hδ, hab, hsep⟩ := rational_sample_radii o a t m U hU hao hinj hdata
  exact smooth_realization_iff o E hE a (fun i => (a i) ^ 2 / (16 * (U : ℝ) ^ 2))
    hao hδ hab hsep η hηzero hηpos hfinite ε hε

end RematSmoothRealization

#print axioms RematSmoothRealization.radius_positive_lt
#print axioms RematSmoothRealization.rational_sample_radii
#print axioms RematSmoothRealization.smooth_realization
#print axioms RematSmoothRealization.smooth_realization_iff
#print axioms RematSmoothRealization.rational_smooth_realization_iff
end

section
set_option autoImplicit true
set_option autoImplicit false

open Filter Topology
open scoped ContDiff

namespace RematOrderBridge

noncomputable section

@[reducible] def closurePreorder {V : Type*} (R E : V → V → Prop) : Preorder V where
  le := Relation.ReflTransGen (fun x y => R x y ∨ E x y)
  le_refl := fun _ => Relation.ReflTransGen.refl
  le_trans := fun _ _ _ => Relation.ReflTransGen.trans

theorem closure_monotone {V : Type*} (R E : V → V → Prop) (u : V → ℝ)
    (hR : ∀ x y, R x y → u x ≤ u y) (hE : ∀ x y, E x y → u x < u y) :
    @Monotone V ℝ (closurePreorder R E) inferInstance u := by
  intro x y h
  induction h with
  | refl => exact le_rfl
  | tail h hstep ih =>
    exact ih.trans (hstep.elim (hR _ _) (fun hs => (hE _ _ hs).le))

theorem bounded_rational_finite_levels {V : Type*} (o : V) (a : V → ℝ)
    (t m : V → ℕ) (U : ℕ) (hao : a o = 0) (hinj : Function.Injective a)
    (hdata : ∀ i, i ≠ o → 0 < t i ∧ t i ≤ U ∧ t i ≤ m i ∧ a i = (t i : ℝ) / m i)
    (ε : ℝ) (hε : 0 < ε) : {i : V | ε ≤ a i}.Finite := by
  classical
  let B := Nat.ceil ((U : ℝ) / ε)
  have hfin : (Set.Iic U ×ˢ Set.Iic B).Finite := (Set.finite_Iic U).prod (Set.finite_Iic B)
  apply Set.Finite.of_finite_image (f := a) ?_ hinj.injOn
  apply (hfin.image (fun p : ℕ × ℕ => (p.1 : ℝ) / p.2)).subset
  rintro _ ⟨i, hi, rfl⟩
  have hio : i ≠ o := by intro he; subst i; exact (not_le.mpr hε) (by simpa [hao] using hi)
  obtain ⟨ht, htU, htm, he⟩ := hdata i hio
  have hm : (0 : ℝ) < m i := by exact_mod_cast (lt_of_lt_of_le ht htm)
  have him : ε * (m i : ℝ) ≤ t i := (le_div_iff₀ hm).mp (he ▸ hi)
  have htUr : (t i : ℝ) ≤ U := by exact_mod_cast htU
  have hmb : (m i : ℝ) ≤ (U : ℝ) / ε := (le_div_iff₀ hε).mpr (by nlinarith)
  have hmB : m i ≤ B := by exact_mod_cast hmb.trans (Nat.le_ceil ((U : ℝ) / ε))
  exact ⟨(t i, m i), ⟨htU, hmB⟩, he.symm⟩

theorem bounded_rational_tendsto_zero {V : Type*} (o : V) (a : V → ℝ)
    (t m : V → ℕ) (U : ℕ) (hao : a o = 0) (hinj : Function.Injective a)
    (hdata : ∀ i, i ≠ o → 0 < t i ∧ t i ≤ U ∧ t i ≤ m i ∧ a i = (t i : ℝ) / m i) :
    Tendsto a cofinite (𝓝 0) := by
  letI := closurePreorder (fun _ _ : V => False) (fun _ _ => False)
  apply RematAnchoredCuts.finite_levels_tendsto_zero a
  · intro i
    by_cases hi : i = o
    · simp [hi, hao]
    · rw [(hdata i hi).2.2.2]
      positivity
  · exact bounded_rational_finite_levels o a t m U hao hinj hdata

theorem ambient_continuous_finite_cut {V : Type*} (R E : V → V → Prop)
    (o : V) (a : V → ℝ) (t m : V → ℕ) (U : ℕ)
    (hao : a o = 0) (hinj : Function.Injective a)
    (hdata : ∀ i, i ≠ o → 0 < t i ∧ t i ≤ U ∧ t i ≤ m i ∧ a i = (t i : ℝ) / m i)
    (u : ℝ → ℝ) (hu : ContinuousAt u 0) (hzero : u 0 = 0)
    (hR : ∀ x y, R x y → u (a x) ≤ u (a y))
    (hE : ∀ x y, E x y → u (a x) < u (a y)) :
    letI := closurePreorder R E
    ∀ x y, E x y → ¬y ≤ x ∧
      (((Set.Iic x).Finite ∧ ¬o ≤ x) ∨ ((Set.Ici y).Finite ∧ ¬y ≤ o)) := by
  letI := closurePreorder R E
  have hlim : Tendsto (fun v => u (a v)) cofinite (𝓝 0) := by
    simpa only [hzero, Function.comp_def] using hu.tendsto.comp (bounded_rational_tendsto_zero o a t m U hao hinj hdata)
  intro x y hxy
  exact RematAnchoredCuts.necessary_anchored_cut o (fun v => u (a v))
    (closure_monotone R E _ hR hE) (by rw [hao, hzero]) hlim (hE x y hxy)

theorem continuous_relations_smooth {V : Type*} [Countable V]
    (R E : V → V → Prop) (o : V) (a : V → ℝ) (t m : V → ℕ) (U : ℕ)
    (hU : 0 < U) (hao : a o = 0) (hinj : Function.Injective a)
    (hdata : ∀ i, i ≠ o → 0 < t i ∧ t i ≤ U ∧ t i ≤ m i ∧ a i = (t i : ℝ) / m i)
    (u : ℝ → ℝ) (hu : ContinuousAt u 0) (hzero : u 0 = 0)
    (hR : ∀ x y, R x y → u (a x) ≤ u (a y))
    (hE : ∀ x y, E x y → u (a x) < u (a y)) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
      (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ ε) ∧
      (∀ x y, R x y → h (a x) ≤ h (a y)) ∧
      ∀ x y, E x y → h (a x) < h (a y) := by
  letI := closurePreorder R E
  have hEord : ∀ x y, E x y → x ≤ y := fun _ _ he => Relation.ReflTransGen.single (Or.inr he)
  have hapos : ∀ v, v ≠ o → 0 < a v := by
    intro v hv
    obtain ⟨ht, _, htm, he⟩ := hdata v hv
    rw [he]
    exact div_pos (by exact_mod_cast ht) (by exact_mod_cast (ht.trans_le htm))
  have hcut := ambient_continuous_finite_cut R E o a t m U hao hinj hdata u hu hzero hR hE
  obtain ⟨h, hsm, hz, hj, hb, _, hm, he⟩ :=
    (RematSmoothRealization.rational_smooth_realization_iff o E hEord a t m U hU hao hinj hdata
      a hao hapos (bounded_rational_finite_levels o a t m U hao hinj hdata) ε hε).mp hcut
  exact ⟨h, hsm, hz, hj, hb, fun x y hxy => hm (Relation.ReflTransGen.single (Or.inl hxy)), he⟩


def SampleSet (T : ℕ) : Set ℝ :=
  {x | x = 0 ∨ ∃ t m : ℕ, 0 < t ∧ t ≤ T ∧ t ≤ m ∧ x = (t : ℝ) / m}

abbrev Sample (T : ℕ) := ↥(SampleSet T)

def origin (T : ℕ) : Sample T := ⟨0, Or.inl rfl⟩

theorem samples_countable (T : ℕ) : (SampleSet T).Countable := by
  apply (Set.countable_range (fun p : ℕ × ℕ => (p.1 : ℝ) / p.2)).mono
  intro x hx
  rcases hx with rfl | ⟨t, m, _, _, _, he⟩
  · exact ⟨(0, 1), by simp⟩
  · exact ⟨(t, m), he.symm⟩

instance sampleCountable (T : ℕ) : Countable (Sample T) := samples_countable T

theorem sample_representatives (T : ℕ) : ∃ t m : Sample T → ℕ,
    ∀ i, i ≠ origin T → 0 < t i ∧ t i ≤ T ∧ t i ≤ m i ∧ (i : ℝ) = (t i : ℝ) / m i := by
  classical
  have hh (i : Sample T) : ∃ t m : ℕ, i ≠ origin T →
      0 < t ∧ t ≤ T ∧ t ≤ m ∧ (i : ℝ) = (t : ℝ) / m := by
    by_cases hi : i = origin T
    · exact ⟨0, 1, fun h => (h hi).elim⟩
    · rcases i.property with hz | ⟨t, m, ht, htT, htm, he⟩
      · exact (hi (Subtype.ext hz)).elim
      · exact ⟨t, m, fun _ => ⟨ht, htT, htm, he⟩⟩
  choose t m h using hh
  exact ⟨t, m, h⟩

theorem sample_finite_levels (T : ℕ) (ε : ℝ) (hε : 0 < ε) :
    {i : Sample T | ε ≤ (i : ℝ)}.Finite := by
  obtain ⟨t, m, hdata⟩ := sample_representatives T
  exact bounded_rational_finite_levels (origin T) Subtype.val t m T rfl Subtype.val_injective hdata ε hε

theorem sample_tendsto_zero (T : ℕ) :
    Tendsto (Subtype.val : Sample T → ℝ) cofinite (𝓝 0) := by
  obtain ⟨t, m, hdata⟩ := sample_representatives T
  exact bounded_rational_tendsto_zero (origin T) Subtype.val t m T rfl Subtype.val_injective hdata

theorem sample_continuousAt_nonzero (T : ℕ) (hT : 0 < T)
    (u : Sample T → ℝ) (x : Sample T) (hx : x ≠ origin T) : ContinuousAt u x := by
  obtain ⟨t, m, hdata⟩ := sample_representatives T
  obtain ⟨hp, _, hsep⟩ := RematSmoothRealization.rational_sample_radii
    (origin T) (Subtype.val : Sample T → ℝ) t m T hT rfl Subtype.val_injective hdata
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨(x : ℝ) ^ 2 / (16 * (T : ℝ) ^ 2), hp x hx, ?_⟩
  intro y hy
  have hyx : y = x := by
    by_contra hne
    have hs := hsep x hx y (Ne.symm hne)
    have hd : |(y : ℝ) - (x : ℝ)| < (x : ℝ) ^ 2 / (16 * (T : ℝ) ^ 2) := by
      simpa only [Subtype.dist_eq, Real.dist_eq] using hy
    exact (not_lt.mpr hs) hd
  simpa [hyx] using hε

theorem sample_continuous_iff_zero (T : ℕ) (hT : 0 < T) (u : Sample T → ℝ) :
    Continuous u ↔ ContinuousAt u (origin T) := by
  constructor
  · exact fun h => h.continuousAt
  · intro h
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = origin T
    · simpa [hx] using h
    · exact sample_continuousAt_nonzero T hT u x hx

def zeroExtend (S : Set ℝ) (u : S → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if hx : x ∈ S then u ⟨x, hx⟩ else 0

theorem zeroExtend_on (S : Set ℝ) (u : S → ℝ) (x : S) : zeroExtend S u x = u x := by
  classical
  simp [zeroExtend, x.property]

theorem zeroExtend_continuousAt_zero (S : Set ℝ) (hS : 0 ∈ S) (u : S → ℝ)
    (hzero : u ⟨0, hS⟩ = 0) (hu : ContinuousAt u ⟨0, hS⟩) :
    ContinuousAt (zeroExtend S u) 0 := by
  classical
  have hz : zeroExtend S u 0 = 0 := (zeroExtend_on S u ⟨0, hS⟩).trans hzero
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := Metric.continuousAt_iff.mp hu ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  rw [hz]
  by_cases hxs : x ∈ S
  · have hp : dist (⟨x, hxs⟩ : S) ⟨0, hS⟩ < δ := by simpa only [Subtype.dist_eq] using hx
    have he := hh hp
    simpa only [zeroExtend, dif_pos hxs, hzero] using he
  · simp only [zeroExtend, dif_neg hxs, dist_self]
    exact hε

theorem sample_continuous_iff_ambient (T : ℕ) (hT : 0 < T) (u : Sample T → ℝ)
    (hzero : u (origin T) = 0) :
    Continuous u ↔ ∃ f : ℝ → ℝ, ContinuousAt f 0 ∧ f 0 = 0 ∧ ∀ x : Sample T, f (x : ℝ) = u x := by
  constructor
  · intro hu
    refine ⟨zeroExtend (SampleSet T) u, zeroExtend_continuousAt_zero _ (Or.inl rfl) u hzero hu.continuousAt, ?_, ?_⟩
    · simpa only [origin] using (zeroExtend_on (SampleSet T) u (origin T)).trans hzero
    · exact zeroExtend_on _ u
  · rintro ⟨f, hf, _, he⟩
    apply (sample_continuous_iff_zero T hT u).mpr
    have hh : ContinuousAt (fun x : Sample T => f (x : ℝ)) (origin T) :=
      (show ContinuousAt f ((origin T : Sample T) : ℝ) from hf).comp
        (continuous_subtype_val.continuousAt : ContinuousAt (Subtype.val : Sample T → ℝ) (origin T))
    have hfun : (fun x : Sample T => f (x : ℝ)) = u := funext he
    rwa [hfun] at hh

theorem sample_relations_smooth (T : ℕ) (hT : 0 < T)
    (R E : Sample T → Sample T → Prop) (u : Sample T → ℝ)
    (hu : Continuous u) (hzero : u (origin T) = 0)
    (hR : ∀ x y, R x y → u x ≤ u y) (hE : ∀ x y, E x y → u x < u y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
      (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ ε) ∧
      (∀ x y, R x y → h (x : ℝ) ≤ h (y : ℝ)) ∧
      ∀ x y, E x y → h (x : ℝ) < h (y : ℝ) := by
  obtain ⟨t, m, hdata⟩ := sample_representatives T
  obtain ⟨f, hf, hfzero, he⟩ := (sample_continuous_iff_ambient T hT u hzero).mp hu
  apply continuous_relations_smooth R E (origin T) Subtype.val t m T hT rfl Subtype.val_injective
    hdata f hf hfzero
  · simpa only [he] using hR
  · simpa only [he] using hE
  · exact hε


theorem sample_ambient_relations_smooth (T : ℕ) (hT : 0 < T)
    (R E : Sample T → Sample T → Prop) (u : ℝ → ℝ)
    (hu : ContinuousAt u 0) (hzero : u 0 = 0)
    (hR : ∀ x y, R x y → u (x : ℝ) ≤ u (y : ℝ))
    (hE : ∀ x y, E x y → u (x : ℝ) < u (y : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
      (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ ε) ∧
      (∀ x y, R x y → h (x : ℝ) ≤ h (y : ℝ)) ∧
      ∀ x y, E x y → h (x : ℝ) < h (y : ℝ) := by
  obtain ⟨t, m, hdata⟩ := sample_representatives T
  exact continuous_relations_smooth R E (origin T) Subtype.val t m T hT rfl
    Subtype.val_injective hdata u hu hzero hR hE ε hε

theorem sample_feasibility_iff_smooth (T : ℕ) (hT : 0 < T)
    (R E : Sample T → Sample T → Prop) (ε : ℝ) (hε : 0 < ε) :
    (∃ u : Sample T → ℝ, Continuous u ∧ u (origin T) = 0 ∧
      (∀ x y, R x y → u x ≤ u y) ∧ ∀ x y, E x y → u x < u y) ↔
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
      (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ ε) ∧
      (∀ x y, R x y → h (x : ℝ) ≤ h (y : ℝ)) ∧
      ∀ x y, E x y → h (x : ℝ) < h (y : ℝ) := by
  constructor
  · rintro ⟨u, hu, hz, hR, hE⟩
    exact sample_relations_smooth T hT R E u hu hz hR hE ε hε
  · rintro ⟨h, hsm, hz, _, _, hR, hE⟩
    refine ⟨fun x => h (x : ℝ), hsm.continuous.comp continuous_subtype_val, ?_, hR, hE⟩
    exact hz

theorem fraction_mem_samples (T t m : ℕ) (htT : t ≤ T) (htm : t ≤ m) :
    (t : ℝ) / m ∈ SampleSet T := by
  by_cases ht : t = 0
  · left
    simp [ht]
  · exact Or.inr ⟨t, m, Nat.pos_of_ne_zero ht, htT, htm, rfl⟩

theorem scaled_fraction_mem_samples (T H t m : ℕ) (hH : 0 < H) (htT : t ≤ T) (htm : t ≤ m) :
    (t : ℝ) / (H * m : ℕ) ∈ SampleSet T := by
  apply fraction_mem_samples T t (H * m) htT
  exact htm.trans (by nlinarith)


theorem sample_strict_order_realizable (T : ℕ) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
      (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ ε) ∧
      (∀ x y : Sample T, (x : ℝ) ≤ y → h (x : ℝ) ≤ h (y : ℝ)) ∧
      ∀ x y : Sample T, (x : ℝ) < y → h (x : ℝ) < h (y : ℝ) := by
  exact sample_ambient_relations_smooth T hT
    (fun x y => (x : ℝ) ≤ y) (fun x y => (x : ℝ) < y) id
    continuous_id.continuousAt rfl (fun _ _ h => h) (fun _ _ h => h) ε hε

theorem sample_positive (T : ℕ) (x : Sample T) (hx : x ≠ origin T) : 0 < (x : ℝ) := by
  rcases x.property with hz | ⟨t, m, ht, _, htm, he⟩
  · exact (hx (Subtype.ext hz)).elim
  · rw [he]
    exact div_pos (by exact_mod_cast ht) (by exact_mod_cast (ht.trans_le htm))

theorem finite_support_sample_continuous (T : ℕ) (hT : 0 < T)
    (u : Sample T → ℝ) (hz : u (origin T) = 0) (hfin : (Function.support u).Finite) :
    Continuous u := by
  classical
  apply (sample_continuous_iff_zero T hT u).mpr
  let s := hfin.toFinset
  have hpos : ∀ x ∈ s, 0 < (x : ℝ) := by
    intro x hx
    have hux : u x ≠ 0 := by simpa only [s, Set.Finite.mem_toFinset, Function.mem_support] using hx
    exact sample_positive T x (by intro he; exact hux (he ▸ hz))
  obtain ⟨δ, hδ, hb⟩ := RematAnchoredCuts.finite_positive_lower_bound_on s
    (fun x : Sample T => (x : ℝ)) hpos
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hux : u x = 0 := by
    by_contra hn
    have hxs : x ∈ s := by simpa only [s, Set.Finite.mem_toFinset, Function.mem_support] using hn
    have hl := hb x hxs
    have hd : |(x : ℝ)| < δ := by simpa only [Subtype.dist_eq, Real.dist_eq, origin, sub_zero] using hx
    exact (not_lt.mpr (hl.trans (le_abs_self _))) hd
  simpa only [hux, hz, dist_self] using hε

theorem finite_relations_smooth (T : ℕ) (hT : 0 < T)
    (R E : Sample T → Sample T → Prop) (s : Finset (Sample T))
    (hs : ∀ x y, R x y ∨ E x y → x ∈ s ∧ y ∈ s)
    (u : Sample T → ℝ) (hz : u (origin T) = 0)
    (hR : ∀ x y, R x y → u x ≤ u y) (hE : ∀ x y, E x y → u x < u y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
      (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ ε) ∧
      (∀ x y, R x y → h (x : ℝ) ≤ h (y : ℝ)) ∧
      ∀ x y, E x y → h (x : ℝ) < h (y : ℝ) := by
  classical
  let v : Sample T → ℝ := fun x => if x ∈ s then u x else 0
  have hvz : v (origin T) = 0 := by simp [v, hz]
  have hfin : (Function.support v).Finite := by
    apply s.finite_toSet.subset
    intro x hx
    by_contra hn
    have hn' : x ∉ s := hn
    exact hx (by simp [v, hn'])
  have hvR : ∀ x y, R x y → v x ≤ v y := by
    intro x y hxy
    obtain ⟨hx, hy⟩ := hs x y (Or.inl hxy)
    simpa only [v, if_pos hx, if_pos hy] using hR x y hxy
  have hvE : ∀ x y, E x y → v x < v y := by
    intro x y hxy
    obtain ⟨hx, hy⟩ := hs x y (Or.inr hxy)
    simpa only [v, if_pos hx, if_pos hy] using hE x y hxy
  exact sample_relations_smooth T hT R E v (finite_support_sample_continuous T hT v hvz hfin)
    hvz hvR hvE ε hε

theorem continuous_subtype_extension_at_zero (S : Set ℝ) (hS : 0 ∈ S)
    (u : S → ℝ) (hu : ContinuousAt u ⟨0, hS⟩) :
    ∃ f : ℝ → ℝ, ContinuousAt f 0 ∧ ∀ x : S, f (x : ℝ) = u x := by
  let v : S → ℝ := fun x => u x - u ⟨0, hS⟩
  have hvz : v ⟨0, hS⟩ = 0 := sub_self _
  have hv : ContinuousAt v ⟨0, hS⟩ := hu.sub continuousAt_const
  refine ⟨fun x => zeroExtend S v x + u ⟨0, hS⟩,
    (zeroExtend_continuousAt_zero S hS v hvz hv).add continuousAt_const, ?_⟩
  intro x
  change zeroExtend S v (x : ℝ) + u ⟨0, hS⟩ = u x
  rw [zeroExtend_on]
  exact sub_add_cancel _ _

theorem continuous_interval_extension_at_zero
    (u : Set.Icc (0 : ℝ) 1 → ℝ) (hu : Continuous u) :
    ∃ f : ℝ → ℝ, ContinuousAt f 0 ∧ ∀ x : Set.Icc (0 : ℝ) 1, f (x : ℝ) = u x :=
  continuous_subtype_extension_at_zero (Set.Icc (0 : ℝ) 1) (by norm_num) u hu.continuousAt

end

end RematOrderBridge

#print axioms RematOrderBridge.closure_monotone
#print axioms RematOrderBridge.bounded_rational_finite_levels
#print axioms RematOrderBridge.bounded_rational_tendsto_zero
#print axioms RematOrderBridge.ambient_continuous_finite_cut
#print axioms RematOrderBridge.continuous_relations_smooth
#print axioms RematOrderBridge.samples_countable
#print axioms RematOrderBridge.sample_representatives
#print axioms RematOrderBridge.sample_finite_levels
#print axioms RematOrderBridge.sample_tendsto_zero
#print axioms RematOrderBridge.sample_continuousAt_nonzero
#print axioms RematOrderBridge.sample_continuous_iff_zero
#print axioms RematOrderBridge.zeroExtend_on
#print axioms RematOrderBridge.zeroExtend_continuousAt_zero
#print axioms RematOrderBridge.sample_continuous_iff_ambient
#print axioms RematOrderBridge.sample_relations_smooth
#print axioms RematOrderBridge.sample_ambient_relations_smooth
#print axioms RematOrderBridge.sample_feasibility_iff_smooth
#print axioms RematOrderBridge.fraction_mem_samples
#print axioms RematOrderBridge.scaled_fraction_mem_samples
#print axioms RematOrderBridge.sample_strict_order_realizable
#print axioms RematOrderBridge.sample_positive
#print axioms RematOrderBridge.finite_support_sample_continuous
#print axioms RematOrderBridge.finite_relations_smooth
#print axioms RematOrderBridge.continuous_subtype_extension_at_zero
#print axioms RematOrderBridge.continuous_interval_extension_at_zero
end

section
set_option autoImplicit true
set_option autoImplicit false

open scoped BigOperators

namespace RematTransfer

noncomputable section

variable {N : ℕ}

def index (y : Fin N → ℝ) (n : Fin N → ℤ) : ℤ :=
  (∑ i, n i) - ∑ i, RematRounding.base y i

def occurs (G : ℤ → ℝ) (M : ℤ) (y : Fin N → ℝ) (j : ℤ) : Prop :=
  ∃ n, RematGeneralResidual.isMinimum G M y n ∧ index y n = j

def exactIndex (G : ℤ → ℝ) (M : ℤ) (y : Fin N → ℝ) (j : ℤ) : Prop :=
  occurs G M y j ∧ ∀ n, RematGeneralResidual.isMinimum G M y n → index y n = j

theorem index_base (y : Fin N → ℝ) : index y (RematRounding.base y) = 0 := by
  simp [index]

theorem index_rounded (y : Fin N → ℝ) (E : Finset (Fin N)) :
    index y (RematRounding.rounded y E) = E.card := by
  rw [index, RematRounding.rounded_sum]
  omega

theorem fixed_sum_shift_certificate (y : Fin N → ℝ) (n z : Fin N → ℤ)
    (c : ℝ) (hs : ∑ i, z i = ∑ i, n i)
    (hn : ∀ i, (n i : ℝ) - 1 / 2 ≤ y i - c ∧ y i - c ≤ (n i : ℝ) + 1 / 2) :
    RematGeneral.loss y n ≤ RematGeneral.loss y z := by
  have hnear : GridResidueCertificate.loss (fun i => y i - c) n ≤
      GridResidueCertificate.loss (fun i => y i - c) z := by
    exact Finset.sum_le_sum (fun i _ => GridResidueCertificate.nearest_integer _ _ _ (hn i).1 (hn i).2)
  have hsum : (∑ i, (z i : ℝ)) = ∑ i, (n i : ℝ) := by exact_mod_cast hs
  have he := GridResidueCertificate.shifted_loss_difference y n z c
  rw [hsum] at he
  change GridResidueCertificate.loss y n ≤ GridResidueCertificate.loss y z
  linarith

theorem floor_fitting_minimum (y : Fin N → ℝ)
    (hf : ∀ i, RematRounding.fraction y i ≤ 1 / 2) (n : Fin N → ℤ) :
    RematGeneral.loss y (RematRounding.base y) ≤ RematGeneral.loss y n := by
  apply Finset.sum_le_sum
  intro i _
  have hlo := (RematRounding.fraction_bounds y i).1
  have hhi := hf i
  dsimp [RematRounding.fraction] at hlo hhi
  exact GridResidueCertificate.nearest_integer _ _ _ (by linarith) (by linarith)

theorem one_fitting_minimum (y : Fin N → ℝ) (i₀ : Fin N) (q : ℝ)
    (hq : q ≤ 1 / 2) (hf : ∀ i, RematRounding.fraction y i ≤ q)
    (hmax : RematRounding.fraction y i₀ = q) (n : Fin N → ℤ) (hn : index y n = 1) :
    RematGeneral.loss y (RematRounding.rounded y {i₀}) ≤ RematGeneral.loss y n := by
  classical
  apply fixed_sum_shift_certificate y _ n (q - 1 / 2)
  · have hs := RematRounding.rounded_sum y {i₀}
    simp only [Finset.card_singleton, Nat.cast_one] at hs
    dsimp [index] at hn
    omega
  · intro i
    have hlo := (RematRounding.fraction_bounds y i).1
    have hhi := hf i
    dsimp [RematRounding.fraction] at hlo hhi hmax
    by_cases hi : i = i₀
    · subst i
      simp only [RematRounding.rounded, Finset.mem_singleton_self, ite_true, Int.cast_add, Int.cast_one]
      constructor <;> linarith
    · simp only [RematRounding.rounded, Finset.mem_singleton, hi, ite_false, add_zero]
      constructor <;> linarith

theorem fixed_index_zero_loss (G : ℤ → ℝ) (M : ℤ) (y : Fin N → ℝ)
    (hf : ∀ i, RematRounding.fraction y i ≤ 1 / 2) (n : Fin N → ℤ) (hn : index y n = 0) :
    RematGeneralResidual.loss G M y (RematRounding.base y) ≤ RematGeneralResidual.loss G M y n := by
  have hfit := floor_fitting_minimum y hf n
  have hs : ∑ i, n i = ∑ i, RematRounding.base y i := by dsimp [index] at hn; omega
  simp only [RematGeneralResidual.loss, hs]
  linarith

theorem fixed_index_one_loss (G : ℤ → ℝ) (M : ℤ) (y : Fin N → ℝ)
    (i₀ : Fin N) (q : ℝ) (hq : q ≤ 1 / 2)
    (hf : ∀ i, RematRounding.fraction y i ≤ q)
    (hmax : RematRounding.fraction y i₀ = q) (n : Fin N → ℤ) (hn : index y n = 1) :
    RematGeneralResidual.loss G M y (RematRounding.rounded y {i₀}) ≤ RematGeneralResidual.loss G M y n := by
  have hfit := one_fitting_minimum y i₀ q hq hf hmax n hn
  have hs : ∑ i, n i = ∑ i, RematRounding.rounded y {i₀} i := by
    have hi := index_rounded y {i₀}
    simp only [Finset.card_singleton, Nat.cast_one] at hi
    dsimp [index] at hn hi
    omega
  simp only [RematGeneralResidual.loss, hs]
  linarith

theorem fixed_slice_global (G : ℤ → ℝ) (M : ℤ) (y : Fin N → ℝ)
    (j : ℤ) (v : Fin N → ℤ) (hv : RematGeneral.feasible M v)
    (hfit : ∀ n, index y n = j → RematGeneralResidual.loss G M y v ≤ RematGeneralResidual.loss G M y n)
    (hobs : occurs G M y j) : RematGeneralResidual.isMinimum G M y v := by
  obtain ⟨n, hn, hi⟩ := hobs
  exact ⟨hv, fun z hz => (hfit n hi).trans (hn.2 z hz)⟩

theorem strict_slice_comparison (G : ℤ → ℝ) (M : ℤ) (y : Fin N → ℝ)
    (j : ℤ) (v w : Fin N → ℤ) (hv : RematGeneral.feasible M v)
    (hw : RematGeneral.feasible M w) (hwi : index y w ≠ j)
    (hfit : ∀ n, index y n = j → RematGeneralResidual.loss G M y v ≤ RematGeneralResidual.loss G M y n)
    (hobs : exactIndex G M y j) :
    RematGeneralResidual.loss G M y v < RematGeneralResidual.loss G M y w := by
  have hmin := fixed_slice_global G M y j v hv hfit hobs.1
  by_contra hnot
  have hwv : RematGeneralResidual.loss G M y w ≤ RematGeneralResidual.loss G M y v := le_of_not_gt hnot
  have hwmin : RematGeneralResidual.isMinimum G M y w :=
    ⟨hw, fun z hz => hwv.trans (hmin.2 z hz)⟩
  exact hwi (hobs.2 w hwmin)

theorem minimum_index_bounds (G : ℤ → ℝ) (M : ℤ)
    (hG : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ M → G a ≤ G b)
    (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (n : Fin N → ℤ) (hn : RematGeneralResidual.isMinimum G M y n) :
    0 ≤ index y n ∧ index y n ≤ (RematRounding.capacity M y : ℤ) := by
  have hlo : (∑ i, RematRounding.base y i) ≤ ∑ i, n i :=
    Finset.sum_le_sum (fun i _ => RematGeneralResidual.coordinate_lower G M hG y hy hs n hn i)
  have hcap := RematRounding.capacity_cast M y hs
  have hsum := hn.1.2
  dsimp [index]
  omega

theorem base_feasible (M : ℤ) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hs : ∑ i, y i = (M : ℝ)) : RematGeneral.feasible M (RematRounding.base y) := by
  have h := (RematRounding.rounded_feasible_iff M y hy hs ∅).mpr (by simp)
  have he : RematRounding.rounded y ∅ = RematRounding.base y := by
    funext i
    simp [RematRounding.rounded]
  rwa [he] at h

theorem one_feasible (M : ℤ) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hs : ∑ i, y i = (M : ℝ)) (i₀ : Fin N) (hk : 1 ≤ RematRounding.capacity M y) :
    RematGeneral.feasible M (RematRounding.rounded y {i₀}) := by
  exact (RematRounding.rounded_feasible_iff M y hy hs {i₀}).mpr (by simpa using hk)

theorem pair_loss_difference (G : ℤ → ℝ) (M : ℤ) (y : Fin N → ℝ)
    (hs : ∑ i, y i = (M : ℝ)) (t : ℕ) (ht : RematRounding.capacity M y = t)
    (i₀ : Fin N) (q : ℝ) (hmax : RematRounding.fraction y i₀ = q) :
    RematGeneralResidual.loss G M y (RematRounding.rounded y {i₀}) -
      RematGeneralResidual.loss G M y (RematRounding.base y) =
      1 - 2 * q + G ((t : ℤ) - 1) - G t := by
  have hfit : RematGeneral.loss y (RematRounding.rounded y {i₀}) =
      RematGeneral.loss y (RematRounding.base y) + (1 - 2 * q) := by
    rw [RematRounding.rounded_loss]
    simp [RematSelection.cost, RematRounding.benefit, hmax]
  have hcap := RematRounding.capacity_cast M y hs
  rw [ht] at hcap
  unfold RematGeneralResidual.loss
  rw [hfit, RematRounding.rounded_slack M y hs, ht, ← hcap]
  simp only [Finset.card_singleton, Nat.cast_one]
  ring

theorem sampled_quadratic_split (ell : ℝ) (h : ℝ → ℝ) (M : ℤ) (hM : 0 < M) (r : ℤ) :
    RematGeneralResidual.sampledPenalty (fun s => ell * s ^ 2 + h s) M r =
      ell * (r : ℝ) ^ 2 + (M : ℝ) ^ 2 * h ((r : ℝ) / M) := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold RematGeneralResidual.sampledPenalty
  field_simp

theorem sampled_pair_difference (ell : ℝ) (h : ℝ → ℝ) (M : ℤ) (hM : 0 < M)
    (y : Fin N → ℝ) (hs : ∑ i, y i = (M : ℝ)) (t : ℕ)
    (ht : RematRounding.capacity M y = t) (i₀ : Fin N)
    (hmax : RematRounding.fraction y i₀ = (1 - ell * (2 * t - 1)) / 2) :
    let G := RematGeneralResidual.sampledPenalty (fun s => ell * s ^ 2 + h s) M
    RematGeneralResidual.loss G M y (RematRounding.rounded y {i₀}) -
      RematGeneralResidual.loss G M y (RematRounding.base y) =
      (M : ℝ) ^ 2 * (h (((t : ℝ) - 1) / M) - h ((t : ℝ) / M)) := by
  dsimp
  rw [pair_loss_difference _ M y hs t ht i₀ _ hmax]
  rw [sampled_quadratic_split ell h M hM, sampled_quadratic_split ell h M hM]
  push_cast
  ring

theorem all_vector_observation_necessity (ell : ℝ) (h : ℝ → ℝ) (M : ℤ) (hM : 0 < M)
    (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (t : ℕ) (ht : 0 < t) (hcap : RematRounding.capacity M y = t) (i₀ : Fin N)
    (hq : (1 - ell * (2 * t - 1)) / 2 ≤ 1 / 2)
    (hf : ∀ i, RematRounding.fraction y i ≤ (1 - ell * (2 * t - 1)) / 2)
    (hmax : RematRounding.fraction y i₀ = (1 - ell * (2 * t - 1)) / 2) :
    let G := RematGeneralResidual.sampledPenalty (fun s => ell * s ^ 2 + h s) M
    (occurs G M y 0 → h ((t : ℝ) / M) ≤ h (((t : ℝ) - 1) / M)) ∧
    (occurs G M y 1 → h (((t : ℝ) - 1) / M) ≤ h ((t : ℝ) / M)) ∧
    (exactIndex G M y 0 → h ((t : ℝ) / M) < h (((t : ℝ) - 1) / M)) ∧
    (exactIndex G M y 1 → h (((t : ℝ) - 1) / M) < h ((t : ℝ) / M)) := by
  dsimp
  let G := RematGeneralResidual.sampledPenalty (fun s => ell * s ^ 2 + h s) M
  have hb := base_feasible M y hy hs
  have ho := one_feasible M y hy hs i₀ (by omega)
  have hz := fixed_index_zero_loss G M y (fun i => (hf i).trans hq)
  have hu := fixed_index_one_loss G M y i₀ _ hq hf hmax
  have he := sampled_pair_difference ell h M hM y hs t hcap i₀ hmax
  have hp : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hM)
  have hi : index y (RematRounding.rounded y {i₀}) = 1 := by simpa using index_rounded y {i₀}
  change RematGeneralResidual.loss G M y (RematRounding.rounded y {i₀}) -
    RematGeneralResidual.loss G M y (RematRounding.base y) = _ at he
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hobs
    have hcmp := (fixed_slice_global G M y 0 _ hb hz hobs).2 _ ho
    nlinarith
  · intro hobs
    have hcmp := (fixed_slice_global G M y 1 _ ho hu hobs).2 _ hb
    nlinarith
  · intro hobs
    have hcmp := strict_slice_comparison G M y 0 _ _ hb ho (by omega) hz hobs
    nlinarith
  · intro hobs
    have hcmp := strict_slice_comparison G M y 1 _ _ ho hb (by simp [index_base]) hu hobs
    nlinarith

theorem monotone_from_derivatives (f f₁ : ℝ → ℝ)
    (hd : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f₁ x) x)
    (hn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f₁ x) : MonotoneOn f (Set.Icc 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt
  · exact fun x hx => hn x (interior_subset hx)

theorem first_derivative_bound (_h h₁ h₂ : ℝ → ℝ) (eps : ℝ)
    (hd : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h₁ (h₂ x) x)
    (hzero : h₁ 0 = 0) (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h₂ x| ≤ eps)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : |h₁ x| ≤ eps * x := by
  have hup : MonotoneOn (fun s => eps * s - h₁ s) (Set.Icc 0 1) := by
    apply monotone_from_derivatives _ (fun s => eps - h₂ s)
    · intro s hs
      convert! ((hasDerivAt_id s).const_mul eps).sub (hd s hs) using 1; simp
    · intro s hs
      have hb := (abs_le.mp (hbound s hs)).2
      linarith
  have hlo : MonotoneOn (fun s => eps * s + h₁ s) (Set.Icc 0 1) := by
    apply monotone_from_derivatives _ (fun s => eps + h₂ s)
    · intro s hs
      convert! ((hasDerivAt_id s).const_mul eps).add (hd s hs) using 1; simp
    · intro s hs
      have hb := (abs_le.mp (hbound s hs)).1
      linarith
  have hu := hup (by norm_num) hx hx.1
  have hl := hlo (by norm_num) hx hx.1
  simp only [mul_zero, hzero, sub_zero, add_zero] at hu hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem second_derivative_quadratic_bound (h h₁ h₂ : ℝ → ℝ) (eps : ℝ)
    (hd₀ : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h (h₁ x) x)
    (hd₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h₁ (h₂ x) x)
    (hzero : h 0 = 0) (hone : h₁ 0 = 0)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h₂ x| ≤ eps)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : |h x| ≤ eps * x ^ 2 / 2 := by
  have hb s hs := first_derivative_bound h h₁ h₂ eps hd₁ hone hbound s hs
  have hup : MonotoneOn (fun s => eps / 2 * s ^ 2 - h s) (Set.Icc 0 1) := by
    apply monotone_from_derivatives _ (fun s => eps * s - h₁ s)
    · intro s hs
      convert! (((hasDerivAt_id s).pow 2).const_mul (eps / 2)).sub (hd₀ s hs) using 1; simp; ring
    · intro s hs
      have hh := (abs_le.mp (hb s hs)).2
      linarith
  have hlo : MonotoneOn (fun s => eps / 2 * s ^ 2 + h s) (Set.Icc 0 1) := by
    apply monotone_from_derivatives _ (fun s => eps * s + h₁ s)
    · intro s hs
      convert! (((hasDerivAt_id s).pow 2).const_mul (eps / 2)).add (hd₀ s hs) using 1; simp; ring
    · intro s hs
      have hh := (abs_le.mp (hb s hs)).1
      linarith
  have hu := hup (by norm_num) hx hx.1
  have hl := hlo (by norm_num) hx hx.1
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, hzero, sub_zero, add_zero] at hu hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem perturbed_penalty_monotone (ell eps : ℝ) (hell : 0 ≤ ell) (heps : eps ≤ ell)
    (h h₁ h₂ : ℝ → ℝ)
    (hd₀ : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h (h₁ x) x)
    (hd₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h₁ (h₂ x) x)
    (hone : h₁ 0 = 0) (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h₂ x| ≤ eps) :
    MonotoneOn (fun s => ell * s ^ 2 + h s) (Set.Icc 0 1) := by
  apply monotone_from_derivatives _ (fun s => 2 * ell * s + h₁ s)
  · intro s hs
    convert! (((hasDerivAt_id s).pow 2).const_mul ell).add (hd₀ s hs) using 1; simp; ring
  · intro s hs
    have hb := (abs_le.mp (first_derivative_bound h h₁ h₂ eps hd₁ hone hbound s hs)).1
    have hh := mul_le_mul_of_nonneg_right heps hs.1
    have hp := mul_nonneg hell hs.1
    nlinarith

theorem perturbed_curvature_bound (ell eps : ℝ) (heps : eps ≤ ell)
    (h₁ h₂ : ℝ → ℝ) (hd₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h₁ (h₂ x) x)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h₂ x| ≤ eps) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => 2 * ell * s + h₁ s) (2 * ell + h₂ x) x ∧ ell ≤ 2 * ell + h₂ x := by
  intro x hx
  refine ⟨?_, ?_⟩
  · convert! ((hasDerivAt_id x).const_mul (2 * ell)).add (hd₁ x hx) using 1; simp
  · have hb := (abs_le.mp (hbound x hx)).1
    linarith

theorem normalized_error_bound (h : ℝ → ℝ) (eps M T r : ℝ)
    (heps : 0 ≤ eps) (hM : 0 < M) (hr : 0 ≤ r) (hrT : r ≤ T) (hrM : r ≤ M)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h x| ≤ eps * x ^ 2 / 2) :
    |M ^ 2 * h (r / M)| ≤ eps * T ^ 2 / 2 := by
  have hx : r / M ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hr hM.le, (div_le_one₀ hM).mpr hrM⟩
  have hb := mul_le_mul_of_nonneg_left (hbound (r / M) hx) (sq_nonneg M)
  have he : M ^ 2 * (eps * (r / M) ^ 2 / 2) = eps * r ^ 2 / 2 := by
    field_simp
  have hsq : r ^ 2 ≤ T ^ 2 := by nlinarith
  have hep := mul_le_mul_of_nonneg_left hsq heps
  rw [he] at hb
  rw [abs_mul, abs_of_nonneg (sq_nonneg M)]
  linarith

theorem epsilon_budget (ell eps : ℝ) (T : ℕ) (hT : 1 ≤ T)
    (heps : 0 ≤ eps) (hsmall : eps < ell / (T : ℝ) ^ 2) :
    eps * (T : ℝ) ^ 2 < ell ∧ eps < ell := by
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTp : (0 : ℝ) < (T : ℝ) ^ 2 := by positivity
  have hbudget := (lt_div_iff₀ hTp).mp hsmall
  have hs : (1 : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hs heps
  exact ⟨hbudget, by linarith⟩

theorem two_candidate_perturbation_gap (c₀ c₁ c e₀ e₁ e ell B : ℝ)
    (htie : c₁ = c₀) (hgap : c₀ + 2 * ell ≤ c) (hsmall : 2 * B < ell)
    (hzero : |e₀| ≤ B) (hone : |e₁| ≤ B) (he : |e| ≤ B) :
    c₀ + e₀ + ell < c + e ∧ c₁ + e₁ + ell < c + e := by
  obtain ⟨h₀l, h₀u⟩ := abs_le.mp hzero
  obtain ⟨h₁l, h₁u⟩ := abs_le.mp hone
  obtain ⟨hel, heu⟩ := abs_le.mp he
  constructor <;> linarith

theorem scalar_perturbation_excludes (ell eps M : ℝ) (hell : 0 < ell)
    (heps : 0 ≤ eps) (hM : 0 < M) (t T : ℕ) (ht : 0 < t) (htT : t ≤ T)
    (htM : (t : ℝ) ≤ M) (hsmall : eps < ell / (T : ℝ) ^ 2)
    (f : ℕ → ℝ) (hf : ∀ j, j < t → f j ≤ (1 - ell * (2 * t - 1)) / 2)
    (hf₀ : f 0 = (1 - ell * (2 * t - 1)) / 2)
    (h : ℝ → ℝ) (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h x| ≤ eps * x ^ 2 / 2)
    (j : ℕ) (hj : 2 ≤ j) (hjt : j ≤ t) :
    let P := fun m => RematDilationSynthesis.scalarCost ell t f m + M ^ 2 * h (((t : ℝ) - m) / M)
    P 0 + ell < P j ∧ P 1 + ell < P j := by
  have hb m (hm : m ≤ t) : |M ^ 2 * h (((t : ℝ) - m) / M)| ≤ eps * (T : ℝ) ^ 2 / 2 := by
    apply normalized_error_bound h eps M T _ heps hM
    · exact sub_nonneg.mpr (by exact_mod_cast hm)
    · have htt : (t : ℝ) ≤ T := by exact_mod_cast htT
      have hmp : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · have hmp : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · exact hbound
  have hbudget := (epsilon_budget ell eps T (by omega) heps hsmall).1
  exact two_candidate_perturbation_gap _ _ _ _ _ _ ell (eps * (T : ℝ) ^ 2 / 2)
    (RematDilationSynthesis.scalar_first_tie ell t f hf₀)
    (RematDilationSynthesis.scalar_excluded_gap ell hell t f hf j hj hjt)
    (by linarith) (hb 0 (by omega)) (hb 1 (by omega)) (hb j hjt)

theorem two_scalar_minima_iff (P : ℕ → ℝ) (t : ℕ) (ht : 0 < t)
    (hexcluded : ∀ j, 2 ≤ j → j ≤ t → P 0 < P j ∧ P 1 < P j)
    (j : ℕ) (hjt : j ≤ t) :
    (∀ m, m ≤ t → P j ≤ P m) ↔
      (j = 0 ∧ P 0 ≤ P 1) ∨ (j = 1 ∧ P 1 ≤ P 0) := by
  constructor
  · intro hmin
    by_cases hj₀ : j = 0
    · exact Or.inl ⟨hj₀, by simpa [hj₀] using hmin 1 (by omega)⟩
    by_cases hj₁ : j = 1
    · exact Or.inr ⟨hj₁, by simpa [hj₁] using hmin 0 (by omega)⟩
    have hh := (hexcluded j (by omega) hjt).1
    have hz := hmin 0 (by omega)
    linarith
  · rintro (⟨rfl, h01⟩ | ⟨rfl, h10⟩) m hm
    · by_cases h0 : m = 0
      · simp [h0]
      by_cases h1 : m = 1
      · simpa [h1] using h01
      exact (hexcluded m (by omega) hm).1.le
    · by_cases h0 : m = 0
      · simpa [h0] using h10
      by_cases h1 : m = 1
      · simp [h1]
      exact (hexcluded m (by omega) hm).2.le

theorem loss_sampled_split (ell : ℝ) (h : ℝ → ℝ) (M : ℤ) (hM : 0 < M)
    (y : Fin N → ℝ) (n : Fin N → ℤ) :
    RematGeneralResidual.loss (RematGeneralResidual.sampledPenalty (fun s => ell * s ^ 2 + h s) M) M y n =
      RematGeneralResidual.loss (fun r => ell * (r : ℝ) ^ 2) M y n +
      (M : ℝ) ^ 2 * h (((M - ∑ i, n i : ℤ) : ℝ) / M) := by
  unfold RematGeneralResidual.loss
  rw [sampled_quadratic_split ell h M hM]
  ring

theorem rounded_quadratic_gap (ell : ℝ) (hell : 0 < ell) (M : ℤ)
    (y : Fin N → ℝ) (hs : ∑ i, y i = (M : ℝ)) (t : ℕ)
    (ht : RematRounding.capacity M y = t)
    (hf : ∀ i, RematRounding.fraction y i ≤ (1 - ell * (2 * t - 1)) / 2)
    (E : Finset (Fin N)) (hE : 2 ≤ E.card) (hEt : E.card ≤ t) :
    RematGeneralResidual.loss (fun r => ell * (r : ℝ) ^ 2) M y (RematRounding.base y) + 2 * ell ≤
      RematGeneralResidual.loss (fun r => ell * (r : ℝ) ^ 2) M y (RematRounding.rounded y E) := by
  let q := (1 - ell * (2 * t - 1)) / 2
  have hcost : (E.card : ℝ) * (1 - 2 * q) ≤ RematSelection.cost (RematRounding.benefit y) E := by
    calc
      _ = ∑ _i ∈ E, (1 - 2 * q) := by simp; ring
      _ ≤ RematSelection.cost (RematRounding.benefit y) E := by
        apply Finset.sum_le_sum
        intro i hi
        have h := hf i
        dsimp [RematRounding.benefit, q]
        linarith
  have hg := RematDilationSynthesis.scalar_excluded_gap ell hell t (fun _ => q)
    (fun _ _ => le_refl _) E.card hE hEt
  simp only [RematDilationSynthesis.scalarCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_zero, zero_mul, sub_zero] at hg
  have hc := RematRounding.capacity_cast M y hs
  rw [ht] at hc
  unfold RematGeneralResidual.loss
  rw [RematRounding.rounded_loss, RematRounding.rounded_slack M y hs, ht, ← hc]
  push_cast
  linarith

theorem quadratic_pair_tie (ell : ℝ) (M : ℤ) (y : Fin N → ℝ)
    (hs : ∑ i, y i = (M : ℝ)) (t : ℕ) (ht : RematRounding.capacity M y = t)
    (i₀ : Fin N) (hmax : RematRounding.fraction y i₀ = (1 - ell * (2 * t - 1)) / 2) :
    RematGeneralResidual.loss (fun r => ell * (r : ℝ) ^ 2) M y (RematRounding.rounded y {i₀}) =
      RematGeneralResidual.loss (fun r => ell * (r : ℝ) ^ 2) M y (RematRounding.base y) := by
  have h := pair_loss_difference (fun r => ell * (r : ℝ) ^ 2) M y hs t ht i₀ _ hmax
  push_cast at h
  nlinarith

theorem rounded_perturbation_excludes (ell eps : ℝ) (hell : 0 < ell) (heps : 0 ≤ eps)
    (M : ℤ) (hM : 0 < M) (y : Fin N → ℝ) (hs : ∑ i, y i = (M : ℝ))
    (t T : ℕ) (ht : 0 < t) (htT : t ≤ T) (htM : (t : ℤ) ≤ M)
    (hcap : RematRounding.capacity M y = t) (hsmall : eps < ell / (T : ℝ) ^ 2)
    (hf : ∀ i, RematRounding.fraction y i ≤ (1 - ell * (2 * t - 1)) / 2)
    (i₀ : Fin N) (hmax : RematRounding.fraction y i₀ = (1 - ell * (2 * t - 1)) / 2)
    (h : ℝ → ℝ) (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h x| ≤ eps * x ^ 2 / 2)
    (E : Finset (Fin N)) (hE : 2 ≤ E.card) (hEt : E.card ≤ t) :
    let G := RematGeneralResidual.sampledPenalty (fun s => ell * s ^ 2 + h s) M
    RematGeneralResidual.loss G M y (RematRounding.base y) + ell <
      RematGeneralResidual.loss G M y (RematRounding.rounded y E) ∧
    RematGeneralResidual.loss G M y (RematRounding.rounded y {i₀}) + ell <
      RematGeneralResidual.loss G M y (RematRounding.rounded y E) := by
  have hb m (hm : m ≤ t) : |(M : ℝ) ^ 2 * h (((t : ℝ) - m) / M)| ≤ eps * (T : ℝ) ^ 2 / 2 := by
    apply normalized_error_bound h eps M T _ heps (by exact_mod_cast hM)
    · exact sub_nonneg.mpr (by exact_mod_cast hm)
    · have htt : (t : ℝ) ≤ T := by exact_mod_cast htT
      have hmp : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · have htm : (t : ℝ) ≤ M := by exact_mod_cast htM
      have hmp : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · exact hbound
  have hbudget := (epsilon_budget ell eps T (by omega) heps hsmall).1
  have hc := RematRounding.capacity_cast M y hs
  rw [hcap] at hc
  dsimp
  simp only [loss_sampled_split ell h M hM, RematRounding.rounded_slack M y hs,
    hcap, ← hc, Int.cast_sub, Int.cast_natCast, Finset.card_singleton, Nat.cast_one, Int.cast_one]
  have hb₀ := hb 0 (by omega)
  have hb₁ := hb 1 (by omega)
  simp only [Nat.cast_zero, sub_zero, Nat.cast_one] at hb₀ hb₁
  exact two_candidate_perturbation_gap _ _ _ _ _ _ ell (eps * (T : ℝ) ^ 2 / 2)
    (quadratic_pair_tie ell M y hs t hcap i₀ hmax)
    (rounded_quadratic_gap ell hell M y hs t hcap hf E hE hEt)
    (by linarith) hb₀ hb₁ (hb E.card hEt)

theorem all_minimizer_indices_two (ell eps : ℝ) (hell : 0 < ell) (heps : 0 ≤ eps)
    (M : ℤ) (hM : 0 < M) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hs : ∑ i, y i = (M : ℝ)) (t T : ℕ) (ht : 0 < t) (htT : t ≤ T)
    (htM : (t : ℤ) ≤ M) (hcap : RematRounding.capacity M y = t)
    (hsmall : eps < ell / (T : ℝ) ^ 2)
    (hf : ∀ i, RematRounding.fraction y i ≤ (1 - ell * (2 * t - 1)) / 2)
    (i₀ : Fin N) (hmax : RematRounding.fraction y i₀ = (1 - ell * (2 * t - 1)) / 2)
    (h : ℝ → ℝ) (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h x| ≤ eps * x ^ 2 / 2)
    (hmono : MonotoneOn (fun s => ell * s ^ 2 + h s) (Set.Icc 0 1))
    (n : Fin N → ℤ)
    (hn : RematGeneralResidual.isMinimum
      (RematGeneralResidual.sampledPenalty (fun s => ell * s ^ 2 + h s) M) M y n) :
    index y n = 0 ∨ index y n = 1 := by
  let G := RematGeneralResidual.sampledPenalty (fun s => ell * s ^ 2 + h s) M
  have hG := RematGeneralResidual.sampledPenalty_monotone _ hmono M hM
  have hrep := RematGeneralResidual.minimum_rounded_representation G M hG y hy hs n hn
  let E := RematRounding.selected y n
  have hEt : E.card ≤ t := by
    rw [← hcap]
    apply (RematRounding.rounded_feasible_iff M y hy hs E).mp
    rw [← hrep]
    exact hn.1
  have hind : index y n = E.card := by
    rw [hrep]
    exact index_rounded y E
  by_cases hE : 2 ≤ E.card
  · have hg := (rounded_perturbation_excludes ell eps hell heps M hM y hs t T ht htT htM
      hcap hsmall hf i₀ hmax h hbound E hE hEt).1
    have hz := hn.2 (RematRounding.base y) (base_feasible M y hy hs)
    rw [hrep] at hz
    change RematGeneralResidual.loss G M y (RematRounding.base y) + ell <
      RematGeneralResidual.loss G M y (RematRounding.rounded y E) at hg
    change RematGeneralResidual.loss G M y (RematRounding.rounded y E) ≤ _ at hz
    exfalso
    linarith
  · omega

theorem two_index_observation_iff (G : ℤ → ℝ) (M : ℤ) (hM : 0 ≤ M)
    (y : Fin N → ℝ) (v₀ v₁ : Fin N → ℤ)
    (hv₀ : RematGeneral.feasible M v₀) (hv₁ : RematGeneral.feasible M v₁)
    (hi₀ : index y v₀ = 0) (hi₁ : index y v₁ = 1)
    (hfit₀ : ∀ n, index y n = 0 → RematGeneralResidual.loss G M y v₀ ≤ RematGeneralResidual.loss G M y n)
    (hfit₁ : ∀ n, index y n = 1 → RematGeneralResidual.loss G M y v₁ ≤ RematGeneralResidual.loss G M y n)
    (honly : ∀ n, RematGeneralResidual.isMinimum G M y n → index y n = 0 ∨ index y n = 1) :
    (occurs G M y 0 ↔ RematGeneralResidual.loss G M y v₀ ≤ RematGeneralResidual.loss G M y v₁) ∧
    (occurs G M y 1 ↔ RematGeneralResidual.loss G M y v₁ ≤ RematGeneralResidual.loss G M y v₀) ∧
    (exactIndex G M y 0 ↔ RematGeneralResidual.loss G M y v₀ < RematGeneralResidual.loss G M y v₁) ∧
    (exactIndex G M y 1 ↔ RematGeneralResidual.loss G M y v₁ < RematGeneralResidual.loss G M y v₀) := by
  have hzero : occurs G M y 0 ↔ RematGeneralResidual.loss G M y v₀ ≤ RematGeneralResidual.loss G M y v₁ := by
    constructor
    · intro hobs
      exact (fixed_slice_global G M y 0 v₀ hv₀ hfit₀ hobs).2 v₁ hv₁
    · intro hle
      obtain ⟨n, hn⟩ := RematGeneralResidual.minimum_exists G M hM y
      rcases honly n hn with h0 | h1
      · exact ⟨n, hn, h0⟩
      · have hmin := fixed_slice_global G M y 1 v₁ hv₁ hfit₁ ⟨n, hn, h1⟩
        exact ⟨v₀, ⟨hv₀, fun z hz => hle.trans (hmin.2 z hz)⟩, hi₀⟩
  have hone : occurs G M y 1 ↔ RematGeneralResidual.loss G M y v₁ ≤ RematGeneralResidual.loss G M y v₀ := by
    constructor
    · intro hobs
      exact (fixed_slice_global G M y 1 v₁ hv₁ hfit₁ hobs).2 v₀ hv₀
    · intro hle
      obtain ⟨n, hn⟩ := RematGeneralResidual.minimum_exists G M hM y
      rcases honly n hn with h0 | h1
      · have hmin := fixed_slice_global G M y 0 v₀ hv₀ hfit₀ ⟨n, hn, h0⟩
        exact ⟨v₁, ⟨hv₁, fun z hz => hle.trans (hmin.2 z hz)⟩, hi₁⟩
      · exact ⟨n, hn, h1⟩
  refine ⟨hzero, hone, ?_, ?_⟩
  · constructor
    · exact strict_slice_comparison G M y 0 v₀ v₁ hv₀ hv₁ (by omega) hfit₀
    · intro hlt
      refine ⟨hzero.mpr hlt.le, ?_⟩
      intro n hn
      rcases honly n hn with h0 | h1
      · exact h0
      · have hf := hfit₁ n h1
        have hc := hn.2 v₀ hv₀
        exfalso
        linarith
  · constructor
    · exact strict_slice_comparison G M y 1 v₁ v₀ hv₁ hv₀ (by omega) hfit₁
    · intro hlt
      refine ⟨hone.mpr hlt.le, ?_⟩
      intro n hn
      rcases honly n hn with h0 | h1
      · have hf := hfit₀ n h0
        have hc := hn.2 v₁ hv₁
        exfalso
        linarith
      · exact h1

theorem c2_all_vector_transfer (ell eps : ℝ) (hell : 0 < ell) (heps : 0 ≤ eps)
    (M : ℤ) (hM : 0 < M) (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hs : ∑ i, y i = (M : ℝ)) (t T : ℕ) (ht : 0 < t) (htT : t ≤ T)
    (htM : (t : ℤ) ≤ M) (hcap : RematRounding.capacity M y = t)
    (hsmall : eps < ell / (T : ℝ) ^ 2)
    (hf : ∀ i, RematRounding.fraction y i ≤ (1 - ell * (2 * t - 1)) / 2)
    (i₀ : Fin N) (hmax : RematRounding.fraction y i₀ = (1 - ell * (2 * t - 1)) / 2)
    (h h₁ h₂ : ℝ → ℝ)
    (hd₀ : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h (h₁ x) x)
    (hd₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h₁ (h₂ x) x)
    (hzero : h 0 = 0) (hone : h₁ 0 = 0)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h₂ x| ≤ eps) :
    let G := RematGeneralResidual.sampledPenalty (fun s => ell * s ^ 2 + h s) M
    (∀ n, RematGeneralResidual.isMinimum G M y n → index y n = 0 ∨ index y n = 1) ∧
    (occurs G M y 0 ↔ h ((t : ℝ) / M) ≤ h (((t : ℝ) - 1) / M)) ∧
    (occurs G M y 1 ↔ h (((t : ℝ) - 1) / M) ≤ h ((t : ℝ) / M)) ∧
    (exactIndex G M y 0 ↔ h ((t : ℝ) / M) < h (((t : ℝ) - 1) / M)) ∧
    (exactIndex G M y 1 ↔ h (((t : ℝ) - 1) / M) < h ((t : ℝ) / M)) ∧
    ((occurs G M y 0 ∧ occurs G M y 1) ↔ h ((t : ℝ) / M) = h (((t : ℝ) - 1) / M)) := by
  let G := RematGeneralResidual.sampledPenalty (fun s => ell * s ^ 2 + h s) M
  have hepsell := (epsilon_budget ell eps T (by omega) heps hsmall).2.le
  have hb := second_derivative_quadratic_bound h h₁ h₂ eps hd₀ hd₁ hzero hone hbound
  have hmono := perturbed_penalty_monotone ell eps hell.le hepsell h h₁ h₂ hd₀ hd₁ hone hbound
  have honly := all_minimizer_indices_two ell eps hell heps M hM y hy hs t T ht htT htM hcap
    hsmall hf i₀ hmax h hb hmono
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hq : (1 - ell * (2 * t - 1)) / 2 ≤ 1 / 2 := by
    have hp : 0 ≤ ell * (2 * t - 1) := mul_nonneg hell.le (by linarith)
    linarith
  have hv₀ := base_feasible M y hy hs
  have hv₁ := one_feasible M y hy hs i₀ (by omega)
  have hi₁ : index y (RematRounding.rounded y {i₀}) = 1 := by simpa using index_rounded y {i₀}
  have hclass := two_index_observation_iff G M hM.le y _ _ hv₀ hv₁ (index_base y) hi₁
    (fixed_index_zero_loss G M y (fun i => (hf i).trans hq))
    (fixed_index_one_loss G M y i₀ _ hq hf hmax) honly
  have hdiff := sampled_pair_difference ell h M hM y hs t hcap i₀ hmax
  change RematGeneralResidual.loss G M y (RematRounding.rounded y {i₀}) -
    RematGeneralResidual.loss G M y (RematRounding.base y) = _ at hdiff
  have hp : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hM)
  have hz : occurs G M y 0 ↔ h ((t : ℝ) / M) ≤ h (((t : ℝ) - 1) / M) := by
    rw [hclass.1]
    constructor <;> intro hc <;> nlinarith
  have ho : occurs G M y 1 ↔ h (((t : ℝ) - 1) / M) ≤ h ((t : ℝ) / M) := by
    rw [hclass.2.1]
    constructor <;> intro hc <;> nlinarith
  refine ⟨honly, hz, ho, ?_, ?_, ?_⟩
  · rw [hclass.2.2.1]
    constructor <;> intro hc <;> nlinarith
  · rw [hclass.2.2.2]
    constructor <;> intro hc <;> nlinarith
  · rw [hz, ho]
    exact ⟨fun hle => le_antisymm hle.1 hle.2, fun he => ⟨he.le, he.ge⟩⟩

theorem arbitrary_loss_observation_necessity (ell : ℝ) (φ : ℝ → ℝ) (M : ℤ) (hM : 0 < M)
    (y : Fin N → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = (M : ℝ))
    (t : ℕ) (ht : 0 < t) (hcap : RematRounding.capacity M y = t) (i₀ : Fin N)
    (hq : (1 - ell * (2 * t - 1)) / 2 ≤ 1 / 2)
    (hf : ∀ i, RematRounding.fraction y i ≤ (1 - ell * (2 * t - 1)) / 2)
    (hmax : RematRounding.fraction y i₀ = (1 - ell * (2 * t - 1)) / 2) :
    let G := RematGeneralResidual.sampledPenalty φ M
    let h := fun s => φ s - ell * s ^ 2
    (occurs G M y 0 → h ((t : ℝ) / M) ≤ h (((t : ℝ) - 1) / M)) ∧
    (occurs G M y 1 → h (((t : ℝ) - 1) / M) ≤ h ((t : ℝ) / M)) ∧
    (exactIndex G M y 0 → h ((t : ℝ) / M) < h (((t : ℝ) - 1) / M)) ∧
    (exactIndex G M y 1 → h (((t : ℝ) - 1) / M) < h ((t : ℝ) / M)) := by
  have h := all_vector_observation_necessity ell (fun s => φ s - ell * s ^ 2) M hM y hy hs
    t ht hcap i₀ hq hf hmax
  have he : (fun s => ell * s ^ 2 + (φ s - ell * s ^ 2)) = φ := by
    funext s
    ring
  dsimp at h ⊢
  simpa only [he] using h

theorem continuous_residual_difference (ell : ℝ) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    Continuous (fun s => φ s - ell * s ^ 2) := by
  exact hφ.sub (continuous_const.mul (continuous_id.pow 2))

def gridOccurs (φ : ℝ → ℝ) (M : ℤ) (a : Fin N → ℝ) (j : ℤ) : Prop :=
  ∃ n, RematGeneralResidual.gridMinimum φ M a (RematGrid.point M n) ∧
    index (fun i => (M : ℝ) * a i) n = j

def gridExactIndex (φ : ℝ → ℝ) (M : ℤ) (a : Fin N → ℝ) (j : ℤ) : Prop :=
  gridOccurs φ M a j ∧ ∀ n, RematGeneralResidual.gridMinimum φ M a (RematGrid.point M n) →
    index (fun i => (M : ℝ) * a i) n = j

theorem grid_observation_iff (φ : ℝ → ℝ) (M : ℤ) (hM : 0 < M)
    (a : Fin N → ℝ) (j : ℤ) :
    (gridOccurs φ M a j ↔ occurs (RematGeneralResidual.sampledPenalty φ M) M (fun i => (M : ℝ) * a i) j) ∧
    (gridExactIndex φ M a j ↔ exactIndex (RematGeneralResidual.sampledPenalty φ M) M (fun i => (M : ℝ) * a i) j) := by
  simp [gridOccurs, gridExactIndex, occurs, exactIndex,
    RematGeneralResidual.grid_minimum_point_iff φ M hM]

theorem grid_minimum_has_integer_representative (φ : ℝ → ℝ) (M : ℤ) (hM : 0 < M)
    (a d : Fin N → ℝ) (hd : RematGeneralResidual.gridMinimum φ M a d) :
    ∃ n, d = RematGrid.point M n ∧
      RematGeneralResidual.isMinimum (RematGeneralResidual.sampledPenalty φ M) M
        (fun i => (M : ℝ) * a i) n := by
  obtain ⟨n, he⟩ := hd.1.2.2
  refine ⟨n, he, ?_⟩
  apply (RematGeneralResidual.grid_minimum_point_iff φ M hM a n).mp
  rwa [← he]

theorem cubic_three_coordinate_examples (c : ℝ) (hc : |c| ≤ 1 / 100) :
    let y : Fin 3 → ℝ := fun _ => 1 / 3
    let G := RematGeneralResidual.sampledPenalty (fun s => (1 / 3 : ℝ) * s ^ 2 + c * s ^ 3) 1
    (exactIndex G 1 y 0 ↔ c < 0) ∧ (exactIndex G 1 y 1 ↔ 0 < c) ∧
      ((occurs G 1 y 0 ∧ occurs G 1 y 1) ↔ c = 0) := by
  let y : Fin 3 → ℝ := fun _ => 1 / 3
  have hy : ∀ i, 0 ≤ y i := by intro i; norm_num [y]
  have hs : ∑ i, y i = ((1 : ℤ) : ℝ) := by norm_num [y]
  have hcap : RematRounding.capacity 1 y = 1 := by
    norm_num [RematRounding.capacity, RematRounding.base, y]
  have hf : ∀ i, RematRounding.fraction y i ≤ (1 - (1 / 3 : ℝ) * (2 * (1 : ℕ) - 1)) / 2 := by
    intro i
    norm_num [RematRounding.fraction, RematRounding.base, y]
  have hmax : RematRounding.fraction y (0 : Fin 3) = (1 - (1 / 3 : ℝ) * (2 * (1 : ℕ) - 1)) / 2 := by
    norm_num [RematRounding.fraction, RematRounding.base, y]
  have hd₀ : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => c * s ^ 3) (3 * c * x ^ 2) x := by
    intro x hx
    convert! ((hasDerivAt_id x).pow 3).const_mul c using 1; simp; ring
  have hd₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => 3 * c * s ^ 2) (6 * c * x) x := by
    intro x hx
    convert! ((hasDerivAt_id x).pow 2).const_mul (3 * c) using 1; simp; ring
  have hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |6 * c * x| ≤ 3 / 50 := by
    intro x hx
    have hp := mul_le_mul hc hx.2 hx.1 (by norm_num : (0 : ℝ) ≤ 1 / 100)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6), abs_of_nonneg hx.1]
    nlinarith
  have h := c2_all_vector_transfer (1 / 3) (3 / 50) (by norm_num) (by norm_num)
    1 (by norm_num) y hy hs 1 1 (by norm_num) (by norm_num) (by norm_num) hcap
    (by norm_num) hf 0 hmax (fun s => c * s ^ 3) (fun s => 3 * c * s ^ 2) (fun s => 6 * c * s)
    hd₀ hd₁ (by norm_num) (by norm_num) hb
  dsimp at h ⊢
  norm_num at h ⊢
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem perturbed_quantitative_convexity (ell eps : ℝ) (heps : eps ≤ ell)
    (h h₁ h₂ : ℝ → ℝ)
    (hd₀ : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h (h₁ x) x)
    (hd₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h₁ (h₂ x) x)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h₂ x| ≤ eps) :
    ConvexOn ℝ (Set.Icc 0 1) (fun s => (ell * s ^ 2 + h s) - ell / 2 * s ^ 2) := by
  have hd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => ell / 2 * s ^ 2 + h s) (ell * x + h₁ x) x := by
    intro x hx
    convert! (((hasDerivAt_id x).pow 2).const_mul (ell / 2)).add (hd₀ x hx) using 1; simp; ring
  have hdd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => ell * s + h₁ s) (ell + h₂ x) x := by
    intro x hx
    convert! ((hasDerivAt_id x).const_mul ell).add (hd₁ x hx) using 1; simp
  have hconv : ConvexOn ℝ (Set.Icc 0 1) (fun s => ell / 2 * s ^ 2 + h s) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0 : ℝ) 1)
      (f' := fun s => ell * s + h₁ s) (f'' := fun s => ell + h₂ s)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt
    · exact fun x hx => (hdd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      have hb := (abs_le.mp (hbound x (interior_subset hx))).1
      linarith
  convert hconv using 1
  funext s
  ring

theorem scalar_sample_classification (ell eps M : ℝ) (hell : 0 < ell)
    (heps : 0 ≤ eps) (hM : 0 < M) (t T : ℕ) (ht : 0 < t) (htT : t ≤ T)
    (htM : (t : ℝ) ≤ M) (hsmall : eps < ell / (T : ℝ) ^ 2)
    (f : ℕ → ℝ) (hf : ∀ j, j < t → f j ≤ (1 - ell * (2 * t - 1)) / 2)
    (hf₀ : f 0 = (1 - ell * (2 * t - 1)) / 2)
    (h : ℝ → ℝ) (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h x| ≤ eps * x ^ 2 / 2)
    (j : ℕ) (hjt : j ≤ t) :
    let P := fun m => RematDilationSynthesis.scalarCost ell t f m + M ^ 2 * h (((t : ℝ) - m) / M)
    (∀ m, m ≤ t → P j ≤ P m) ↔
      (j = 0 ∧ h ((t : ℝ) / M) ≤ h (((t : ℝ) - 1) / M)) ∨
      (j = 1 ∧ h (((t : ℝ) - 1) / M) ≤ h ((t : ℝ) / M)) := by
  let P := fun m => RematDilationSynthesis.scalarCost ell t f m + M ^ 2 * h (((t : ℝ) - m) / M)
  have hex m hm hmt := scalar_perturbation_excludes ell eps M hell heps hM t T ht htT htM
    hsmall f hf hf₀ h hbound m hm hmt
  have htie := RematDilationSynthesis.scalar_first_tie ell t f hf₀
  have hp : 0 < M ^ 2 := sq_pos_of_pos hM
  have h01 : P 0 ≤ P 1 ↔ h ((t : ℝ) / M) ≤ h (((t : ℝ) - 1) / M) := by
    dsimp [P]
    simp only [Nat.cast_zero, Nat.cast_one, sub_zero, htie]
    constructor <;> intro hc <;> nlinarith
  have h10 : P 1 ≤ P 0 ↔ h (((t : ℝ) - 1) / M) ≤ h ((t : ℝ) / M) := by
    dsimp [P]
    simp only [Nat.cast_zero, Nat.cast_one, sub_zero, htie]
    constructor <;> intro hc <;> nlinarith
  have hclass := two_scalar_minima_iff P t ht (fun m hm hmt =>
    ⟨by have hh := (hex m hm hmt).1; change P 0 + ell < P m at hh; linarith,
     by have hh := (hex m hm hmt).2; change P 1 + ell < P m at hh; linarith⟩) j hjt
  rwa [h01, h10] at hclass

theorem nonvacuous_three_regimes :
    let y : Fin 3 → ℝ := fun _ => 1 / 3
    (∃ φ : ℝ → ℝ, exactIndex (RematGeneralResidual.sampledPenalty φ 1) 1 y 0) ∧
    (∃ φ : ℝ → ℝ, exactIndex (RematGeneralResidual.sampledPenalty φ 1) 1 y 1) ∧
    (∃ φ : ℝ → ℝ, occurs (RematGeneralResidual.sampledPenalty φ 1) 1 y 0 ∧
      occurs (RematGeneralResidual.sampledPenalty φ 1) 1 y 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨_, (cubic_three_coordinate_examples (-1 / 100) (by norm_num)).1.mpr (by norm_num)⟩
  · exact ⟨_, (cubic_three_coordinate_examples (1 / 100) (by norm_num)).2.1.mpr (by norm_num)⟩
  · exact ⟨_, (cubic_three_coordinate_examples 0 (by norm_num)).2.2.mpr rfl⟩

end

end RematTransfer

#print axioms RematTransfer.index_base
#print axioms RematTransfer.index_rounded
#print axioms RematTransfer.fixed_sum_shift_certificate
#print axioms RematTransfer.floor_fitting_minimum
#print axioms RematTransfer.one_fitting_minimum
#print axioms RematTransfer.fixed_index_zero_loss
#print axioms RematTransfer.fixed_index_one_loss
#print axioms RematTransfer.fixed_slice_global
#print axioms RematTransfer.strict_slice_comparison
#print axioms RematTransfer.minimum_index_bounds
#print axioms RematTransfer.base_feasible
#print axioms RematTransfer.one_feasible
#print axioms RematTransfer.pair_loss_difference
#print axioms RematTransfer.sampled_quadratic_split
#print axioms RematTransfer.sampled_pair_difference
#print axioms RematTransfer.all_vector_observation_necessity
#print axioms RematTransfer.monotone_from_derivatives
#print axioms RematTransfer.first_derivative_bound
#print axioms RematTransfer.second_derivative_quadratic_bound
#print axioms RematTransfer.perturbed_penalty_monotone
#print axioms RematTransfer.perturbed_curvature_bound
#print axioms RematTransfer.normalized_error_bound
#print axioms RematTransfer.epsilon_budget
#print axioms RematTransfer.two_candidate_perturbation_gap
#print axioms RematTransfer.scalar_perturbation_excludes
#print axioms RematTransfer.two_scalar_minima_iff
#print axioms RematTransfer.loss_sampled_split
#print axioms RematTransfer.rounded_quadratic_gap
#print axioms RematTransfer.quadratic_pair_tie
#print axioms RematTransfer.rounded_perturbation_excludes
#print axioms RematTransfer.all_minimizer_indices_two
#print axioms RematTransfer.two_index_observation_iff
#print axioms RematTransfer.c2_all_vector_transfer
#print axioms RematTransfer.arbitrary_loss_observation_necessity
#print axioms RematTransfer.continuous_residual_difference
#print axioms RematTransfer.grid_observation_iff
#print axioms RematTransfer.grid_minimum_has_integer_representative
#print axioms RematTransfer.cubic_three_coordinate_examples
#print axioms RematTransfer.perturbed_quantitative_convexity
#print axioms RematTransfer.scalar_sample_classification
#print axioms RematTransfer.nonvacuous_three_regimes
end

section
set_option autoImplicit true
set_option autoImplicit false

open scoped BigOperators ContDiff

namespace RematUniformRepresentation

open RematUniformTargets

noncomputable section

def RealTarget (D K H t r : ℕ) (a : Fin (dimension K t) → ℚ) : Prop :=
  (∀ i, 0 < (a i : ℝ)) ∧ (∑ i, (a i : ℝ) = 1) ∧
  (∀ m : ℕ, m ≡ r [MOD D * denominator K] → ∀ i,
    Int.fract (((H * m : ℕ) : ℝ) * (a i : ℝ)) = ((profile K t i.val : ℚ) : ℝ)) ∧
  (∀ m : ℕ, m ≡ r [MOD D * denominator K] →
    ∑ i, Int.fract (((H * m : ℕ) : ℝ) * (a i : ℝ)) = t)

theorem real_target_exists {D K H t r : ℕ} (h : TargetAt D K H t r) :
    ∃ a : Fin (dimension K t) → ℚ, RealTarget D K H t r a :=
  target_real_coordinates h

theorem real_target_scaled_data {D K H T t r : ℕ} (hH : 0 < H) (hK : 2 * T ≤ K)
    (ht : 0 < t) (htT : t ≤ T) (a : Fin (dimension K t) → ℚ)
    (ha : RealTarget D K H t r a) (m : ℕ) (htm : t ≤ m)
    (hmr : m ≡ r [MOD D * denominator K]) :
    let M : ℤ := (H * m : ℕ)
    let y : Fin (dimension K t) → ℝ := fun i => (M : ℝ) * (a i : ℝ)
    0 < M ∧ (t : ℤ) ≤ M ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, y i = (M : ℝ)) ∧
      RematRounding.capacity M y = t ∧
      (∀ i, RematRounding.fraction y i ≤ (1 - (1 / (denominator K : ℝ)) * (2 * t - 1)) / 2) ∧
      ∃ i₀, RematRounding.fraction y i₀ = (1 - (1 / (denominator K : ℝ)) * (2 * t - 1)) / 2 := by
  dsimp
  have hm : 0 < m := ht.trans_le htm
  have hM : 0 < H * m := Nat.mul_pos hH hm
  have htM : t ≤ H * m := htm.trans (by nlinarith)
  have hf (i : Fin (dimension K t)) :
      RematRounding.fraction (fun i => (((H * m : ℕ) : ℤ) : ℝ) * (a i : ℝ)) i = (profile K t i.val : ℝ) := by
    change Int.fract (((((H * m : ℕ) : ℤ) : ℝ)) * (a i : ℝ)) = _
    simpa only [Int.cast_natCast] using ha.2.2.1 m hmr i
  have hs : (∑ i, (((H * m : ℕ) : ℤ) : ℝ) * (a i : ℝ)) = (((H * m : ℕ) : ℤ) : ℝ) := by
    rw [← Finset.mul_sum, ha.2.1, mul_one]
  have hcap : RematRounding.capacity (H * m : ℕ) (fun i => (((H * m : ℕ) : ℤ) : ℝ) * (a i : ℝ)) = t := by
    have hh := RematRounding.fraction_sum ((H * m : ℕ) : ℤ) (fun i => (((H * m : ℕ) : ℤ) : ℝ) * (a i : ℝ)) hs
    have hmass : (∑ i, RematRounding.fraction (fun i => (((H * m : ℕ) : ℤ) : ℝ) * (a i : ℝ)) i) = (t : ℝ) := by
      change (∑ i, Int.fract (((((H * m : ℕ) : ℤ) : ℝ)) * (a i : ℝ))) = _
      simpa only [Int.cast_natCast] using ha.2.2.2 m hmr
    rw [hmass] at hh
    exact_mod_cast hh.symm
  have hform : (threshold K t : ℝ) = (1 - (1 / (denominator K : ℝ)) * (2 * t - 1)) / 2 := by
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (threshold_bounds hK ht htT).2.2
    push_cast at hh
    exact hh
  have hp := profile_properties hK ht htT
  refine ⟨by exact_mod_cast hM, by exact_mod_cast htM, ?_, hs, hcap, ?_, ?_⟩
  · intro i
    exact mul_nonneg (by exact_mod_cast hM.le) (ha.1 i).le
  · intro i
    have hfi := hf i
    simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast] at hfi ⊢
    rw [hfi, ← hform]
    exact_mod_cast (hp.2.2.1 i.val i.isLt).2
  · have hN : 0 < dimension K t := lt_of_lt_of_le (by omega) (dimension_bounds hK ht htT).1
    refine ⟨⟨0, hN⟩, ?_⟩
    have hfi := hf ⟨0, hN⟩
    simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast] at hfi ⊢
    rw [hfi, hp.1, hform]

def Observation {N : ℕ} (forward strict : Bool) (φ : ℝ → ℝ) (M : ℤ)
    (a : Fin N → ℝ) : Prop :=
  if forward then
    (if strict then RematTransfer.gridExactIndex φ M a 0 else RematTransfer.gridOccurs φ M a 0)
  else (if strict then RematTransfer.gridExactIndex φ M a 1 else RematTransfer.gridOccurs φ M a 1)

theorem target_observation_iff {D K H T t r : ℕ} (hH : 0 < H) (hK : 2 * T ≤ K)
    (ht : 0 < t) (htT : t ≤ T) (a : Fin (dimension K t) → ℚ)
    (ha : RealTarget D K H t r a) (m : ℕ) (htm : t ≤ m)
    (hmr : m ≡ r [MOD D * denominator K])
    (eps : ℝ) (heps : 0 ≤ eps) (hsmall : eps < (1 / (denominator K : ℝ)) / (T : ℝ)^2)
    (h h₁ h₂ : ℝ → ℝ)
    (hd₀ : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h (h₁ x) x)
    (hd₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h₁ (h₂ x) x)
    (hz : h 0 = 0) (hz₁ : h₁ 0 = 0)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h₂ x| ≤ eps) (forward strict : Bool) :
    Observation forward strict (fun s => (1 / (denominator K : ℝ)) * s^2 + h s)
      ((H * m : ℕ) : ℤ) (fun i => (a i : ℝ)) ↔
    Comparison forward strict (h ((t : ℝ) / (H * m : ℕ)))
      (h (((t - 1 : ℕ) : ℝ) / (H * m : ℕ))) := by
  obtain ⟨hM, htM, hy, hs, hcap, hf, i₀, hmax⟩ := real_target_scaled_data hH hK ht htT a ha m htm hmr
  have hell : (0 : ℝ) < 1 / (denominator K : ℝ) := by apply one_div_pos.mpr; simp [denominator]; positivity
  have hh := RematTransfer.c2_all_vector_transfer (1 / (denominator K : ℝ)) eps hell heps
    ((H * m : ℕ) : ℤ) hM (fun i => (((H * m : ℕ) : ℤ) : ℝ) * (a i : ℝ)) hy hs t T ht htT htM hcap
    hsmall hf i₀ hmax h h₁ h₂ hd₀ hd₁ hz hz₁ hb
  have hg0 := RematTransfer.grid_observation_iff (fun s => (1 / (denominator K : ℝ)) * s^2 + h s)
    ((H * m : ℕ) : ℤ) hM (fun i => (a i : ℝ)) 0
  have hg1 := RematTransfer.grid_observation_iff (fun s => (1 / (denominator K : ℝ)) * s^2 + h s)
    ((H * m : ℕ) : ℤ) hM (fun i => (a i : ℝ)) 1
  have he : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ t)]; norm_num
  cases forward <;> cases strict
  · simpa only [Observation, Comparison, Bool.false_eq_true, ↓reduceIte, he, Int.cast_natCast] using hg1.1.trans hh.2.2.1
  · simpa only [Observation, Comparison, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, he, Int.cast_natCast] using hg1.2.trans hh.2.2.2.2.1
  · simpa only [Observation, Comparison, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, he, Int.cast_natCast] using hg0.1.trans hh.2.1
  · simpa only [Observation, Comparison, Bool.true_eq, ↓reduceIte, he, Int.cast_natCast] using hg0.2.trans hh.2.2.2.1

theorem target_observation_necessary {D K H T t r : ℕ} (hH : 0 < H) (hK : 2 * T ≤ K)
    (ht : 0 < t) (htT : t ≤ T) (a : Fin (dimension K t) → ℚ)
    (ha : RealTarget D K H t r a) (m : ℕ) (htm : t ≤ m)
    (hmr : m ≡ r [MOD D * denominator K]) (φ : ℝ → ℝ) (forward strict : Bool)
    (hobs : Observation forward strict φ ((H * m : ℕ) : ℤ) (fun i => (a i : ℝ))) :
    let h := fun s => φ s - (1 / (denominator K : ℝ)) * s^2
    Comparison forward strict (h ((t : ℝ) / (H * m : ℕ)))
      (h (((t - 1 : ℕ) : ℝ) / (H * m : ℕ))) := by
  obtain ⟨hM, _, hy, hs, hcap, hf, i₀, hmax⟩ := real_target_scaled_data hH hK ht htT a ha m htm hmr
  have hq : (1 - (1 / (denominator K : ℝ)) * (2 * t - 1)) / 2 ≤ 1 / 2 := by
    have hell : (0 : ℝ) ≤ 1 / (denominator K : ℝ) := by positivity
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    nlinarith [mul_nonneg hell (show (0 : ℝ) ≤ 2 * t - 1 by linarith)]
  have hh := RematTransfer.arbitrary_loss_observation_necessity (1 / (denominator K : ℝ)) φ
    ((H * m : ℕ) : ℤ) hM (fun i => (((H * m : ℕ) : ℤ) : ℝ) * (a i : ℝ)) hy hs
    t ht hcap i₀ hq hf hmax
  have hg0 := RematTransfer.grid_observation_iff φ ((H * m : ℕ) : ℤ) hM (fun i => (a i : ℝ)) 0
  have hg1 := RematTransfer.grid_observation_iff φ ((H * m : ℕ) : ℤ) hM (fun i => (a i : ℝ)) 1
  have he : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ t)]; norm_num
  cases forward <;> cases strict
  · simpa only [Comparison, Bool.false_eq_true, ↓reduceIte, he, Int.cast_natCast] using hh.2.1 (hg1.1.mp hobs)
  · simpa only [Comparison, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, he, Int.cast_natCast] using hh.2.2.2 (hg1.2.mp hobs)
  · simpa only [Comparison, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, he, Int.cast_natCast] using hh.1 (hg0.1.mp hobs)
  · simpa only [Comparison, Bool.true_eq, ↓reduceIte, he, Int.cast_natCast] using hh.2.2.1 (hg0.2.mp hobs)

theorem comparison_sub_const (forward strict : Bool) (x y c : ℝ) :
    Comparison forward strict (x - c) (y - c) ↔ Comparison forward strict x y := by
  cases forward <;> cases strict <;> simp [Comparison]

def leftEndpoint (forward : Bool) (H t m : ℕ) : ℝ :=
  if forward then (t : ℝ) / (H * m : ℕ) else ((t - 1 : ℕ) : ℝ) / (H * m : ℕ)

def rightEndpoint (forward : Bool) (H t m : ℕ) : ℝ :=
  if forward then ((t - 1 : ℕ) : ℝ) / (H * m : ℕ) else (t : ℝ) / (H * m : ℕ)

theorem comparison_oriented (forward strict : Bool) (u : ℝ → ℝ) (H t m : ℕ) :
    Comparison forward strict (u ((t : ℝ) / (H * m : ℕ))) (u (((t - 1 : ℕ) : ℝ) / (H * m : ℕ))) ↔
    if strict then u (leftEndpoint forward H t m) < u (rightEndpoint forward H t m)
    else u (leftEndpoint forward H t m) ≤ u (rightEndpoint forward H t m) := by
  cases forward <;> cases strict <;> rfl

theorem endpoints_mem_samples {H T t m : ℕ} (hH : 0 < H) (htT : t ≤ T) (htm : t ≤ m) (forward : Bool) :
    leftEndpoint forward H t m ∈ RematOrderBridge.SampleSet T ∧
    rightEndpoint forward H t m ∈ RematOrderBridge.SampleSet T := by
  have h1 := RematOrderBridge.scaled_fraction_mem_samples T H t m hH htT htm
  have h0 := RematOrderBridge.scaled_fraction_mem_samples T H (t-1) m hH
    ((Nat.sub_le t 1).trans htT) ((Nat.sub_le t 1).trans htm)
  cases forward
  · exact ⟨h0, h1⟩
  · exact ⟨h1, h0⟩

theorem realizes_scaled_smooth {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) (D H T : ℕ) (hH : 0 < H) (hT : 0 < T)
    (ht : ∀ a ∈ A, t a ≤ T) (u : ℝ → ℝ) (hu : ContinuousAt u 0) (hz : u 0 = 0)
    (hR : RealizesScaled A t r forward strict D H u) (eps : ℝ) (heps : 0 < eps) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
      (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ eps) ∧
      RealizesScaled A t r forward strict D H h := by
  let Edge (b : Bool) (x y : RematOrderBridge.Sample T) : Prop :=
    ∃ a ∈ A, ∃ m : ℕ, t a ≤ m ∧ m ≡ r a [MOD D] ∧ strict a = b ∧
      (x : ℝ) = leftEndpoint (forward a) H (t a) m ∧
      (y : ℝ) = rightEndpoint (forward a) H (t a) m
  have hw (x y : RematOrderBridge.Sample T) (hxy : Edge false x y) : u (x : ℝ) ≤ u (y : ℝ) := by
    obtain ⟨a, ha, m, htm, hmr, hs, hx, hy⟩ := hxy
    have hh := (comparison_oriented (forward a) (strict a) u H (t a) m).mp (hR a ha m htm hmr)
    simpa only [hs, Bool.false_eq_true, ↓reduceIte, hx, hy] using hh
  have he (x y : RematOrderBridge.Sample T) (hxy : Edge true x y) : u (x : ℝ) < u (y : ℝ) := by
    obtain ⟨a, ha, m, htm, hmr, hs, hx, hy⟩ := hxy
    have hh := (comparison_oriented (forward a) (strict a) u H (t a) m).mp (hR a ha m htm hmr)
    simpa only [hs, Bool.true_eq, ↓reduceIte, hx, hy] using hh
  obtain ⟨h, hsm, hzero, hj, hb, hweak, hstrict⟩ :=
    RematOrderBridge.sample_ambient_relations_smooth T hT (Edge false) (Edge true) u hu hz hw he eps heps
  refine ⟨h, hsm, hzero, hj, hb, ?_⟩
  intro a ha m htm hmr
  have hmem := endpoints_mem_samples hH (ht a ha) htm (forward a)
  let x : RematOrderBridge.Sample T := ⟨leftEndpoint (forward a) H (t a) m, hmem.1⟩
  let y : RematOrderBridge.Sample T := ⟨rightEndpoint (forward a) H (t a) m, hmem.2⟩
  apply (comparison_oriented (forward a) (strict a) h H (t a) m).mpr
  cases hs : strict a
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hweak x y ⟨a, ha, m, htm, hmr, hs, rfl, rfl⟩
  · simp only [↓reduceIte]
    exact hstrict x y ⟨a, ha, m, htm, hmr, hs, rfl, rfl⟩

theorem smooth_derivative_data (h : ℝ → ℝ) (hsm : ContDiff ℝ ∞ h) :
    (∀ x : ℝ, HasDerivAt h (iteratedDeriv 1 h x) x) ∧
    ∀ x : ℝ, HasDerivAt (iteratedDeriv 1 h) (iteratedDeriv 2 h x) x := by
  constructor
  · intro x
    have hh := (hsm.differentiable_iteratedDeriv 0 (by simp)) x
    simpa only [iteratedDeriv_zero, iteratedDeriv_succ] using hh.hasDerivAt
  · intro x
    have hh := (hsm.differentiable_iteratedDeriv 1 (by simp)) x
    simpa only [show 2 = 1 + 1 by rfl, iteratedDeriv_succ] using hh.hasDerivAt


def FamilyObservations {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) (D K H : ℕ)
    (a : ∀ e, Fin (dimension K (t e)) → ℚ) (φ : ℝ → ℝ) : Prop :=
  ∀ e ∈ A, ∀ m : ℕ, t e ≤ m → m ≡ r e [MOD D * denominator K] →
    Observation (forward e) (strict e) φ ((H * m : ℕ) : ℤ) (fun i => (a e i : ℝ))

def SmoothFit {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) (D K H : ℕ)
    (a : ∀ e, Fin (dimension K (t e)) → ℚ) (eps : ℝ) : Prop :=
  ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
    (∀ k, iteratedDeriv k h 0 = 0) ∧
    (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ eps / 2) ∧
    MonotoneOn (fun s => (1 / (denominator K : ℝ)) * s^2 + h s) (Set.Icc 0 1) ∧
    ConvexOn ℝ (Set.Icc 0 1)
      (fun s => ((1 / (denominator K : ℝ)) * s^2 + h s) - (1 / (denominator K : ℝ)) / 2 * s^2) ∧
    FamilyObservations A t r forward strict D K H a
      (fun s => (1 / (denominator K : ℝ)) * s^2 + h s)

theorem sample_in_unit_interval {H t m : ℕ} (hH : 0 < H) (ht : 0 < t) (htm : t ≤ m) :
    (t : ℝ) / (H * m : ℕ) ∈ Set.Icc (0 : ℝ) 1 ∧
    ((t - 1 : ℕ) : ℝ) / (H * m : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hM : (0 : ℝ) < (H * m : ℕ) := by exact_mod_cast Nat.mul_pos hH (ht.trans_le htm)
  have htM : t ≤ H * m := htm.trans (by nlinarith)
  constructor
  · exact ⟨by positivity, (div_le_one₀ hM).mpr (by exact_mod_cast htM)⟩
  · exact ⟨by positivity, (div_le_one₀ hM).mpr (by exact_mod_cast (Nat.sub_le t 1).trans htM)⟩

theorem family_observations_necessary {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) {D K H T : ℕ} (hH : 0 < H) (hK : 2 * T ≤ K)
    (ht : ∀ e ∈ A, 0 < t e ∧ t e ≤ T)
    (a : ∀ e, Fin (dimension K (t e)) → ℚ)
    (ha : ∀ e ∈ A, RealTarget D K H (t e) (r e) (a e))
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc 0 1))
    (ho : FamilyObservations A t r forward strict D K H a φ) :
    ∃ u : ℝ → ℝ, ContinuousAt u 0 ∧ u 0 = 0 ∧
      RealizesScaled A t r forward strict (D * denominator K) H u := by
  let clamp : ℝ → ℝ := fun x => max 0 (min 1 x)
  have hc : Continuous clamp := continuous_const.max (continuous_const.min continuous_id)
  have hmem (x : ℝ) : clamp x ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have he (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : clamp x = x := by
    dsimp [clamp]
    rw [min_eq_right hx.2, max_eq_right hx.1]
  have hcont : Continuous (fun x => φ (clamp x)) := hφ.comp_continuous hc hmem
  let u : ℝ → ℝ := fun x => φ (clamp x) - (1 / (denominator K : ℝ)) * x^2 - φ 0
  refine ⟨u, ((hcont.continuousAt.sub (continuousAt_const.mul (continuousAt_id.pow 2))).sub continuousAt_const), ?_, ?_⟩
  · simp [u, clamp]
  · intro e heA m htm hmr
    have hh := target_observation_necessary hH hK (ht e heA).1 (ht e heA).2
      (a e) (ha e heA) m htm hmr φ (forward e) (strict e) (ho e heA m htm hmr)
    have hx := sample_in_unit_interval hH (ht e heA).1 htm
    change Comparison _ _ (_ - φ 0) (_ - φ 0)
    rw [he _ hx.1, he _ hx.2, comparison_sub_const]
    exact hh

theorem family_smooth_fit {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) {D K H T : ℕ} (hH : 0 < H) (hT : 0 < T) (hK : 2 * T ≤ K)
    (ht : ∀ e ∈ A, 0 < t e ∧ t e ≤ T)
    (a : ∀ e, Fin (dimension K (t e)) → ℚ)
    (ha : ∀ e ∈ A, RealTarget D K H (t e) (r e) (a e))
    (u : ℝ → ℝ) (hu : ContinuousAt u 0) (hz : u 0 = 0)
    (hR : RealizesScaled A t r forward strict (D * denominator K) H u)
    (eps : ℝ) (heps : 0 < eps) : SmoothFit A t r forward strict D K H a eps := by
  let ell : ℝ := 1 / (denominator K : ℝ)
  have hell : 0 < ell := by dsimp [ell]; apply one_div_pos.mpr; simp [denominator]; positivity
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ (T : ℝ)^2 := by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  let b : ℝ := min (eps / 2) (ell / (2 * (T : ℝ)^2))
  have hbpos : 0 < b := lt_min (by positivity) (by positivity)
  have hbsmall : b < ell / (T : ℝ)^2 := by
    have hh := min_le_right (eps / 2) (ell / (2 * (T : ℝ)^2))
    have hp : 0 < ell / (T : ℝ)^2 := by positivity
    have hid : ell / (2 * (T : ℝ)^2) = (ell / (T : ℝ)^2) / 2 := by ring
    dsimp [b]
    rw [hid] at hh ⊢
    linarith
  have hbell : b ≤ ell := hbsmall.le.trans ((div_le_self hell.le hT1))
  obtain ⟨h, hsm, hzero, hj, hb, hr⟩ := realizes_scaled_smooth A t r forward strict
    (D * denominator K) H T hH hT (fun e he => (ht e he).2) u hu hz hR b hbpos
  have hd := smooth_derivative_data h hsm
  have hd0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h (iteratedDeriv 1 h x) x := fun x _ => hd.1 x
  have hd1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (iteratedDeriv 1 h) (iteratedDeriv 2 h x) x := fun x _ => hd.2 x
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 2 h x| ≤ b := fun x _ => hb 2 (by omega) x
  refine ⟨h, hsm, hzero, hj, ?_, ?_, ?_, ?_⟩
  · intro k hk x
    exact (hb k hk x).trans (min_le_left _ _)
  · exact RematTransfer.perturbed_penalty_monotone ell b hell.le hbell h
      (iteratedDeriv 1 h) (iteratedDeriv 2 h) hd0 hd1 (hj 1) hbound
  · exact RematTransfer.perturbed_quantitative_convexity ell b hbell h
      (iteratedDeriv 1 h) (iteratedDeriv 2 h) hd0 hd1 hbound
  · intro e he m htm hmr
    exact (target_observation_iff hH hK (ht e he).1 (ht e he).2 (a e) (ha e he)
      m htm hmr b hbpos.le hbsmall h (iteratedDeriv 1 h) (iteratedDeriv 2 h)
      hd0 hd1 hzero (hj 1) hbound (forward e) (strict e)).mpr (hr e he m htm hmr)

theorem smooth_fit_continuous {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) (D K H : ℕ) (a : ∀ e, Fin (dimension K (t e)) → ℚ)
    (eps : ℝ) (hfit : SmoothFit A t r forward strict D K H a eps) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc 0 1) ∧ FamilyObservations A t r forward strict D K H a φ := by
  obtain ⟨h, hs, _, _, _, _, _, ho⟩ := hfit
  exact ⟨_, ((continuous_const.mul (continuous_id.pow 2)).add hs.continuous).continuousOn, ho⟩

theorem family_feasibility_equivalence {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) {D K H T : ℕ} (hH : 0 < H) (hT : 0 < T) (hK : 2 * T ≤ K)
    (ht : ∀ e ∈ A, 0 < t e ∧ t e ≤ T)
    (a : ∀ e, Fin (dimension K (t e)) → ℚ)
    (ha : ∀ e ∈ A, RealTarget D K H (t e) (r e) (a e)) :
    ((∃ u : ℝ → ℝ, ContinuousAt u 0 ∧ u 0 = 0 ∧
        RealizesScaled A t r forward strict (D * denominator K) H u) ↔
      (∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc 0 1) ∧ FamilyObservations A t r forward strict D K H a φ)) ∧
    ((∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc 0 1) ∧ FamilyObservations A t r forward strict D K H a φ) ↔
      ∀ eps : ℝ, 0 < eps → SmoothFit A t r forward strict D K H a eps) := by
  have toSmooth (hh : ∃ u : ℝ → ℝ, ContinuousAt u 0 ∧ u 0 = 0 ∧
      RealizesScaled A t r forward strict (D * denominator K) H u) :
      ∀ eps : ℝ, 0 < eps → SmoothFit A t r forward strict D K H a eps := by
    obtain ⟨u, hu, hz, hR⟩ := hh
    exact family_smooth_fit A t r forward strict hH hT hK ht a ha u hu hz hR
  have toOriginal (hh : ∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc 0 1) ∧
      FamilyObservations A t r forward strict D K H a φ) :
      ∃ u : ℝ → ℝ, ContinuousAt u 0 ∧ u 0 = 0 ∧
        RealizesScaled A t r forward strict (D * denominator K) H u := by
    obtain ⟨φ, hφ, ho⟩ := hh
    exact family_observations_necessary A t r forward strict hH hK ht a ha φ hφ ho
  refine ⟨⟨?_, toOriginal⟩, ⟨fun hh => toSmooth (toOriginal hh), ?_⟩⟩
  · intro hh
    exact smooth_fit_continuous A t r forward strict D K H a 1 (toSmooth hh 1 (by norm_num))
  · intro hh
    exact smooth_fit_continuous A t r forward strict D K H a 1 (hh 1 (by norm_num))


def SampleRealizes {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) (D T : ℕ) (u : RematOrderBridge.Sample T → ℝ) : Prop :=
  ∀ e ∈ A, ∀ m : ℕ, t e ≤ m → m ≡ r e [MOD D] →
    ∀ x y : RematOrderBridge.Sample T,
      (x : ℝ) = (t e : ℝ) / m → (y : ℝ) = ((t e - 1 : ℕ) : ℝ) / m →
      Comparison (forward e) (strict e) (u x) (u y)

theorem sample_original_feasibility {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) (D T : ℕ) (hT : 0 < T)
    (ht : ∀ e ∈ A, t e ≤ T) :
    (∃ u : RematOrderBridge.Sample T → ℝ, Continuous u ∧ u (RematOrderBridge.origin T) = 0 ∧
      SampleRealizes A t r forward strict D T u) ↔
    (∃ u : ℝ → ℝ, ContinuousAt u 0 ∧ u 0 = 0 ∧ Realizes A t r forward strict D u) := by
  constructor
  · rintro ⟨u, hu, hz, hR⟩
    obtain ⟨f, hf, hfz, he⟩ := (RematOrderBridge.sample_continuous_iff_ambient T hT u hz).mp hu
    refine ⟨f, hf, hfz, ?_⟩
    intro e heA m htm hmr
    let x : RematOrderBridge.Sample T := ⟨(t e : ℝ) / m,
      RematOrderBridge.fraction_mem_samples T (t e) m (ht e heA) htm⟩
    let y : RematOrderBridge.Sample T := ⟨((t e - 1 : ℕ) : ℝ) / m,
      RematOrderBridge.fraction_mem_samples T (t e - 1) m
        ((Nat.sub_le _ _).trans (ht e heA)) ((Nat.sub_le _ _).trans htm)⟩
    have hh := hR e heA m htm hmr x y rfl rfl
    have hx : f ((t e : ℝ) / m) = u x := he x
    have hy : f (((t e - 1 : ℕ) : ℝ) / m) = u y := he y
    simpa only [hx, hy] using hh
  · rintro ⟨f, hf, hz, hR⟩
    let u : RematOrderBridge.Sample T → ℝ := fun x => f (x : ℝ)
    have huz : u (RematOrderBridge.origin T) = 0 := hz
    refine ⟨u, (RematOrderBridge.sample_continuous_iff_ambient T hT u huz).mpr ⟨f, hf, hz, fun _ => rfl⟩, huz, ?_⟩
    intro e he m htm hmr x y hx hy
    dsimp [u]
    rw [hx, hy]
    exact hR e he m htm hmr

theorem real_target_with_denominator_exists {D K H t r : ℕ} (h : TargetAt D K H t r) :
    ∃ a : Fin (dimension K t) → ℚ, RealTarget D K H t r a ∧
      ∃ C : Fin (dimension K t) → ℕ, ∀ i, a i = (C i : ℚ) / (H * (D * denominator K) : ℕ) := by
  obtain ⟨a, hpos, hsum, hfract, hmass, hC⟩ := target_fin_coordinates h
  refine ⟨a, ⟨?_, ?_, ?_, ?_⟩, hC⟩
  · intro i
    exact_mod_cast hpos i
  · exact_mod_cast hsum
  · intro m hm i
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (hfract m hm i)
    rw [← rat_fract_cast] at hh
    simpa only [Rat.cast_mul, Rat.cast_natCast, Nat.cast_mul] using hh
  · intro m hm
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (hmass m hm)
    push_cast at hh
    simpa only [Rat.cast_mul, Rat.cast_natCast, Nat.cast_mul] using hh

theorem uniform_representation {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (t r : ι → ℕ) {D T : ℕ} (hD : 0 < D) (hT : 0 < T)
    (ht : ∀ e ∈ A, 0 < t e ∧ t e ≤ T) :
    let K := auxiliaryHalf D T
    let B := refined A r D (denominator K)
    ∃ H : ℕ, ∃ a : ∀ e : ι × ℕ, Fin (dimension K (t e.1)) → ℚ,
      0 < H ∧ H ≤ 4 * T ∧
      (∀ e ∈ B, 2 ≤ dimension K (t e.1) ∧ dimension K (t e.1) ≤ 4 * T ∧
        RealTarget D K H (t e.1) e.2 (a e) ∧
        ∃ C : Fin (dimension K (t e.1)) → ℕ,
          ∀ i, a e i = (C i : ℚ) / (H * (D * denominator K) : ℕ)) ∧
      ∀ forward strict : ι → Bool,
        ((∃ u : RematOrderBridge.Sample T → ℝ, Continuous u ∧ u (RematOrderBridge.origin T) = 0 ∧
            SampleRealizes A t r forward strict D T u) ↔
          (∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc 0 1) ∧
            FamilyObservations B (fun e => t e.1) (fun e => e.2)
              (fun e => forward e.1) (fun e => strict e.1) D K H a φ)) ∧
        ((∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc 0 1) ∧
            FamilyObservations B (fun e => t e.1) (fun e => e.2)
              (fun e => forward e.1) (fun e => strict e.1) D K H a φ) ↔
          ∀ eps : ℝ, 0 < eps →
            SmoothFit B (fun e => t e.1) (fun e => e.2)
              (fun e => forward e.1) (fun e => strict e.1) D K H a eps) := by
  classical
  dsimp
  obtain ⟨H, hH, hHb, htargets, hequiv⟩ := uniform_arithmetic_representation A t r hD hT ht
  let B := refined A r D (denominator (auxiliaryHalf D T))
  let K := auxiliaryHalf D T
  have hex (e : ι × ℕ) : ∃ ae : Fin (dimension K (t e.1)) → ℚ,
      e ∈ B → RealTarget D K H (t e.1) e.2 ae ∧
        ∃ C : Fin (dimension K (t e.1)) → ℕ,
          ∀ i, ae i = (C i : ℚ) / (H * (D * denominator K) : ℕ) := by
    by_cases he : e ∈ B
    · obtain ⟨ae, hra, hc⟩ := real_target_with_denominator_exists (htargets e he).2.2
      exact ⟨ae, fun _ => ⟨hra, hc⟩⟩
    · exact ⟨fun _ => 0, fun hh => False.elim (he hh)⟩
  choose a ha using hex
  refine ⟨H, a, hH, hHb, ?_, ?_⟩
  · intro e he
    exact ⟨(htargets e he).1, (htargets e he).2.1, ha e he⟩
  · intro forward strict
    have hb (e : ι × ℕ) (he : e ∈ B) : 0 < t e.1 ∧ t e.1 ≤ T :=
      ht e.1 ((mem_refined A r D (denominator K) e.1 e.2).mp he).1
    have hh := family_feasibility_equivalence B (fun e => t e.1) (fun e => e.2)
      (fun e => forward e.1) (fun e => strict e.1) hH hT (auxiliary_properties hD).1
      hb a (fun e he => (ha e he).1)
    refine ⟨?_, hh.2⟩
    exact (sample_original_feasibility A t r forward strict D T hT (fun e he => (ht e he).2)).trans
      ((hequiv forward strict).trans hh.1)

end

end RematUniformRepresentation

#print axioms RematUniformRepresentation.real_target_exists
#print axioms RematUniformRepresentation.real_target_scaled_data
#print axioms RematUniformRepresentation.target_observation_iff
#print axioms RematUniformRepresentation.target_observation_necessary
#print axioms RematUniformRepresentation.comparison_sub_const
#print axioms RematUniformRepresentation.comparison_oriented
#print axioms RematUniformRepresentation.endpoints_mem_samples
#print axioms RematUniformRepresentation.realizes_scaled_smooth
#print axioms RematUniformRepresentation.smooth_derivative_data
#print axioms RematUniformRepresentation.sample_in_unit_interval
#print axioms RematUniformRepresentation.family_observations_necessary
#print axioms RematUniformRepresentation.family_smooth_fit
#print axioms RematUniformRepresentation.smooth_fit_continuous
#print axioms RematUniformRepresentation.family_feasibility_equivalence
#print axioms RematUniformRepresentation.sample_original_feasibility
#print axioms RematUniformRepresentation.real_target_with_denominator_exists
#print axioms RematUniformRepresentation.uniform_representation
end

section
set_option autoImplicit true
set_option autoImplicit false

open scoped BigOperators ContDiff

namespace RematUniformFinite

open RematUniformTargets RematUniformRepresentation

noncomputable section

def ValidInstance {ι : Type*} (A : Finset ι) (t r : ι → ℕ) (D : ℕ) (e : ι × ℕ) : Prop :=
  e.1 ∈ A ∧ t e.1 ≤ e.2 ∧ e.2 ≡ r e.1 [MOD D]

def SelectedComparisons {ι : Type*} (C : Finset (ι × ℕ)) (t : ι → ℕ)
    (forward strict : ι → Bool) (H : ℕ) (u : ℝ → ℝ) : Prop :=
  ∀ e ∈ C, Comparison (forward e.1) (strict e.1)
    (u ((t e.1 : ℝ) / (H * e.2 : ℕ))) (u (((t e.1 - 1 : ℕ) : ℝ) / (H * e.2 : ℕ)))

def FiniteConsistent {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) (D H : ℕ) : Prop :=
  ∀ C : Finset (ι × ℕ), (∀ e ∈ C, ValidInstance A t r D e) →
    ∃ u : ℝ → ℝ, SelectedComparisons C t forward strict H u

theorem finite_dilation_iff {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) (D H : ℕ) (hH : 0 < H) :
    FiniteConsistent A t r forward strict D 1 ↔ FiniteConsistent A t r forward strict D H := by
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hH
  constructor
  · intro hh C hc
    obtain ⟨u, hu⟩ := hh C hc
    refine ⟨fun x => u ((H : ℝ) * x), ?_⟩
    have he (n m : ℕ) : (H : ℝ) * ((n : ℝ) / (H * m : ℕ)) = (n : ℝ) / m := by
      push_cast
      field_simp
    intro e heC
    simpa only [he, one_mul] using hu e heC
  · intro hh C hc
    obtain ⟨u, hu⟩ := hh C hc
    refine ⟨fun x => u (x / H), ?_⟩
    have he (n m : ℕ) : ((n : ℝ) / m) / H = (n : ℝ) / (H * m : ℕ) := by
      push_cast
      rw [div_div, mul_comm (m : ℝ)]
    intro e heC
    simpa only [one_mul, he] using hu e heC

theorem finite_refinement_iff {ι : Type*} [DecidableEq ι] (A : Finset ι)
    (t r : ι → ℕ) (forward strict : ι → Bool) {D T Q : ℕ}
    (hD : 0 < D) (hQ : 0 < Q) (hcop : (D * T.factorial).Coprime Q)
    (ht : ∀ e ∈ A, 0 < t e ∧ t e ≤ T) :
    FiniteConsistent A t r forward strict D 1 ↔
      FiniteConsistent (refined A r D Q) (fun e => t e.1) (fun e => e.2)
        (fun e => forward e.1) (fun e => strict e.1) (D * Q) 1 := by
  classical
  constructor
  · intro hh C hc
    let p : (ι × ℕ) × ℕ → ι × ℕ := fun e => (e.1.1, e.2)
    have hv : ∀ e ∈ C.image p, ValidInstance A t r D e := by
      intro e he
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨ha, htm, hmr⟩ := hc v hv
      have hm := (mem_refined A r D Q v.1.1 v.1.2).mp ha
      exact ⟨hm.1, htm, (hmr.of_dvd (Nat.dvd_mul_right D Q)).trans hm.2.2.1⟩
    obtain ⟨u, hu⟩ := hh (C.image p) hv
    refine ⟨u, ?_⟩
    intro e he
    exact hu (p e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  · intro hh C hc
    have hex (v : C) : ∃ z : (ι × ℕ) × ℕ,
        ValidInstance (refined A r D Q) (fun e => t e.1) (fun e => e.2) (D * Q) z ∧
        z.1.1 = v.val.1 ∧
        RematCofinalEmbedding.embedding D T Q hcop ((t v.val.1 : ℝ) / v.val.2) = (t z.1.1 : ℝ) / z.2 ∧
        RematCofinalEmbedding.embedding D T Q hcop (((t v.val.1 - 1 : ℕ) : ℝ) / v.val.2) = ((t z.1.1 - 1 : ℕ) : ℝ) / z.2 := by
      have hv := hc v.val v.property
      obtain ⟨m, _, htm, hmQ, hmr, he1, he2⟩ :=
        RematCofinalEmbedding.adjacent_record_image hD hQ hcop (ht v.val.1 hv.1).1
          (ht v.val.1 hv.1).2 hv.2.1 hv.2.2
      obtain ⟨s, hs, hsr, hsQ, hms⟩ :=
        (RematCofinalEmbedding.finite_residue_refinement hD hQ).mp ⟨hmr, hmQ⟩
      refine ⟨((v.val.1, s), m), ⟨?_, htm, hms⟩, rfl, he1, he2⟩
      exact (mem_refined A r D Q v.val.1 s).mpr ⟨hv.1, hs, hsr, hsQ⟩
    choose z hz using hex
    have hv : ∀ e ∈ C.attach.image z,
        ValidInstance (refined A r D Q) (fun e => t e.1) (fun e => e.2) (D * Q) e := by
      intro e he
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he
      exact (hz v).1
    obtain ⟨u, hu⟩ := hh (C.attach.image z) hv
    refine ⟨u ∘ RematCofinalEmbedding.embedding D T Q hcop, ?_⟩
    intro e he
    let v : C := ⟨e, he⟩
    have hobs := hu (z v) (Finset.mem_image.mpr ⟨v, Finset.mem_attach _ _, rfl⟩)
    have hzz := hz v
    change Comparison (forward v.val.1) (strict v.val.1)
      (u (RematCofinalEmbedding.embedding D T Q hcop ((t v.val.1 : ℝ) / (1 * v.val.2 : ℕ))))
      (u (RematCofinalEmbedding.embedding D T Q hcop (((t v.val.1 - 1 : ℕ) : ℝ) / (1 * v.val.2 : ℕ))))
    simp only [one_mul]
    rw [hzz.2.2.1, hzz.2.2.2]
    simpa only [one_mul, hzz.2.1] using hobs


def SelectedObservations {ι : Type*} (C : Finset (ι × ℕ)) (t : ι → ℕ)
    (forward strict : ι → Bool) (K H : ℕ)
    (a : ∀ e, Fin (dimension K (t e)) → ℚ) (φ : ℝ → ℝ) : Prop :=
  ∀ e ∈ C, Observation (forward e.1) (strict e.1) φ
    ((H * e.2 : ℕ) : ℤ) (fun i => (a e.1 i : ℝ))

def SelectedSmoothFit {ι : Type*} (C : Finset (ι × ℕ)) (t : ι → ℕ)
    (forward strict : ι → Bool) (K H : ℕ)
    (a : ∀ e, Fin (dimension K (t e)) → ℚ) (eps : ℝ) : Prop :=
  ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
    (∀ k, iteratedDeriv k h 0 = 0) ∧
    (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ eps / 2) ∧
    MonotoneOn (fun s => (1 / (denominator K : ℝ)) * s^2 + h s) (Set.Icc 0 1) ∧
    ConvexOn ℝ (Set.Icc 0 1)
      (fun s => ((1 / (denominator K : ℝ)) * s^2 + h s) - (1 / (denominator K : ℝ)) / 2 * s^2) ∧
    SelectedObservations C t forward strict K H a
      (fun s => (1 / (denominator K : ℝ)) * s^2 + h s)

def FiniteLossConsistent {ι : Type*} (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) (D K H : ℕ)
    (a : ∀ e, Fin (dimension K (t e)) → ℚ) : Prop :=
  ∀ C : Finset (ι × ℕ), (∀ e ∈ C, ValidInstance A t r (D * denominator K) e) →
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc 0 1) ∧ SelectedObservations C t forward strict K H a φ

theorem selected_observations_necessary {ι : Type*} (A : Finset ι) (C : Finset (ι × ℕ))
    (t r : ι → ℕ) (forward strict : ι → Bool) {D K H T : ℕ}
    (hH : 0 < H) (hK : 2 * T ≤ K) (ht : ∀ e ∈ A, 0 < t e ∧ t e ≤ T)
    (hc : ∀ e ∈ C, ValidInstance A t r (D * denominator K) e)
    (a : ∀ e, Fin (dimension K (t e)) → ℚ)
    (ha : ∀ e ∈ A, RealTarget D K H (t e) (r e) (a e))
    (φ : ℝ → ℝ) (ho : SelectedObservations C t forward strict K H a φ) :
    ∃ u : ℝ → ℝ, SelectedComparisons C t forward strict H u := by
  refine ⟨fun s => φ s - (1 / (denominator K : ℝ)) * s^2, ?_⟩
  intro e he
  obtain ⟨heA, htm, hmr⟩ := hc e he
  exact target_observation_necessary hH hK (ht e.1 heA).1 (ht e.1 heA).2
    (a e.1) (ha e.1 heA) e.2 htm hmr φ (forward e.1) (strict e.1) (ho e he)

theorem selected_smooth_continuous {ι : Type*} (C : Finset (ι × ℕ)) (t : ι → ℕ)
    (forward strict : ι → Bool) (K H : ℕ) (a : ∀ e, Fin (dimension K (t e)) → ℚ)
    (eps : ℝ) (hfit : SelectedSmoothFit C t forward strict K H a eps) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc 0 1) ∧ SelectedObservations C t forward strict K H a φ := by
  obtain ⟨h, hs, _, _, _, _, _, ho⟩ := hfit
  exact ⟨_, ((continuous_const.mul (continuous_id.pow 2)).add hs.continuous).continuousOn, ho⟩


theorem selected_comparisons_smooth {ι : Type*} (C : Finset (ι × ℕ)) (t : ι → ℕ)
    (forward strict : ι → Bool) (H T : ℕ) (hH : 0 < H) (hT : 0 < T)
    (hc : ∀ e ∈ C, t e.1 ≤ T ∧ t e.1 ≤ e.2)
    (u : ℝ → ℝ) (hu : SelectedComparisons C t forward strict H u)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
      (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ eps) ∧
      SelectedComparisons C t forward strict H h := by
  classical
  let x (e : C) : RematOrderBridge.Sample T :=
    ⟨leftEndpoint (forward e.val.1) H (t e.val.1) e.val.2,
      (endpoints_mem_samples hH (hc e.val e.property).1 (hc e.val e.property).2 (forward e.val.1)).1⟩
  let y (e : C) : RematOrderBridge.Sample T :=
    ⟨rightEndpoint (forward e.val.1) H (t e.val.1) e.val.2,
      (endpoints_mem_samples hH (hc e.val e.property).1 (hc e.val e.property).2 (forward e.val.1)).2⟩
  let Edge (b : Bool) (v w : RematOrderBridge.Sample T) : Prop :=
    ∃ e : C, strict e.val.1 = b ∧ v = x e ∧ w = y e
  let s := Finset.univ.image x ∪ Finset.univ.image y
  have hs (v w : RematOrderBridge.Sample T) (he : Edge false v w ∨ Edge true v w) : v ∈ s ∧ w ∈ s := by
    rcases he with ⟨e, _, rfl, rfl⟩ | ⟨e, _, rfl, rfl⟩ <;>
      exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩),
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)⟩
  let v : RematOrderBridge.Sample T → ℝ := fun p => u (p : ℝ) - u 0
  have hvz : v (RematOrderBridge.origin T) = 0 := sub_self _
  have hw (p q : RematOrderBridge.Sample T) (hh : Edge false p q) : v p ≤ v q := by
    obtain ⟨e, he, rfl, rfl⟩ := hh
    have hcmp := (comparison_oriented (forward e.val.1) (strict e.val.1) u H (t e.val.1) e.val.2).mp (hu e.val e.property)
    simp only [he, Bool.false_eq_true, ↓reduceIte] at hcmp
    exact sub_le_sub_right hcmp _
  have he (p q : RematOrderBridge.Sample T) (hh : Edge true p q) : v p < v q := by
    obtain ⟨e, he, rfl, rfl⟩ := hh
    have hcmp := (comparison_oriented (forward e.val.1) (strict e.val.1) u H (t e.val.1) e.val.2).mp (hu e.val e.property)
    simp only [he, ↓reduceIte] at hcmp
    exact sub_lt_sub_right hcmp _
  obtain ⟨h, hsm, hz, hj, hb, hw, he⟩ :=
    RematOrderBridge.finite_relations_smooth T hT (Edge false) (Edge true) s hs v hvz hw he eps heps
  refine ⟨h, hsm, hz, hj, hb, ?_⟩
  intro e heC
  let p : C := ⟨e, heC⟩
  apply (comparison_oriented (forward e.1) (strict e.1) h H (t e.1) e.2).mpr
  cases hb : strict e.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hw (x p) (y p) ⟨p, hb, rfl, rfl⟩
  · simp only [↓reduceIte]
    exact he (x p) (y p) ⟨p, hb, rfl, rfl⟩

theorem selected_smooth_fit {ι : Type*} (A : Finset ι) (C : Finset (ι × ℕ))
    (t r : ι → ℕ) (forward strict : ι → Bool) {D K H T : ℕ}
    (hH : 0 < H) (hT : 0 < T) (hK : 2 * T ≤ K)
    (ht : ∀ e ∈ A, 0 < t e ∧ t e ≤ T)
    (hc : ∀ e ∈ C, ValidInstance A t r (D * denominator K) e)
    (a : ∀ e, Fin (dimension K (t e)) → ℚ)
    (ha : ∀ e ∈ A, RealTarget D K H (t e) (r e) (a e))
    (u : ℝ → ℝ) (hu : SelectedComparisons C t forward strict H u)
    (eps : ℝ) (heps : 0 < eps) : SelectedSmoothFit C t forward strict K H a eps := by
  let ell : ℝ := 1 / (denominator K : ℝ)
  have hell : 0 < ell := by dsimp [ell]; apply one_div_pos.mpr; simp [denominator]; positivity
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ (T : ℝ)^2 := by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  let b : ℝ := min (eps / 2) (ell / (2 * (T : ℝ)^2))
  have hbpos : 0 < b := lt_min (by positivity) (by positivity)
  have hbsmall : b < ell / (T : ℝ)^2 := by
    have hh := min_le_right (eps / 2) (ell / (2 * (T : ℝ)^2))
    have hp : 0 < ell / (T : ℝ)^2 := by positivity
    have hid : ell / (2 * (T : ℝ)^2) = (ell / (T : ℝ)^2) / 2 := by ring
    dsimp [b]
    rw [hid] at hh ⊢
    linarith
  have hbell : b ≤ ell := hbsmall.le.trans (div_le_self hell.le hT1)
  obtain ⟨h, hsm, hzero, hj, hb, hr⟩ := selected_comparisons_smooth C t forward strict H T hH hT
    (fun e he => ⟨(ht e.1 (hc e he).1).2, (hc e he).2.1⟩) u hu b hbpos
  have hd := smooth_derivative_data h hsm
  have hd0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h (iteratedDeriv 1 h x) x := fun x _ => hd.1 x
  have hd1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (iteratedDeriv 1 h) (iteratedDeriv 2 h x) x := fun x _ => hd.2 x
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 2 h x| ≤ b := fun x _ => hb 2 (by omega) x
  refine ⟨h, hsm, hzero, hj, ?_, ?_, ?_, ?_⟩
  · intro k hk x
    exact (hb k hk x).trans (min_le_left _ _)
  · exact RematTransfer.perturbed_penalty_monotone ell b hell.le hbell h
      (iteratedDeriv 1 h) (iteratedDeriv 2 h) hd0 hd1 (hj 1) hbound
  · exact RematTransfer.perturbed_quantitative_convexity ell b hbell h
      (iteratedDeriv 1 h) (iteratedDeriv 2 h) hd0 hd1 hbound
  · intro e he
    obtain ⟨heA, htm, hmr⟩ := hc e he
    exact (target_observation_iff hH hK (ht e.1 heA).1 (ht e.1 heA).2 (a e.1) (ha e.1 heA)
      e.2 htm hmr b hbpos.le hbsmall h (iteratedDeriv 1 h) (iteratedDeriv 2 h)
      hd0 hd1 hzero (hj 1) hbound (forward e.1) (strict e.1)).mpr (hr e he)

theorem finite_loss_equivalence {ι : Type*} (A : Finset ι)
    (t r : ι → ℕ) (forward strict : ι → Bool) {D K H T : ℕ}
    (hH : 0 < H) (hT : 0 < T) (hK : 2 * T ≤ K)
    (ht : ∀ e ∈ A, 0 < t e ∧ t e ≤ T)
    (a : ∀ e, Fin (dimension K (t e)) → ℚ)
    (ha : ∀ e ∈ A, RealTarget D K H (t e) (r e) (a e)) :
    (FiniteConsistent A t r forward strict (D * denominator K) H ↔
      FiniteLossConsistent A t r forward strict D K H a) ∧
    (FiniteLossConsistent A t r forward strict D K H a ↔
      ∀ C : Finset (ι × ℕ), (∀ e ∈ C, ValidInstance A t r (D * denominator K) e) →
        ∀ eps : ℝ, 0 < eps → SelectedSmoothFit C t forward strict K H a eps) := by
  have toSmooth (hh : FiniteConsistent A t r forward strict (D * denominator K) H) :
      ∀ C : Finset (ι × ℕ), (∀ e ∈ C, ValidInstance A t r (D * denominator K) e) →
        ∀ eps : ℝ, 0 < eps → SelectedSmoothFit C t forward strict K H a eps := by
    intro C hc eps heps
    obtain ⟨u, hu⟩ := hh C hc
    exact selected_smooth_fit A C t r forward strict hH hT hK ht hc a ha u hu eps heps
  have toOriginal (hh : FiniteLossConsistent A t r forward strict D K H a) :
      FiniteConsistent A t r forward strict (D * denominator K) H := by
    intro C hc
    obtain ⟨φ, _, ho⟩ := hh C hc
    exact selected_observations_necessary A C t r forward strict hH hK ht hc a ha φ ho
  refine ⟨⟨?_, toOriginal⟩, ⟨fun hh => toSmooth (toOriginal hh), ?_⟩⟩
  · intro hh C hc
    exact selected_smooth_continuous C t forward strict K H a 1 (toSmooth hh C hc 1 (by norm_num))
  · intro hh C hc
    exact selected_smooth_continuous C t forward strict K H a 1 (hh C hc 1 (by norm_num))

def GlobalEquivalences {ι : Type*} [DecidableEq ι] (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) (D T H : ℕ)
    (a : ∀ e : ι × ℕ, Fin (dimension (auxiliaryHalf D T) (t e.1)) → ℚ) : Prop :=
  let K := auxiliaryHalf D T
  let B := refined A r D (denominator K)
  ((∃ u : RematOrderBridge.Sample T → ℝ, Continuous u ∧ u (RematOrderBridge.origin T) = 0 ∧
      SampleRealizes A t r forward strict D T u) ↔
    (∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc 0 1) ∧
      FamilyObservations B (fun e => t e.1) (fun e => e.2)
        (fun e => forward e.1) (fun e => strict e.1) D K H a φ)) ∧
  ((∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc 0 1) ∧
      FamilyObservations B (fun e => t e.1) (fun e => e.2)
        (fun e => forward e.1) (fun e => strict e.1) D K H a φ) ↔
    ∀ eps : ℝ, 0 < eps →
      SmoothFit B (fun e => t e.1) (fun e => e.2)
        (fun e => forward e.1) (fun e => strict e.1) D K H a eps)

def FiniteEquivalences {ι : Type*} [DecidableEq ι] (A : Finset ι) (t r : ι → ℕ)
    (forward strict : ι → Bool) (D T H : ℕ)
    (a : ∀ e : ι × ℕ, Fin (dimension (auxiliaryHalf D T) (t e.1)) → ℚ) : Prop :=
  let K := auxiliaryHalf D T
  let B := refined A r D (denominator K)
  (FiniteConsistent A t r forward strict D 1 ↔
    FiniteLossConsistent B (fun e => t e.1) (fun e => e.2)
      (fun e => forward e.1) (fun e => strict e.1) D K H a) ∧
  (FiniteLossConsistent B (fun e => t e.1) (fun e => e.2)
      (fun e => forward e.1) (fun e => strict e.1) D K H a ↔
    ∀ C : Finset ((ι × ℕ) × ℕ),
      (∀ e ∈ C, ValidInstance B (fun e => t e.1) (fun e => e.2) (D * denominator K) e) →
      ∀ eps : ℝ, 0 < eps → SelectedSmoothFit C (fun e => t e.1)
        (fun e => forward e.1) (fun e => strict e.1) K H a eps)

theorem uniform_full_representation {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (t r : ι → ℕ) {D T : ℕ} (hD : 0 < D) (hT : 0 < T)
    (ht : ∀ e ∈ A, 0 < t e ∧ t e ≤ T) :
    let K := auxiliaryHalf D T
    let B := refined A r D (denominator K)
    ∃ H : ℕ, ∃ a : ∀ e : ι × ℕ, Fin (dimension K (t e.1)) → ℚ,
      0 < H ∧ H ≤ 4 * T ∧
      (∀ e ∈ B, 2 ≤ dimension K (t e.1) ∧ dimension K (t e.1) ≤ 4 * T ∧
        RealTarget D K H (t e.1) e.2 (a e) ∧
        ∃ C : Fin (dimension K (t e.1)) → ℕ,
          ∀ i, a e i = (C i : ℚ) / (H * (D * denominator K) : ℕ)) ∧
      ∀ forward strict : ι → Bool,
        GlobalEquivalences A t r forward strict D T H a ∧
        FiniteEquivalences A t r forward strict D T H a := by
  classical
  dsimp
  obtain ⟨H, a, hH, hHb, hdata, hmain⟩ := uniform_representation A t r hD hT ht
  refine ⟨H, a, hH, hHb, hdata, ?_⟩
  intro forward strict
  refine ⟨hmain forward strict, ?_⟩
  let K := auxiliaryHalf D T
  let B := refined A r D (denominator K)
  have hbt (e : ι × ℕ) (he : e ∈ B) : 0 < t e.1 ∧ t e.1 ≤ T :=
    ht e.1 ((mem_refined A r D (denominator K) e.1 e.2).mp he).1
  have hh := finite_loss_equivalence B (fun e => t e.1) (fun e => e.2)
    (fun e => forward e.1) (fun e => strict e.1) hH hT (auxiliary_properties hD).1
    hbt a (fun e he => (hdata e he).2.2.1)
  have hQ : 0 < denominator K := by simp [denominator]
  have hre := finite_refinement_iff A t r forward strict hD hQ (auxiliary_properties hD).2.2.1 ht
  have hdil := finite_dilation_iff B (fun e => t e.1) (fun e => e.2)
    (fun e => forward e.1) (fun e => strict e.1) (D * denominator K) H hH
  exact ⟨hre.trans (hdil.trans hh.1), hh.2⟩

end

end RematUniformFinite

#print axioms RematUniformFinite.finite_dilation_iff
#print axioms RematUniformFinite.finite_refinement_iff
#print axioms RematUniformFinite.selected_observations_necessary
#print axioms RematUniformFinite.selected_smooth_continuous
#print axioms RematUniformFinite.selected_comparisons_smooth
#print axioms RematUniformFinite.selected_smooth_fit
#print axioms RematUniformFinite.finite_loss_equivalence
#print axioms RematUniformFinite.uniform_full_representation
end

section
set_option autoImplicit true
set_option autoImplicit false

namespace RematProfileNecessity

theorem two_profiles_integer_coordinate (H D r : ℕ) (a f : ℚ)
    (hH : 0 < H) (hD : 0 < D) (ha : 0 < a)
    (h0 : Int.fract ((H : ℚ) * r * a) = f)
    (h1 : Int.fract ((H : ℚ) * (r + D) * a) = f) :
    ∃ c : ℕ, 0 < c ∧ (H : ℚ) * D * a = c := by
  obtain ⟨_, _, z0, hz0⟩ := Int.fract_eq_iff.mp h0
  obtain ⟨_, _, z1, hz1⟩ := Int.fract_eq_iff.mp h1
  have he : (H : ℚ) * D * a = ((z1 - z0 : ℤ) : ℚ) := by
    push_cast
    nlinarith
  have hcpos : 0 < z1 - z0 := by
    exact_mod_cast (show (0 : ℚ) < ((z1 - z0 : ℤ) : ℚ) by
      rw [← he]
      exact mul_pos (mul_pos (Nat.cast_pos.mpr hH) (Nat.cast_pos.mpr hD)) ha)
  refine ⟨(z1 - z0).toNat, Int.pos_iff_toNat_pos.mp hcpos, ?_⟩
  rw [he]
  norm_cast
  exact (Int.toNat_of_nonneg hcpos.le).symm

theorem fractional_integer_residue (D r c : ℕ) (f : ℚ)
    (hD : 0 < D) (hf : 0 < f) (hfract : Int.fract ((r : ℚ) * c / D) = f) :
    ∃ w : ℕ, 0 < w ∧ w < D ∧ (D : ℚ) * f = w ∧ Nat.ModEq D (r * c) w ∧ Nat.gcd D r ∣ w := by
  have hf1 := (Int.fract_eq_iff.mp hfract).2.1
  obtain ⟨_, _, z, hz⟩ := Int.fract_eq_iff.mp hfract
  have hDr : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have he : (D : ℚ) * f = (((r : ℤ) * c - (D : ℤ) * z : ℤ) : ℚ) := by
    push_cast
    field_simp at hz
    nlinarith
  let wz : ℤ := (r : ℤ) * c - (D : ℤ) * z
  have hwz : 0 < wz := by
    exact_mod_cast (show (0 : ℚ) < (wz : ℚ) by rw [← he]; exact mul_pos (Nat.cast_pos.mpr hD) hf)
  let w : ℕ := wz.toNat
  have hwcast : (w : ℤ) = wz := Int.toNat_of_nonneg hwz.le
  have hew : (D : ℚ) * f = w := by
    rw [he]
    exact_mod_cast hwcast.symm
  have hwpos : 0 < w := Int.pos_iff_toNat_pos.mp hwz
  have hwlt : w < D := by
    have hDpos : (0 : ℚ) < D := by exact_mod_cast hD
    have : (w : ℚ) < D := by rw [← hew]; nlinarith [hDpos]
    exact_mod_cast this
  have hmod : Nat.ModEq D (r * c) w := by
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨-z, ?_⟩
    push_cast
    rw [hwcast]
    dsimp [wz]
    ring
  have hg : Nat.gcd D r ∣ w := by
    have hr : Nat.gcd D r ∣ r * c := dvd_mul_of_dvd_left (Nat.gcd_dvd_right D r) c
    exact (hmod.dvd_iff (Nat.gcd_dvd_left D r)).mp hr
  exact ⟨w, hwpos, hwlt, hew, hmod, hg⟩

theorem constant_profile_lattice_necessary (H D r : ℕ) (a f : ℚ)
    (hH : 0 < H) (hD : 0 < D) (ha : 0 < a) (hf : 0 < f)
    (h0 : Int.fract ((H : ℚ) * r * a) = f)
    (h1 : Int.fract ((H : ℚ) * (r + D) * a) = f) :
    ∃ c w : ℕ, 0 < c ∧ (H : ℚ) * D * a = c ∧ 0 < w ∧ w < D ∧
      (D : ℚ) * f = w ∧ Nat.ModEq D (r * c) w ∧ Nat.gcd D r ∣ w := by
  obtain ⟨c, hcpos, hc⟩ := two_profiles_integer_coordinate H D r a f hH hD ha h0 h1
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hr : (r : ℚ) * c / D = (H : ℚ) * r * a := by
    rw [← hc]
    field_simp
  obtain ⟨w, hw⟩ := fractional_integer_residue D r c f hD hf (by rwa [hr])
  exact ⟨c, w, hcpos, hc, hw⟩

end RematProfileNecessity

#print axioms RematProfileNecessity.two_profiles_integer_coordinate
#print axioms RematProfileNecessity.fractional_integer_residue
#print axioms RematProfileNecessity.constant_profile_lattice_necessary
end

section
set_option autoImplicit true
open scoped BigOperators

set_option autoImplicit false

namespace RematProfileInverse

theorem simplex_integer_coordinates (N H D r : ℕ) (a f : Fin N → ℚ)
    (hH : 0 < H) (hD : 0 < D) (ha : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 1)
    (h0 : ∀ i, Int.fract ((H : ℚ) * r * a i) = f i)
    (h1 : ∀ i, Int.fract ((H : ℚ) * (r + D) * a i) = f i) :
    ∃ C : Fin N → ℕ, (∑ i, C i = H * D) ∧
      ∀ i, 0 < C i ∧ (H : ℚ) * D * a i = C i := by
  choose C hC using fun i => RematProfileNecessity.two_profiles_integer_coordinate
    H D r (a i) (f i) hH hD (ha i) (h0 i) (h1 i)
  refine ⟨C, ?_, hC⟩
  have he : ((∑ i, C i : ℕ) : ℚ) = (H : ℚ) * D := by
    push_cast
    calc
      (∑ i, (C i : ℚ)) = ∑ i, (H : ℚ) * D * a i :=
        Finset.sum_congr rfl (fun i _ => (hC i).2.symm)
      _ = (H : ℚ) * D := by rw [← Finset.mul_sum, hsum, mul_one]
  exact_mod_cast he

theorem profile_minimum_height_necessary (N H D r : ℕ) (a : Fin N → ℚ)
    (w c : Fin N → ℕ) (hH : 0 < H) (hD : 0 < D)
    (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1)
    (hw : ∀ i, 0 < w i ∧ w i < D)
    (hc : ∀ i, c i < D / Nat.gcd D r ∧ Nat.ModEq D (r * c i) (w i))
    (h0 : ∀ i, Int.fract ((H : ℚ) * r * a i) = (w i : ℚ) / D)
    (h1 : ∀ i, Int.fract ((H : ℚ) * (r + D) * a i) = (w i : ℚ) / D) :
    Nat.ceil (((∑ i, c i : ℕ) : ℚ) / D) ≤ H := by
  obtain ⟨C, hCsum, hC⟩ := simplex_integer_coordinates N H D r a
    (fun i => (w i : ℚ) / D) hH hD ha hsum h0 h1
  apply RematDilationArithmetic.least_height_necessary Finset.univ D r H w c C hD
    (fun i _ => hc i) ?_ hCsum
  intro i _
  obtain ⟨z, hzpos, hzlt, he, hmod, _⟩ := RematProfileNecessity.fractional_integer_residue
    D r (C i) ((w i : ℚ) / D) hD
    (div_pos (by exact_mod_cast (hw i).1) (by exact_mod_cast hD)) (by
      have hd : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
      have hrel : (r : ℚ) * C i / D = (H : ℚ) * r * a i := by
        rw [← (hC i).2]
        field_simp
      rw [hrel]
      exact h0 i)
  have hz : z = w i := by
    have hd : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    have : (w i : ℚ) = z := by simpa [mul_div_cancel₀, hd] using he
    exact_mod_cast this.symm
  simpa [hz] using hmod

end RematProfileInverse

#print axioms RematProfileInverse.simplex_integer_coordinates
#print axioms RematProfileInverse.profile_minimum_height_necessary
end

section
set_option autoImplicit true
set_option autoImplicit false

open scoped BigOperators

namespace RematProfileRealBridge

theorem rat_fract_cast (q : ℚ) : Int.fract (q : ℝ) = ((Int.fract q : ℚ) : ℝ) :=
  Int.map_fract (Rat.castHom ℝ) Rat.cast_strictMono q

theorem real_profile_rational (H r : ℕ) (a : ℚ) (f : ℝ)
    (hf : Int.fract ((H : ℝ) * r * (a : ℝ)) = f) :
    ∃ q : ℚ, (q : ℝ) = f ∧ Int.fract ((H : ℚ) * r * a) = q := by
  refine ⟨Int.fract ((H : ℚ) * r * a), ?_, rfl⟩
  rw [← rat_fract_cast]
  simpa only [Rat.cast_mul, Rat.cast_natCast] using hf

theorem positive_real_lattice (D : ℕ) (f : ℝ) (hD : 0 < D)
    (hf : 0 < f) (hf1 : f < 1) (hint : ∃ z : ℤ, (D : ℝ) * f = z) :
    ∃ w : ℕ, 0 < w ∧ w < D ∧ (D : ℝ) * f = w ∧
      (((w : ℚ) / D : ℚ) : ℝ) = f := by
  obtain ⟨z, hz⟩ := hint
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hzpos : 0 < z := by exact_mod_cast (show (0 : ℝ) < (z : ℝ) by rw [← hz]; positivity)
  let w := z.toNat
  have hwz : (w : ℤ) = z := Int.toNat_of_nonneg hzpos.le
  have hw : (D : ℝ) * f = w := by rw [hz]; exact_mod_cast hwz.symm
  have hwb : w < D := by
    have : (w : ℝ) < D := by rw [← hw]; nlinarith
    exact_mod_cast this
  refine ⟨w, Int.pos_iff_toNat_pos.mp hzpos, hwb, hw, ?_⟩
  push_cast
  exact (eq_div_iff hDr.ne').mpr (by simpa [mul_comm] using hw) |>.symm

theorem real_profile_lattice_necessary (H D r : ℕ) (a : ℚ) (f : ℝ)
    (hH : 0 < H) (hD : 0 < D) (ha : 0 < a) (hf : 0 < f)
    (h0 : Int.fract ((H : ℝ) * r * (a : ℝ)) = f)
    (h1 : Int.fract ((H : ℝ) * (r + D) * (a : ℝ)) = f) :
    ∃ c w : ℕ, 0 < c ∧ (H : ℝ) * D * (a : ℝ) = c ∧ 0 < w ∧ w < D ∧
      (D : ℝ) * f = w ∧ Nat.ModEq D (r * c) w ∧ Nat.gcd D r ∣ w := by
  obtain ⟨q, hq, h0q⟩ := real_profile_rational H r a f h0
  have hqpos : 0 < q := by exact_mod_cast (hq.symm ▸ hf)
  have h1q : Int.fract ((H : ℚ) * (r + D) * a) = q := by
    apply Rat.cast_injective (α := ℝ)
    rw [← rat_fract_cast, hq]
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_natCast] using h1
  obtain ⟨c, w, hc, hce, hw, hwD, hwq, hm, hg⟩ :=
    RematProfileNecessity.constant_profile_lattice_necessary H D r a q hH hD ha hqpos h0q h1q
  refine ⟨c, w, hc, ?_, hw, hwD, ?_, hm, hg⟩
  · exact_mod_cast hce
  · rw [← hq]
    exact_mod_cast hwq

theorem real_simplex_integer_coordinates (N H D r : ℕ) (a : Fin N → ℚ) (f : Fin N → ℝ)
    (hH : 0 < H) (hD : 0 < D) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1)
    (h0 : ∀ i, Int.fract ((H : ℝ) * r * (a i : ℝ)) = f i)
    (h1 : ∀ i, Int.fract ((H : ℝ) * (r + D) * (a i : ℝ)) = f i) :
    ∃ C : Fin N → ℕ, (∑ i, C i = H * D) ∧
      ∀ i, 0 < C i ∧ (H : ℝ) * D * (a i : ℝ) = C i := by
  choose q hq h0q using fun i => real_profile_rational H r (a i) (f i) (h0 i)
  have h1q (i : Fin N) : Int.fract ((H : ℚ) * (r + D) * a i) = q i := by
    apply Rat.cast_injective (α := ℝ)
    rw [← rat_fract_cast, hq i]
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_natCast] using h1 i
  obtain ⟨C, hs, hc⟩ := RematProfileInverse.simplex_integer_coordinates N H D r a q hH hD ha hsum h0q h1q
  refine ⟨C, hs, fun i => ⟨(hc i).1, ?_⟩⟩
  exact_mod_cast (hc i).2

theorem real_profile_minimum_height (N H D r : ℕ) (a : Fin N → ℚ) (f : Fin N → ℝ)
    (w c : Fin N → ℕ) (hH : 0 < H) (hD : 0 < D)
    (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1)
    (hw : ∀ i, 0 < w i ∧ w i < D) (hfw : ∀ i, (D : ℝ) * f i = w i)
    (hc : ∀ i, c i < D / Nat.gcd D r ∧ Nat.ModEq D (r * c i) (w i))
    (h0 : ∀ i, Int.fract ((H : ℝ) * r * (a i : ℝ)) = f i)
    (h1 : ∀ i, Int.fract ((H : ℝ) * (r + D) * (a i : ℝ)) = f i) :
    Nat.ceil (((∑ i, c i : ℕ) : ℚ) / D) ≤ H := by
  have hf (i : Fin N) : f i = (w i : ℝ) / D :=
    (eq_div_iff (show (D : ℝ) ≠ 0 by exact_mod_cast hD.ne')).mpr (by simpa [mul_comm] using hfw i)
  apply RematProfileInverse.profile_minimum_height_necessary N H D r a w c hH hD ha hsum hw hc
  · intro i
    apply Rat.cast_injective (α := ℝ)
    rw [← rat_fract_cast]
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast] using (h0 i).trans (hf i)
  · intro i
    apply Rat.cast_injective (α := ℝ)
    rw [← rat_fract_cast]
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_natCast] using (h1 i).trans (hf i)


theorem real_lattice_profile_all_heights {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (hs : s.Nonempty) (D r : ℕ) (f : ι → ℝ) (hD : 0 < D)
    (hf : ∀ i ∈ s, 0 < f i ∧ f i < 1)
    (hint : ∀ i ∈ s, ∃ z : ℤ, (D : ℝ) * f i = z ∧ ((Nat.gcd D r : ℕ) : ℤ) ∣ z)
    (hsint : ∃ z : ℤ, ∑ i ∈ s, f i = z) :
    ∃ L : ℕ, 0 < L ∧ L ≤ s.card ∧ ∀ H : ℕ, L ≤ H →
      ∃ a : ι → ℚ, (∀ i ∈ s, 0 < a i) ∧ (∑ i ∈ s, a i = 1) ∧
        ∀ j : ℕ, ∀ i ∈ s,
          Int.fract (((H * (r + j * D) : ℕ) : ℝ) * (a i : ℝ)) = f i := by
  classical
  have hex (i : ι) : ∃ w : ℕ, i ∈ s → 0 < w ∧ w < D ∧ Nat.gcd D r ∣ w ∧ (D : ℝ) * f i = w := by
    by_cases hi : i ∈ s
    · obtain ⟨z, hz, hgz⟩ := hint i hi
      obtain ⟨w, hw, hwD, hwe, _⟩ := positive_real_lattice D (f i) hD (hf i hi).1 (hf i hi).2 ⟨z, hz⟩
      have hzw : (w : ℤ) = z := by
        exact_mod_cast (show (w : ℝ) = (z : ℝ) from hwe.symm.trans hz)
      have hgw : Nat.gcd D r ∣ w := by
        exact_mod_cast (show ((Nat.gcd D r : ℕ) : ℤ) ∣ (w : ℤ) by rwa [hzw])
      exact ⟨w, fun _ => ⟨hw, hwD, hgw, hwe⟩⟩
    · exact ⟨0, fun hh => False.elim (hi hh)⟩
  choose w hw using hex
  obtain ⟨z, hz⟩ := hsint
  have hsumpos : 0 < ∑ i ∈ s, f i := Finset.sum_pos (fun i hi => (hf i hi).1) hs
  have hzpos : 0 < z := by exact_mod_cast (hz ▸ hsumpos)
  let t := z.toNat
  have hzt : (t : ℤ) = z := Int.toNat_of_nonneg hzpos.le
  have hsum : ∑ i ∈ s, f i = (t : ℝ) := by rw [hz]; exact_mod_cast hzt.symm
  have hwsum : ∑ i ∈ s, w i = D * t := by
    have hh : (∑ i ∈ s, (w i : ℝ)) = (D : ℝ) * t := by
      calc
        (∑ i ∈ s, (w i : ℝ)) = ∑ i ∈ s, (D : ℝ) * f i :=
          Finset.sum_congr rfl (fun i hi => (hw i hi).2.2.2.symm)
        _ = (D : ℝ) * t := by rw [← Finset.mul_sum, hsum]
    exact_mod_cast hh
  obtain ⟨c, _, hL, hLN, htarget⟩ := RematDilationArithmetic.lattice_profile_all_heights
    s hs D r t w hD (fun i hi => ⟨(hw i hi).1, (hw i hi).2.1, (hw i hi).2.2.1⟩) hwsum
  refine ⟨_, hL, hLN, ?_⟩
  intro H hH
  obtain ⟨C, _, hpos, hasum, hfract, _⟩ := htarget H hH
  refine ⟨fun i => (C i : ℚ) / (H * D : ℕ), hpos, hasum, ?_⟩
  intro j i hi
  have hh := congrArg (fun x : ℚ => (x : ℝ)) (hfract j i hi)
  rw [← rat_fract_cast] at hh
  have hfi : (w i : ℝ) / D = f i :=
    ((eq_div_iff (show (D : ℝ) ≠ 0 by exact_mod_cast hD.ne')).mpr
      (by simpa [mul_comm] using (hw i hi).2.2.2)).symm
  simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, hfi] using hh

end RematProfileRealBridge

#print axioms RematProfileRealBridge.rat_fract_cast
#print axioms RematProfileRealBridge.real_profile_rational
#print axioms RematProfileRealBridge.positive_real_lattice
#print axioms RematProfileRealBridge.real_profile_lattice_necessary
#print axioms RematProfileRealBridge.real_simplex_integer_coordinates
#print axioms RematProfileRealBridge.real_profile_minimum_height
#print axioms RematProfileRealBridge.real_lattice_profile_all_heights
end

section
set_option autoImplicit true
set_option autoImplicit false

open Filter Topology

namespace RematCompactFamily

theorem anchor_first_fraction (j : ℕ) :
    Int.fract ((4 * (1 + 9 * (j : ℚ))) * (31 / 36)) = (4 / 9 : ℚ) := by
  apply Int.fract_eq_iff.mpr
  refine ⟨by norm_num, by norm_num, (31 * j + 3 : ℤ), ?_⟩
  push_cast
  ring

theorem anchor_second_fraction (j : ℕ) :
    Int.fract ((4 * (1 + 9 * (j : ℚ))) * (4 / 36)) = (4 / 9 : ℚ) := by
  apply Int.fract_eq_iff.mpr
  refine ⟨by norm_num, by norm_num, (4 * j : ℤ), ?_⟩
  push_cast
  ring

theorem anchor_third_fraction (j : ℕ) :
    Int.fract ((4 * (1 + 9 * (j : ℚ))) * (1 / 36)) = (1 / 9 : ℚ) := by
  apply Int.fract_eq_iff.mpr
  refine ⟨by norm_num, by norm_num, (j : ℤ), ?_⟩
  push_cast
  ring

theorem residue_one_first_fraction (j : ℕ) :
    Int.fract ((4 * (4 + 3 * (j : ℚ))) * (7 / 12)) = (1 / 3 : ℚ) := by
  apply Int.fract_eq_iff.mpr
  refine ⟨by norm_num, by norm_num, (7 * j + 9 : ℤ), ?_⟩
  push_cast
  ring

theorem residue_one_other_fraction (j : ℕ) :
    Int.fract ((4 * (4 + 3 * (j : ℚ))) * (1 / 12)) = (1 / 3 : ℚ) := by
  apply Int.fract_eq_iff.mpr
  refine ⟨by norm_num, by norm_num, (j + 1 : ℤ), ?_⟩
  push_cast
  ring

theorem residue_two_fraction (j : ℕ) :
    Int.fract ((4 * (2 + 3 * (j : ℚ))) * (1 / 6)) = (1 / 3 : ℚ) := by
  apply Int.fract_eq_iff.mpr
  refine ⟨by norm_num, by norm_num, (2 * j + 1 : ℤ), ?_⟩
  push_cast
  ring

noncomputable def dyadic (n : ℕ) : ℝ := (1 / 4) * (1 / 2) ^ n

theorem dyadic_zero : dyadic 0 = 1 / 4 := by norm_num [dyadic]

theorem dyadic_positive (n : ℕ) : 0 < dyadic n := by
  unfold dyadic
  positivity

theorem dyadic_half (n : ℕ) : dyadic (n + 1) = dyadic n / 2 := by
  simp only [dyadic, pow_succ]
  ring

theorem dyadic_tendsto : Tendsto dyadic atTop (𝓝 (0 : ℝ)) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (1 / 4 : ℝ)
  change Tendsto (fun n : ℕ => (1 / 4 : ℝ) * (1 / 2) ^ n) atTop (𝓝 0)
  simpa only [mul_zero] using h

theorem dyadic_comparison_obstruction (h : ℝ → ℝ) (hcont : ContinuousAt h 0)
    (hanchor : h 0 < h (1 / 4))
    (hstep : ∀ n : ℕ, h (dyadic n) ≤ h (dyadic (n + 1))) : False := by
  have lower (n : ℕ) : h (1 / 4) ≤ h (dyadic n) := by
    induction n with
    | zero => simp only [dyadic_zero, le_refl]
    | succ n ih => exact ih.trans (hstep n)
  have ht : Tendsto (fun n => h (dyadic n)) atTop (𝓝 (h 0)) := hcont.tendsto.comp dyadic_tendsto
  have hlim : h (1 / 4) ≤ h 0 := ge_of_tendsto' ht lower
  exact (not_lt_of_ge hlim) hanchor

theorem dyadic_strict_obstruction (h : ℝ → ℝ) (hcont : ContinuousAt h 0)
    (hanchor : h 0 < h (1 / 4))
    (hstep : ∀ n : ℕ, h (dyadic n) < h (dyadic (n + 1))) : False :=
  dyadic_comparison_obstruction h hcont hanchor (fun n => (hstep n).le)

theorem dyadic_mesh_not_divisible_three (n : ℕ) : ¬ 3 ∣ 2 ^ n := by
  intro h
  have hc : Nat.Coprime (2 ^ n) 3 := (by decide : Nat.Coprime 2 3).pow_left n
  have := hc.gcd_eq_one
  rw [Nat.gcd_eq_right h] at this
  norm_num at this

theorem positive_reciprocal_strict (M : ℝ) (hM : 0 < M) :
    1 / (2 / M) < 1 / (1 / M) := by
  field_simp
  linarith

end RematCompactFamily

#print axioms RematCompactFamily.anchor_first_fraction
#print axioms RematCompactFamily.anchor_second_fraction
#print axioms RematCompactFamily.anchor_third_fraction
#print axioms RematCompactFamily.residue_one_first_fraction
#print axioms RematCompactFamily.residue_one_other_fraction
#print axioms RematCompactFamily.residue_two_fraction
#print axioms RematCompactFamily.dyadic_zero
#print axioms RematCompactFamily.dyadic_positive
#print axioms RematCompactFamily.dyadic_half
#print axioms RematCompactFamily.dyadic_tendsto
#print axioms RematCompactFamily.dyadic_comparison_obstruction
#print axioms RematCompactFamily.dyadic_strict_obstruction
#print axioms RematCompactFamily.dyadic_mesh_not_divisible_three
#print axioms RematCompactFamily.positive_reciprocal_strict
end

section
set_option autoImplicit true
set_option autoImplicit false

open scoped BigOperators

namespace RematCompactTransfer

noncomputable section

def anchorTarget : Fin 3 → ℝ := ![31 / 36, 4 / 36, 1 / 36]

def firstTarget : Fin 6 → ℝ := fun i => if i = 0 then 7 / 12 else 1 / 12

def secondTarget : Fin 6 → ℝ := fun _ => 1 / 6

theorem target_positive_sum :
    (∀ i, 0 < anchorTarget i) ∧ (∑ i, anchorTarget i = 1) ∧
    (∀ i, 0 < firstTarget i) ∧ (∑ i, firstTarget i = 1) ∧
    (∀ i, 0 < secondTarget i) ∧ (∑ i, secondTarget i = 1) := by
  norm_num [anchorTarget, firstTarget, secondTarget, Fin.sum_univ_succ]
  constructor
  · intro i; fin_cases i <;> norm_num
  · intro i; split_ifs <;> norm_num

theorem anchor_profile (i : Fin 3) :
    RematRounding.fraction (fun k => (4 : ℝ) * anchorTarget k) i =
      if i = 2 then 1 / 9 else 4 / 9 := by
  fin_cases i <;> norm_num [RematRounding.fraction, RematRounding.base, anchorTarget, Fin.ext_iff]

theorem first_profile (j : ℕ) (i : Fin 6) :
    RematRounding.fraction (fun k => (4 * (4 + 3 * j) : ℕ) * firstTarget k) i = 1 / 3 := by
  have hfirst : Int.fract ((4 * (4 + 3 * (j : ℝ))) * (7 / 12)) = (1 / 3 : ℝ) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (RematCompactFamily.residue_one_first_fraction j)
    push_cast at h
    exact h
  have hother : Int.fract ((4 * (4 + 3 * (j : ℝ))) * (1 / 12)) = (1 / 3 : ℝ) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (RematCompactFamily.residue_one_other_fraction j)
    push_cast at h
    exact h
  change Int.fract (_ * firstTarget i) = _
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  by_cases hi : i = 0
  · simpa only [firstTarget, if_pos hi] using hfirst
  · simpa only [firstTarget, if_neg hi] using hother

theorem second_profile (j : ℕ) (i : Fin 6) :
    RematRounding.fraction (fun k => (4 * (2 + 3 * j) : ℕ) * secondTarget k) i = 1 / 3 := by
  have h : Int.fract ((4 * (2 + 3 * (j : ℝ))) * (1 / 6)) = (1 / 3 : ℝ) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (RematCompactFamily.residue_two_fraction j)
    push_cast at h
    exact h
  change Int.fract (_ * (1 / 6 : ℝ)) = _
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using h


theorem scaled_sum {N : ℕ} (a : Fin N → ℝ) (ha : ∑ i, a i = 1) (M : ℤ) :
    ∑ i, (M : ℝ) * a i = M := by
  rw [← Finset.mul_sum, ha, mul_one]

theorem capacity_from_profile {N : ℕ} (a : Fin N → ℝ) (ha : ∑ i, a i = 1)
    (M : ℤ) (t : ℕ) (hf : ∑ i, RematRounding.fraction (fun k => (M : ℝ) * a k) i = t) :
    RematRounding.capacity M (fun k => (M : ℝ) * a k) = t := by
  have h := RematRounding.fraction_sum M (fun k => (M : ℝ) * a k) (scaled_sum a ha M)
  rw [hf] at h
  exact_mod_cast h.symm

theorem anchor_comparison (φ : ℝ → ℝ)
    (ho : RematTransfer.gridExactIndex φ 4 anchorTarget 1) :
    φ 0 < φ (1 / 4) - (1 / 9 : ℝ) * (1 / 4) ^ 2 := by
  have hp := target_positive_sum
  have hcap : RematRounding.capacity 4 (fun i => (4 : ℝ) * anchorTarget i) = 1 := by
    apply capacity_from_profile anchorTarget hp.2.1 4 1
    norm_num [RematRounding.fraction, RematRounding.base, anchorTarget, Fin.sum_univ_succ]
  have hf : ∀ i, RematRounding.fraction (fun k => (4 : ℝ) * anchorTarget k) i ≤
      (1 - (1 / 9 : ℝ) * (2 * (1 : ℝ) - 1)) / 2 := by
    intro i
    rw [anchor_profile]
    split_ifs <;> norm_num
  have hmax : RematRounding.fraction (fun k => (4 : ℝ) * anchorTarget k) 0 =
      (1 - (1 / 9 : ℝ) * (2 * (1 : ℝ) - 1)) / 2 := by
    rw [anchor_profile]
    norm_num [Fin.ext_iff]
  have hn := RematTransfer.arbitrary_loss_observation_necessity (1 / 9) φ 4 (by norm_num)
    (fun k => (4 : ℝ) * anchorTarget k) (fun i => mul_nonneg (by norm_num) (hp.1 i).le)
    (scaled_sum anchorTarget hp.2.1 4) 1 (by norm_num) hcap 0 (by norm_num) (by simpa using hf) (by simpa using hmax)
  have h := hn.2.2.2 ((RematTransfer.grid_observation_iff φ 4 (by norm_num) anchorTarget 1).2.mp ho)
  norm_num at h ⊢
  exact h

theorem uniform_six_comparison (φ : ℝ → ℝ) (M : ℤ) (hM : 0 < M)
    (a : Fin 6 → ℝ) (ha : ∀ i, 0 < a i) (hs : ∑ i, a i = 1)
    (hf : ∀ i, RematRounding.fraction (fun k => (M : ℝ) * a k) i = 1 / 3)
    (ho : RematTransfer.gridOccurs φ M a 0) :
    φ (2 / M) - (1 / 9 : ℝ) * (2 / M) ^ 2 ≤
      φ (1 / M) - (1 / 9 : ℝ) * (1 / M) ^ 2 := by
  have hcap : RematRounding.capacity M (fun i => (M : ℝ) * a i) = 2 := by
    apply capacity_from_profile a hs M 2
    simp only [hf, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  have hbound : ∀ i, RematRounding.fraction (fun k => (M : ℝ) * a k) i ≤
      (1 - (1 / 9 : ℝ) * (2 * (2 : ℝ) - 1)) / 2 := by
    intro i
    rw [hf]
    norm_num
  have hmax : RematRounding.fraction (fun k => (M : ℝ) * a k) 0 =
      (1 - (1 / 9 : ℝ) * (2 * (2 : ℝ) - 1)) / 2 := by
    rw [hf]
    norm_num
  have hn := RematTransfer.arbitrary_loss_observation_necessity (1 / 9) φ M hM
    (fun k => (M : ℝ) * a k) (fun i => mul_nonneg (by exact_mod_cast hM.le) (ha i).le)
    (scaled_sum a hs M) 2 (by norm_num) hcap 0 (by norm_num) hbound hmax
  have h := hn.1 ((RematTransfer.grid_observation_iff φ M hM a 0).1.mp ho)
  norm_num at h ⊢
  exact h

theorem first_comparison (φ : ℝ → ℝ) (j : ℕ)
    (ho : RematTransfer.gridOccurs φ (4 * (4 + 3 * j)) firstTarget 0) :
    φ (2 / (4 * (4 + 3 * (j : ℝ)))) - (1 / 9 : ℝ) * (2 / (4 * (4 + 3 * (j : ℝ)))) ^ 2 ≤
      φ (1 / (4 * (4 + 3 * (j : ℝ)))) - (1 / 9 : ℝ) * (1 / (4 * (4 + 3 * (j : ℝ)))) ^ 2 := by
  have hp := target_positive_sum
  have h := uniform_six_comparison φ (4 * (4 + 3 * j)) (by positivity) firstTarget
    hp.2.2.1 hp.2.2.2.1 (by intro i; simpa using first_profile j i) ho
  simpa only [Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_natCast] using h

theorem second_comparison (φ : ℝ → ℝ) (j : ℕ)
    (ho : RematTransfer.gridOccurs φ (4 * (2 + 3 * j)) secondTarget 0) :
    φ (2 / (4 * (2 + 3 * (j : ℝ)))) - (1 / 9 : ℝ) * (2 / (4 * (2 + 3 * (j : ℝ)))) ^ 2 ≤
      φ (1 / (4 * (2 + 3 * (j : ℝ)))) - (1 / 9 : ℝ) * (1 / (4 * (2 + 3 * (j : ℝ)))) ^ 2 := by
  have hp := target_positive_sum
  have h := uniform_six_comparison φ (4 * (2 + 3 * j)) (by positivity) secondTarget
    hp.2.2.2.2.1 hp.2.2.2.2.2 (by intro i; simpa using second_profile j i) ho
  simpa only [Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_natCast] using h


theorem progression_cover (m : ℕ) (hm : 2 ≤ m) (hnot : ¬3 ∣ m) :
    (∃ j : ℕ, m = 4 + 3 * j) ∨ (∃ j : ℕ, m = 2 + 3 * j) := by
  have hmod := Nat.mod_lt m (by decide : 0 < 3)
  have hn : m % 3 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hnot
  have hd := Nat.mod_add_div m 3
  by_cases h : m % 3 = 1
  · left
    refine ⟨m / 3 - 1, ?_⟩
    omega
  · right
    exact ⟨m / 3, by omega⟩

theorem dyadic_ratio (n : ℕ) :
    RematCompactFamily.dyadic n = 2 / (4 * (2 : ℝ) ^ (n + 1)) := by
  simp only [RematCompactFamily.dyadic, div_pow, one_pow, pow_succ]
  field_simp

theorem dyadic_ratio_next (n : ℕ) :
    RematCompactFamily.dyadic (n + 1) = 1 / (4 * (2 : ℝ) ^ (n + 1)) := by
  rw [RematCompactFamily.dyadic_half, dyadic_ratio]
  ring

theorem dyadic_from_observations (φ : ℝ → ℝ)
    (ho₁ : ∀ j : ℕ, RematTransfer.gridOccurs φ (4 * (4 + 3 * j)) firstTarget 0)
    (ho₂ : ∀ j : ℕ, RematTransfer.gridOccurs φ (4 * (2 + 3 * j)) secondTarget 0) :
    ∀ n : ℕ, φ (RematCompactFamily.dyadic n) - (1 / 9 : ℝ) * (RematCompactFamily.dyadic n) ^ 2 ≤
      φ (RematCompactFamily.dyadic (n + 1)) - (1 / 9 : ℝ) * (RematCompactFamily.dyadic (n + 1)) ^ 2 := by
  intro n
  have htwo : 2 ≤ 2 ^ (n + 1) := by
    have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) n
    rw [pow_succ]
    omega
  have hc := progression_cover (2 ^ (n + 1)) htwo
    (RematCompactFamily.dyadic_mesh_not_divisible_three (n + 1))
  rw [dyadic_ratio, dyadic_ratio_next]
  rcases hc with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hr : (2 : ℝ) ^ (n + 1) = 4 + 3 * (j : ℝ) := by exact_mod_cast hj
    rw [hr]
    exact first_comparison φ j (ho₁ j)
  · have hr : (2 : ℝ) ^ (n + 1) = 2 + 3 * (j : ℝ) := by exact_mod_cast hj
    rw [hr]
    exact second_comparison φ j (ho₂ j)

theorem compact_no_continuous_loss (φ : ℝ → ℝ) (hφ : ContinuousAt φ 0)
    (ho₀ : RematTransfer.gridExactIndex φ 4 anchorTarget 1)
    (ho₁ : ∀ j : ℕ, RematTransfer.gridOccurs φ (4 * (4 + 3 * j)) firstTarget 0)
    (ho₂ : ∀ j : ℕ, RematTransfer.gridOccurs φ (4 * (2 + 3 * j)) secondTarget 0) : False := by
  let h : ℝ → ℝ := fun s => φ s - (1 / 9 : ℝ) * s ^ 2
  have hc : ContinuousAt h 0 := hφ.sub (continuousAt_const.mul (continuousAt_id.pow 2))
  apply RematCompactFamily.dyadic_comparison_obstruction h hc
  · simpa only [h, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] using anchor_comparison φ ho₀
  · exact dyadic_from_observations φ ho₁ ho₂

theorem compact_no_continuous_strict_loss (φ : ℝ → ℝ) (hφ : ContinuousAt φ 0)
    (ho₀ : ∀ j : ℕ, RematTransfer.gridExactIndex φ (4 * (1 + 9 * j)) anchorTarget 1)
    (ho₁ : ∀ j : ℕ, RematTransfer.gridExactIndex φ (4 * (4 + 3 * j)) firstTarget 0)
    (ho₂ : ∀ j : ℕ, RematTransfer.gridExactIndex φ (4 * (2 + 3 * j)) secondTarget 0) : False := by
  apply compact_no_continuous_loss φ hφ
  · simpa using ho₀ 0
  · exact fun j => (ho₁ j).1
  · exact fun j => (ho₂ j).1

end

end RematCompactTransfer

#print axioms RematCompactTransfer.target_positive_sum
#print axioms RematCompactTransfer.anchor_profile
#print axioms RematCompactTransfer.first_profile
#print axioms RematCompactTransfer.second_profile
#print axioms RematCompactTransfer.scaled_sum
#print axioms RematCompactTransfer.capacity_from_profile
#print axioms RematCompactTransfer.anchor_comparison
#print axioms RematCompactTransfer.uniform_six_comparison
#print axioms RematCompactTransfer.first_comparison
#print axioms RematCompactTransfer.second_comparison
#print axioms RematCompactTransfer.progression_cover
#print axioms RematCompactTransfer.dyadic_ratio
#print axioms RematCompactTransfer.dyadic_ratio_next
#print axioms RematCompactTransfer.dyadic_from_observations
#print axioms RematCompactTransfer.compact_no_continuous_loss
#print axioms RematCompactTransfer.compact_no_continuous_strict_loss
end

section
set_option autoImplicit true
set_option autoImplicit false

open scoped BigOperators ContDiff
open RematCompactTransfer RematOrderBridge

namespace RematCompactFinite

noncomputable section

theorem anchor_full_profile (j : ℕ) (i : Fin 3) :
    RematRounding.fraction (fun k => (4 * (1 + 9 * j) : ℕ) * anchorTarget k) i =
      if i = 2 then 1 / 9 else 4 / 9 := by
  have h₁ := congrArg (fun x : ℚ => (x : ℝ)) (RematCompactFamily.anchor_first_fraction j)
  have h₂ := congrArg (fun x : ℚ => (x : ℝ)) (RematCompactFamily.anchor_second_fraction j)
  have h₃ := congrArg (fun x : ℚ => (x : ℝ)) (RematCompactFamily.anchor_third_fraction j)
  push_cast at h₁ h₂ h₃
  change Int.fract (_ * anchorTarget i) = _
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  fin_cases i
  · simpa [anchorTarget, Fin.ext_iff] using h₁
  · simpa [anchorTarget, Fin.ext_iff] using h₂
  · simpa [anchorTarget, Fin.ext_iff] using h₃

theorem smooth_derivative_data (h : ℝ → ℝ) (hsm : ContDiff ℝ ∞ h) :
    (∀ x, HasDerivAt h (iteratedDeriv 1 h x) x) ∧
      ∀ x, HasDerivAt (iteratedDeriv 1 h) (iteratedDeriv 2 h x) x := by
  constructor
  · intro x
    have hd := (hsm.differentiable_iteratedDeriv 0 (by simp)).differentiableAt.hasDerivAt (x := x)
    simpa only [iteratedDeriv_zero, iteratedDeriv_one] using hd
  · intro x
    have hd := (hsm.differentiable_iteratedDeriv 1 (by simp)).differentiableAt.hasDerivAt (x := x)
    simpa only [iteratedDeriv_succ] using hd

theorem profile_smooth_transfer {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (hs : ∑ i, a i = 1) (M : ℤ) (hM : 0 < M) (t : ℕ) (ht : 0 < t)
    (htT : t ≤ 2) (htM : (t : ℤ) ≤ M)
    (hcap : RematRounding.capacity M (fun i => (M : ℝ) * a i) = t)
    (hf : ∀ i, RematRounding.fraction (fun k => (M : ℝ) * a k) i ≤
      (1 - (1 / 9 : ℝ) * (2 * t - 1)) / 2)
    (i₀ : Fin N) (hmax : RematRounding.fraction (fun k => (M : ℝ) * a k) i₀ =
      (1 - (1 / 9 : ℝ) * (2 * t - 1)) / 2)
    (eps : ℝ) (heps : 0 ≤ eps) (hsmall : eps < 1 / 36)
    (h : ℝ → ℝ) (hsm : ContDiff ℝ ∞ h) (hjet : ∀ k, iteratedDeriv k h 0 = 0)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ eps) :
    (RematTransfer.gridExactIndex (fun s => (1 / 9 : ℝ) * s ^ 2 + h s) M a 0 ↔
      h ((t : ℝ) / M) < h (((t : ℝ) - 1) / M)) ∧
    (RematTransfer.gridExactIndex (fun s => (1 / 9 : ℝ) * s ^ 2 + h s) M a 1 ↔
      h (((t : ℝ) - 1) / M) < h ((t : ℝ) / M)) := by
  have hd := smooth_derivative_data h hsm
  have hz : h 0 = 0 := by simpa only [iteratedDeriv_zero] using hjet 0
  have ht := RematTransfer.c2_all_vector_transfer (1 / 9) eps (by norm_num) heps M hM
    (fun i => (M : ℝ) * a i) (fun i => mul_nonneg (by exact_mod_cast hM.le) (ha i).le)
    (scaled_sum a hs M) t 2 ht htT htM hcap (by norm_num; exact hsmall) hf i₀ hmax
    h (iteratedDeriv 1 h) (iteratedDeriv 2 h) (fun x _ => hd.1 x) (fun x _ => hd.2 x)
    hz (hjet 1) (fun x _ => hb 2 (by decide) x)
  exact ⟨(RematTransfer.grid_observation_iff _ M hM a 0).2.trans ht.2.2.2.1,
    (RematTransfer.grid_observation_iff _ M hM a 1).2.trans ht.2.2.2.2.1⟩


theorem anchor_smooth_transfer (j : ℕ) (eps : ℝ) (heps : 0 ≤ eps) (hsmall : eps < 1 / 36)
    (h : ℝ → ℝ) (hsm : ContDiff ℝ ∞ h) (hjet : ∀ k, iteratedDeriv k h 0 = 0)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ eps) :
    RematTransfer.gridExactIndex (fun s => (1 / 9 : ℝ) * s ^ 2 + h s)
      (4 * (1 + 9 * j)) anchorTarget 1 ↔ h 0 < h (1 / (4 * (1 + 9 * (j : ℝ)))) := by
  have hp := target_positive_sum
  have hf : ∀ i, RematRounding.fraction (fun k => ((4 * (1 + 9 * j) : ℤ) : ℝ) * anchorTarget k) i =
      if i = 2 then 1 / 9 else 4 / 9 := by
    intro i
    simpa using anchor_full_profile j i
  have hcap : RematRounding.capacity (4 * (1 + 9 * j))
      (fun k => ((4 * (1 + 9 * j) : ℤ) : ℝ) * anchorTarget k) = 1 := by
    apply capacity_from_profile anchorTarget hp.2.1 _ 1
    simp only [hf]
    norm_num [Fin.sum_univ_succ, Fin.ext_iff]
  have hh := profile_smooth_transfer anchorTarget hp.1 hp.2.1 (4 * (1 + 9 * j)) (by positivity)
    1 (by decide) (by decide) (by omega) hcap
    (by intro i; rw [hf]; split_ifs <;> norm_num) 0 (by rw [hf]; norm_num [Fin.ext_iff])
    eps heps hsmall h hsm hjet hb
  simpa using hh.2

theorem uniform_six_smooth_transfer (M : ℤ) (hM : 2 ≤ M) (a : Fin 6 → ℝ)
    (ha : ∀ i, 0 < a i) (hs : ∑ i, a i = 1)
    (hf : ∀ i, RematRounding.fraction (fun k => (M : ℝ) * a k) i = 1 / 3)
    (eps : ℝ) (heps : 0 ≤ eps) (hsmall : eps < 1 / 36)
    (h : ℝ → ℝ) (hsm : ContDiff ℝ ∞ h) (hjet : ∀ k, iteratedDeriv k h 0 = 0)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ eps) :
    RematTransfer.gridExactIndex (fun s => (1 / 9 : ℝ) * s ^ 2 + h s) M a 0 ↔
      h (2 / M) < h (1 / M) := by
  have hcap : RematRounding.capacity M (fun k => (M : ℝ) * a k) = 2 := by
    apply capacity_from_profile a hs M 2
    simp only [hf, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  have hh := profile_smooth_transfer a ha hs M (by omega) 2 (by decide) (by decide) hM hcap
    (by intro i; rw [hf]; norm_num) 0 (by rw [hf]; norm_num)
    eps heps hsmall h hsm hjet hb
  simpa [show (2 : ℝ) - 1 = 1 by norm_num] using hh.1

theorem first_smooth_transfer (j : ℕ) (eps : ℝ) (heps : 0 ≤ eps) (hsmall : eps < 1 / 36)
    (h : ℝ → ℝ) (hsm : ContDiff ℝ ∞ h) (hjet : ∀ k, iteratedDeriv k h 0 = 0)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ eps) :
    RematTransfer.gridExactIndex (fun s => (1 / 9 : ℝ) * s ^ 2 + h s)
      (4 * (4 + 3 * j)) firstTarget 0 ↔
      h (2 / (4 * (4 + 3 * (j : ℝ)))) < h (1 / (4 * (4 + 3 * (j : ℝ)))) := by
  have hp := target_positive_sum
  have hh := uniform_six_smooth_transfer (4 * (4 + 3 * j)) (by omega) firstTarget
    hp.2.2.1 hp.2.2.2.1 (by intro i; simpa using first_profile j i)
    eps heps hsmall h hsm hjet hb
  simpa using hh

theorem second_smooth_transfer (j : ℕ) (eps : ℝ) (heps : 0 ≤ eps) (hsmall : eps < 1 / 36)
    (h : ℝ → ℝ) (hsm : ContDiff ℝ ∞ h) (hjet : ∀ k, iteratedDeriv k h 0 = 0)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ eps) :
    RematTransfer.gridExactIndex (fun s => (1 / 9 : ℝ) * s ^ 2 + h s)
      (4 * (2 + 3 * j)) secondTarget 0 ↔
      h (2 / (4 * (2 + 3 * (j : ℝ)))) < h (1 / (4 * (2 + 3 * (j : ℝ)))) := by
  have hp := target_positive_sum
  have hh := uniform_six_smooth_transfer (4 * (2 + 3 * j)) (by omega) secondTarget
    hp.2.2.2.2.1 hp.2.2.2.2.2 (by intro i; simpa using second_profile j i)
    eps heps hsmall h hsm hjet hb
  simpa using hh


def sampleValue (t M : ℕ) (ht : t ≤ 2) (htM : t ≤ M) : Sample 2 :=
  ⟨(t : ℝ) / M, fraction_mem_samples 2 t M ht htM⟩

def anchorSample (j : ℕ) : Sample 2 := sampleValue 1 (4 * (1 + 9 * j)) (by decide) (by omega)
def firstLarge (j : ℕ) : Sample 2 := sampleValue 2 (4 * (4 + 3 * j)) (by decide) (by omega)
def firstSmall (j : ℕ) : Sample 2 := sampleValue 1 (4 * (4 + 3 * j)) (by decide) (by omega)
def secondLarge (j : ℕ) : Sample 2 := sampleValue 2 (4 * (2 + 3 * j)) (by decide) (by omega)
def secondSmall (j : ℕ) : Sample 2 := sampleValue 1 (4 * (2 + 3 * j)) (by decide) (by omega)

def compactEdges (A B C : Finset ℕ) : Finset (Sample 2 × Sample 2) := by
  classical
  exact A.image (fun j => (origin 2, anchorSample j)) ∪
    B.image (fun j => (firstLarge j, firstSmall j)) ∪
    C.image (fun j => (secondLarge j, secondSmall j))

theorem reciprocal_edge (A B C : Finset ℕ) (x y : Sample 2)
    (he : (x, y) ∈ compactEdges A B C) : (x : ℝ)⁻¹ < (y : ℝ)⁻¹ := by
  classical
  rcases Finset.mem_union.mp he with hab | hc
  · rcases Finset.mem_union.mp hab with ha | hb
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ha
      have hx := congrArg Prod.fst hj
      have hy := congrArg Prod.snd hj
      dsimp at hx hy
      rw [← hx, ← hy]
      simp only [origin, anchorSample, sampleValue, Nat.cast_one, inv_zero]
      positivity
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
      have hx := congrArg Prod.fst hj
      have hy := congrArg Prod.snd hj
      dsimp at hx hy
      rw [← hx, ← hy]
      simpa [firstLarge, firstSmall, sampleValue] using RematCompactFamily.positive_reciprocal_strict
        ((4 * (4 + 3 * j) : ℕ) : ℝ) (by positivity)
  · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
    have hx := congrArg Prod.fst hj
    have hy := congrArg Prod.snd hj
    dsimp at hx hy
    rw [← hx, ← hy]
    simpa [secondLarge, secondSmall, sampleValue] using RematCompactFamily.positive_reciprocal_strict
      ((4 * (2 + 3 * j) : ℕ) : ℝ) (by positivity)

theorem finite_sample_labels (A B C : Finset ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ eps) ∧
      (∀ j ∈ A, h 0 < h (1 / (4 * (1 + 9 * (j : ℝ))))) ∧
      (∀ j ∈ B, h (2 / (4 * (4 + 3 * (j : ℝ)))) < h (1 / (4 * (4 + 3 * (j : ℝ))))) ∧
      (∀ j ∈ C, h (2 / (4 * (2 + 3 * (j : ℝ)))) < h (1 / (4 * (2 + 3 * (j : ℝ))))) := by
  classical
  let e := compactEdges A B C
  let s := e.biUnion (fun p => {p.1, p.2})
  let E := fun x y : Sample 2 => (x, y) ∈ e
  have hs : ∀ x y : Sample 2, False ∨ E x y → x ∈ s ∧ y ∈ s := by
    intro x y hxy
    rcases hxy with hf | he
    · exact hf.elim
    · constructor
      · exact Finset.mem_biUnion.mpr ⟨(x, y), he, by simp⟩
      · exact Finset.mem_biUnion.mpr ⟨(x, y), he, by simp⟩
  obtain ⟨h, hsm, _, hjet, hb, _, hlabels⟩ := finite_relations_smooth 2 (by decide)
    (fun _ _ => False) E s hs (fun x => (x : ℝ)⁻¹) (by simp [origin])
    (fun _ _ hf => hf.elim) (reciprocal_edge A B C) eps heps
  refine ⟨h, hsm, hjet, hb, ?_, ?_, ?_⟩
  · intro j hj
    have hh := hlabels (origin 2) (anchorSample j)
      (by simp only [E, e, compactEdges]; exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)))
    simpa [origin, anchorSample, sampleValue] using hh
  · intro j hj
    have hh := hlabels (firstLarge j) (firstSmall j)
      (by simp only [E, e, compactEdges]; exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)))
    simpa [firstLarge, firstSmall, sampleValue] using hh
  · intro j hj
    have hh := hlabels (secondLarge j) (secondSmall j)
      (by simp only [E, e, compactEdges]; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
    simpa [secondLarge, secondSmall, sampleValue] using hh


theorem finite_compact_realization (A B C : Finset ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∀ k : ℕ, k ≤ 2 → ∀ x, |iteratedDeriv k h x| ≤ eta) ∧
      MonotoneOn (fun s => (1 / 9 : ℝ) * s ^ 2 + h s) (Set.Icc 0 1) ∧
      ConvexOn ℝ (Set.Icc 0 1) (fun s => ((1 / 9 : ℝ) * s ^ 2 + h s) - (1 / 18 : ℝ) * s ^ 2) ∧
      (∀ j ∈ A, RematTransfer.gridExactIndex (fun s => (1 / 9 : ℝ) * s ^ 2 + h s)
        (4 * (1 + 9 * j)) anchorTarget 1) ∧
      (∀ j ∈ B, RematTransfer.gridExactIndex (fun s => (1 / 9 : ℝ) * s ^ 2 + h s)
        (4 * (4 + 3 * j)) firstTarget 0) ∧
      (∀ j ∈ C, RematTransfer.gridExactIndex (fun s => (1 / 9 : ℝ) * s ^ 2 + h s)
        (4 * (2 + 3 * j)) secondTarget 0) := by
  let eps := min (eta / 2) (1 / 72)
  have heps : 0 < eps := lt_min (by positivity) (by norm_num)
  have hepseta : eps ≤ eta := (min_le_left _ _).trans (by linarith)
  have hsmall : eps < 1 / 36 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨h, hsm, hjet, hb, ha, h₁, h₂⟩ := finite_sample_labels A B C eps heps
  have hd := smooth_derivative_data h hsm
  refine ⟨h, hsm, hjet, fun k hk x => (hb k hk x).trans hepseta, ?_, ?_, ?_, ?_, ?_⟩
  · exact RematTransfer.perturbed_penalty_monotone (1 / 9) eps (by norm_num) (by linarith)
      h (iteratedDeriv 1 h) (iteratedDeriv 2 h) (fun x _ => hd.1 x) (fun x _ => hd.2 x)
      (hjet 1) (fun x _ => hb 2 (by decide) x)
  · have hc := RematTransfer.perturbed_quantitative_convexity (1 / 9) eps (by linarith)
      h (iteratedDeriv 1 h) (iteratedDeriv 2 h) (fun x _ => hd.1 x) (fun x _ => hd.2 x)
      (fun x _ => hb 2 (by decide) x)
    norm_num at hc ⊢
    exact hc
  · exact fun j hj => (anchor_smooth_transfer j eps heps.le hsmall h hsm hjet hb).mpr (ha j hj)
  · exact fun j hj => (first_smooth_transfer j eps heps.le hsmall h hsm hjet hb).mpr (h₁ j hj)
  · exact fun j hj => (second_smooth_transfer j eps heps.le hsmall h hsm hjet hb).mpr (h₂ j hj)

end

end RematCompactFinite

#print axioms RematCompactFinite.anchor_full_profile
#print axioms RematCompactFinite.smooth_derivative_data
#print axioms RematCompactFinite.profile_smooth_transfer
#print axioms RematCompactFinite.anchor_smooth_transfer
#print axioms RematCompactFinite.uniform_six_smooth_transfer
#print axioms RematCompactFinite.first_smooth_transfer
#print axioms RematCompactFinite.second_smooth_transfer
#print axioms RematCompactFinite.reciprocal_edge
#print axioms RematCompactFinite.finite_sample_labels
#print axioms RematCompactFinite.finite_compact_realization
end

section
set_option autoImplicit true
set_option autoImplicit false

open scoped BigOperators

namespace RematIntervalTransfer

noncomputable section

theorem feasible_residual_mem {N : ℕ} (M : ℤ) (d : Fin N → ℝ) (hd : RematGrid.feasible M d) :
    1 - ∑ i, d i ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : 0 ≤ ∑ i, d i := Finset.sum_nonneg (fun i _ => hd.1 i)
  exact ⟨sub_nonneg.mpr hd.2.1, by linarith⟩

theorem grid_loss_congr {N : ℕ} (φ ψ : ℝ → ℝ)
    (he : ∀ x ∈ Set.Icc (0 : ℝ) 1, φ x = ψ x) (M : ℤ) (a d : Fin N → ℝ)
    (hd : RematGrid.feasible M d) :
    RematGeneralResidual.gridLoss φ a d = RematGeneralResidual.gridLoss ψ a d := by
  unfold RematGeneralResidual.gridLoss
  rw [he _ (feasible_residual_mem M d hd)]

theorem grid_minimum_congr {N : ℕ} (φ ψ : ℝ → ℝ)
    (he : ∀ x ∈ Set.Icc (0 : ℝ) 1, φ x = ψ x) (M : ℤ) (a d : Fin N → ℝ) :
    RematGeneralResidual.gridMinimum φ M a d ↔ RematGeneralResidual.gridMinimum ψ M a d := by
  constructor
  · intro hd
    refine ⟨hd.1, fun e hfe => ?_⟩
    rw [← grid_loss_congr φ ψ he M a d hd.1, ← grid_loss_congr φ ψ he M a e hfe]
    exact hd.2 e hfe
  · intro hd
    refine ⟨hd.1, fun e hfe => ?_⟩
    rw [grid_loss_congr φ ψ he M a d hd.1, grid_loss_congr φ ψ he M a e hfe]
    exact hd.2 e hfe

theorem grid_observation_congr {N : ℕ} (φ ψ : ℝ → ℝ)
    (he : ∀ x ∈ Set.Icc (0 : ℝ) 1, φ x = ψ x) (M : ℤ) (a : Fin N → ℝ) (j : ℤ) :
    (RematTransfer.gridOccurs φ M a j ↔ RematTransfer.gridOccurs ψ M a j) ∧
    (RematTransfer.gridExactIndex φ M a j ↔ RematTransfer.gridExactIndex ψ M a j) := by
  simp only [RematTransfer.gridOccurs, RematTransfer.gridExactIndex,
    grid_minimum_congr φ ψ he]
  trivial

theorem interval_representative (u : Set.Icc (0 : ℝ) 1 → ℝ)
    (hu : ContinuousAt u ⟨0, by norm_num⟩) (φ : ℝ → ℝ)
    (hφ : ∀ x : Set.Icc (0 : ℝ) 1, φ (x : ℝ) = u x) :
    ∃ ψ : ℝ → ℝ, ContinuousAt ψ 0 ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, φ x = ψ x) ∧
      (∀ (N : ℕ) (M : ℤ) (a d : Fin N → ℝ),
        RematGeneralResidual.gridMinimum φ M a d ↔ RematGeneralResidual.gridMinimum ψ M a d) ∧
      ∀ (N : ℕ) (M : ℤ) (a : Fin N → ℝ) (j : ℤ),
        (RematTransfer.gridOccurs φ M a j ↔ RematTransfer.gridOccurs ψ M a j) ∧
        (RematTransfer.gridExactIndex φ M a j ↔ RematTransfer.gridExactIndex ψ M a j) := by
  obtain ⟨ψ, hψ, he⟩ := RematOrderBridge.continuous_subtype_extension_at_zero
    (Set.Icc (0 : ℝ) 1) (by norm_num) u hu
  have hagree : ∀ x ∈ Set.Icc (0 : ℝ) 1, φ x = ψ x := by
    intro x hx
    exact (hφ ⟨x, hx⟩).trans (he ⟨x, hx⟩).symm
  exact ⟨ψ, hψ, hagree, fun _ M a d => grid_minimum_congr φ ψ hagree M a d,
    fun _ M a j => grid_observation_congr φ ψ hagree M a j⟩

theorem compact_no_interval_loss (u : Set.Icc (0 : ℝ) 1 → ℝ)
    (hu : ContinuousAt u ⟨0, by norm_num⟩) (φ : ℝ → ℝ)
    (hφ : ∀ x : Set.Icc (0 : ℝ) 1, φ (x : ℝ) = u x)
    (ho₀ : RematTransfer.gridExactIndex φ 4 RematCompactTransfer.anchorTarget 1)
    (ho₁ : ∀ j : ℕ, RematTransfer.gridOccurs φ (4 * (4 + 3 * j)) RematCompactTransfer.firstTarget 0)
    (ho₂ : ∀ j : ℕ, RematTransfer.gridOccurs φ (4 * (2 + 3 * j)) RematCompactTransfer.secondTarget 0) :
    False := by
  obtain ⟨ψ, hψ, _, _, ho⟩ := interval_representative u hu φ hφ
  exact RematCompactTransfer.compact_no_continuous_loss ψ hψ
    ((ho 3 4 RematCompactTransfer.anchorTarget 1).2.mp ho₀)
    (fun j => (ho 6 _ RematCompactTransfer.firstTarget 0).1.mp (ho₁ j))
    (fun j => (ho 6 _ RematCompactTransfer.secondTarget 0).1.mp (ho₂ j))

end

end RematIntervalTransfer

#print axioms RematIntervalTransfer.feasible_residual_mem
#print axioms RematIntervalTransfer.grid_loss_congr
#print axioms RematIntervalTransfer.grid_minimum_congr
#print axioms RematIntervalTransfer.grid_observation_congr
#print axioms RematIntervalTransfer.interval_representative
#print axioms RematIntervalTransfer.compact_no_interval_loss
end

section
set_option autoImplicit true
set_option autoImplicit false

open scoped BigOperators

namespace RematManuscriptInstances

noncomputable section

open RematDilationSynthesis RematDilationArithmetic

def anchorReps : Fin 3 → ℕ := ![4, 4, 1]

def firstReps : Fin 6 → ℕ := fun _ => 1

def secondReps : Fin 6 → ℕ := fun _ => 2

def anchorProfile : Fin 3 → ℝ := fun i => (anchorReps i : ℝ) / 9

def sixProfile : Fin 6 → ℝ := fun _ => 1 / 3

def ProfileAtHeight {N : ℕ} (D r H : ℕ) (f : Fin N → ℝ) : Prop :=
  0 < H ∧ ∃ a : Fin N → ℚ, (∀ i, 0 < a i) ∧ (∑ i, a i = 1) ∧
    ∀ j : ℕ, ∀ i, Int.fract (((H * (r + j * D) : ℕ) : ℝ) * (a i : ℝ)) = f i

theorem anchor_representatives (i : Fin 3) :
    0 < anchorReps i ∧ anchorReps i < 9 / Nat.gcd 9 1 ∧
      Nat.ModEq 9 (1 * anchorReps i) (anchorReps i) ∧
      ∀ C : ℕ, Nat.ModEq 9 (1 * C) (anchorReps i) → anchorReps i ≤ C := by
  have hc : anchorReps i < 9 / Nat.gcd 9 1 := by fin_cases i <;> norm_num [anchorReps]
  refine ⟨?_, hc, by simp [Nat.ModEq], fun C hC => least_representative_le 9 1 _ _ C (by norm_num) hc (by simp [Nat.ModEq]) hC⟩
  fin_cases i <;> norm_num [anchorReps]

theorem first_representatives (i : Fin 6) :
    0 < firstReps i ∧ firstReps i < 3 / Nat.gcd 3 1 ∧
      Nat.ModEq 3 (1 * firstReps i) 1 ∧
      ∀ C : ℕ, Nat.ModEq 3 (1 * C) 1 → firstReps i ≤ C := by
  refine ⟨by norm_num [firstReps], by norm_num [firstReps], by norm_num [firstReps, Nat.ModEq], ?_⟩
  exact fun C hC => least_representative_le 3 1 1 1 C (by norm_num) (by norm_num) (by norm_num [Nat.ModEq]) hC

theorem second_representatives (i : Fin 6) :
    0 < secondReps i ∧ secondReps i < 3 / Nat.gcd 3 2 ∧
      Nat.ModEq 3 (2 * secondReps i) 1 ∧
      ∀ C : ℕ, Nat.ModEq 3 (2 * C) 1 → secondReps i ≤ C := by
  refine ⟨by norm_num [secondReps], by change 2 < 3 / Nat.gcd 3 2; decide, by norm_num [secondReps, Nat.ModEq], ?_⟩
  exact fun C hC => least_representative_le 3 2 1 2 C (by norm_num) (by decide) (by norm_num [Nat.ModEq]) hC

theorem representative_sums_heights :
    (∑ i, anchorReps i = 9) ∧ (∑ i, firstReps i = 6) ∧ (∑ i, secondReps i = 12) ∧
    Nat.ceil (((∑ i, anchorReps i : ℕ) : ℚ) / 9) = 1 ∧
    Nat.ceil (((∑ i, firstReps i : ℕ) : ℚ) / 3) = 2 ∧
    Nat.ceil (((∑ i, secondReps i : ℕ) : ℚ) / 3) = 4 := by
  norm_num [anchorReps, firstReps, secondReps, Fin.sum_univ_succ]

theorem profile_height_iff {N : ℕ} (hN : 0 < N) (D r t H : ℕ) (w c : Fin N → ℕ)
    (hD : 0 < D) (hw : ∀ i, 0 < w i ∧ w i < D)
    (hc : ∀ i, 0 < c i ∧ c i < D / Nat.gcd D r ∧ Nat.ModEq D (r * c i) (w i))
    (hws : ∑ i, w i = D * t) :
    ProfileAtHeight D r H (fun i => (w i : ℝ) / D) ↔
      Nat.ceil (((∑ i, c i : ℕ) : ℚ) / D) ≤ H := by
  constructor
  · rintro ⟨hH, a, ha, has, hf⟩
    apply RematProfileRealBridge.real_profile_minimum_height N H D r a
      (fun i => (w i : ℝ) / D) w c hH hD ha has hw
      (fun i => by field_simp) (fun i => (hc i).2)
    · intro i
      simpa only [Nat.zero_mul, Nat.add_zero, Nat.cast_mul] using hf 0 i
    · intro i
      simpa only [Nat.one_mul, Nat.cast_mul, Nat.cast_add] using hf 1 i
  · intro hH
    let i₀ : Fin N := ⟨0, hN⟩
    have hS : 0 < ∑ i, c i := Finset.sum_pos (fun i _ => (hc i).1) ⟨i₀, Finset.mem_univ i₀⟩
    have hL : 0 < Nat.ceil (((∑ i, c i : ℕ) : ℚ) / D) :=
      Nat.one_le_ceil_iff.mpr (div_pos (by exact_mod_cast hS) (by exact_mod_cast hD))
    have hHp : 0 < H := hL.trans_le hH
    obtain ⟨C, _, hp, hs, hf, _⟩ := common_dilation_simplex Finset.univ c w i₀ (by simp)
      D r t H hD hHp (fun i _ => (hc i).1) (fun i _ => (hc i).2.2)
      (fun i _ => (hw i).2) hws hH
    refine ⟨hHp, (fun i => (C i : ℚ) / (H * D : ℕ)), fun i => hp i (by simp), hs, ?_⟩
    intro j i
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (hf j i (by simp))
    rw [← RematProfileRealBridge.rat_fract_cast] at hh
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast] using hh

theorem anchor_minimum_height (H : ℕ) : ProfileAtHeight 9 1 H anchorProfile ↔ 1 ≤ H := by
  have hh := profile_height_iff (N := 3) (by norm_num) 9 1 1 H anchorReps anchorReps (by norm_num)
    (fun i => ⟨(anchor_representatives i).1, (anchor_representatives i).2.1⟩)
    (fun i => ⟨(anchor_representatives i).1, (anchor_representatives i).2.1, (anchor_representatives i).2.2.1⟩)
    (by norm_num [anchorReps, Fin.sum_univ_succ])
  change (ProfileAtHeight 9 1 H fun i => (anchorReps i : ℝ) / 9) ↔ 1 ≤ H
  simpa only [Nat.cast_ofNat, representative_sums_heights.2.2.2.1] using hh

theorem first_minimum_height (H : ℕ) : ProfileAtHeight 3 1 H sixProfile ↔ 2 ≤ H := by
  have hh := profile_height_iff (N := 6) (by norm_num) 3 1 2 H (fun _ => 1) firstReps (by norm_num)
    (fun _ => by norm_num) (fun i => ⟨(first_representatives i).1, (first_representatives i).2.1, (first_representatives i).2.2.1⟩)
    (by norm_num)
  change (ProfileAtHeight 3 1 H fun _ : Fin 6 => (1 : ℝ) / 3) ↔ 2 ≤ H
  simpa only [Nat.cast_one, Nat.cast_ofNat, representative_sums_heights.2.2.2.2.1] using hh

theorem second_minimum_height (H : ℕ) : ProfileAtHeight 3 2 H sixProfile ↔ 4 ≤ H := by
  have hh := profile_height_iff (N := 6) (by norm_num) 3 2 2 H (fun _ => 1) secondReps (by norm_num)
    (fun _ => by norm_num) (fun i => ⟨(second_representatives i).1, (second_representatives i).2.1, (second_representatives i).2.2.1⟩)
    (by norm_num)
  change (ProfileAtHeight 3 2 H fun _ : Fin 6 => (1 : ℝ) / 3) ↔ 4 ≤ H
  simpa only [Nat.cast_one, Nat.cast_ofNat, representative_sums_heights.2.2.2.2.2] using hh

theorem common_height_exact (H : ℕ) :
    (ProfileAtHeight 9 1 H anchorProfile ∧ ProfileAtHeight 3 1 H sixProfile ∧
      ProfileAtHeight 3 2 H sixProfile) ↔ 4 ≤ H := by
  rw [anchor_minimum_height, first_minimum_height, second_minimum_height]
  omega

theorem anchor_padding_target (i : Fin 3) :
    ((padded anchorReps 0 (4 * 9 - ∑ j, anchorReps j) i : ℕ) : ℝ) / (4 * 9) =
      RematCompactTransfer.anchorTarget i := by
  fin_cases i <;> norm_num [padded, anchorReps, RematCompactTransfer.anchorTarget, Fin.sum_univ_succ]

theorem first_padding_target (i : Fin 6) :
    ((padded firstReps 0 (4 * 3 - ∑ j, firstReps j) i : ℕ) : ℝ) / (4 * 3) =
      RematCompactTransfer.firstTarget i := by
  fin_cases i <;> norm_num [padded, firstReps, RematCompactTransfer.firstTarget, Fin.sum_univ_succ]

theorem second_padding_target (i : Fin 6) :
    ((padded secondReps 0 (4 * 3 - ∑ j, secondReps j) i : ℕ) : ℝ) / (4 * 3) =
      RematCompactTransfer.secondTarget i := by
  fin_cases i <;> norm_num [padded, secondReps, RematCompactTransfer.secondTarget, Fin.sum_univ_succ]

theorem real_profile_dimension_lower_bound {N : ℕ} (f : Fin N → ℝ) (t q : ℝ)
    (hq : 0 < q) (hf : ∀ i, f i ≤ q) (hs : ∑ i, f i = t) :
    Nat.ceil (t / q) ≤ N := by
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ hq).mpr
  calc
    t = ∑ i, f i := hs.symm
    _ ≤ ∑ _i : Fin N, q := Finset.sum_le_sum (fun i _ => hf i)
    _ = (N : ℝ) * q := by simp

def normalizedReferenceCost {N : ℕ} (f : Fin N → ℝ) (t j : ℕ) : ℝ :=
  (∑ i, (f i)^2) + RematPenaltySelection.scalar (1 / 9) t (fun i => 1 - 2 * f i) (Equiv.refl _) j

theorem anchor_displayed_costs :
    normalizedReferenceCost anchorProfile 1 0 = 14 / 27 ∧
      normalizedReferenceCost anchorProfile 1 1 = 14 / 27 := by
  simp only [normalizedReferenceCost, RematPenaltySelection.scalar, RematSelection.cost,
    RematPenaltySelection.firstSet, RematPenaltySelection.initial, Finset.sum_map,
    Equiv.toEmbedding_apply, Equiv.refl_apply, Finset.sum_filter]
  norm_num [anchorProfile, anchorReps, Fin.sum_univ_succ]

theorem six_displayed_costs :
    normalizedReferenceCost sixProfile 2 0 = 10 / 9 ∧
      normalizedReferenceCost sixProfile 2 1 = 10 / 9 ∧
      normalizedReferenceCost sixProfile 2 2 = 4 / 3 := by
  simp only [normalizedReferenceCost, RematPenaltySelection.scalar, RematSelection.cost,
    RematPenaltySelection.firstSet, RematPenaltySelection.initial, Finset.sum_map,
    Equiv.toEmbedding_apply, Equiv.refl_apply, Finset.sum_filter]
  norm_num [sixProfile, Fin.sum_univ_succ]

end

end RematManuscriptInstances

#print axioms RematManuscriptInstances.anchor_representatives
#print axioms RematManuscriptInstances.first_representatives
#print axioms RematManuscriptInstances.second_representatives
#print axioms RematManuscriptInstances.representative_sums_heights
#print axioms RematManuscriptInstances.profile_height_iff
#print axioms RematManuscriptInstances.anchor_minimum_height
#print axioms RematManuscriptInstances.first_minimum_height
#print axioms RematManuscriptInstances.second_minimum_height
#print axioms RematManuscriptInstances.common_height_exact
#print axioms RematManuscriptInstances.anchor_padding_target
#print axioms RematManuscriptInstances.first_padding_target
#print axioms RematManuscriptInstances.second_padding_target
#print axioms RematManuscriptInstances.real_profile_dimension_lower_bound
#print axioms RematManuscriptInstances.anchor_displayed_costs
#print axioms RematManuscriptInstances.six_displayed_costs
end

section
set_option autoImplicit true
set_option autoImplicit false

open scoped BigOperators Topology ContDiff
open Filter RematCompactFinite RematCompactTransfer

namespace RematReciprocalCutoff

noncomputable section

theorem cutoff_exists (δ : ℝ) (hδ : 0 < δ) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ s, |s| ≤ δ / 3 → χ s = 0) ∧
      (∀ s, δ ≤ s → s ≤ 1 → χ s = 1) ∧ χ =ᶠ[𝓝 0] 0 := by
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := δ / 3
      rOut := δ
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let c : ContDiffBump (0 : ℝ) :=
    { rIn := 1
      rOut := 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let χ := fun s => c s * (1 - b s)
  refine ⟨χ, c.contDiff.mul (contDiff_const.sub b.contDiff), ?_, ?_, ?_, ?_⟩
  · exact c.hasCompactSupport.mul_right
  · intro s hs
    have hb : b s = 1 := b.one_of_mem_closedBall (by simpa [Real.dist_eq, b] using hs)
    simp [χ, hb]
  · intro s hs h1
    have hs0 : 0 ≤ s := hδ.le.trans hs
    have hb : b s = 0 := b.zero_of_le_dist (by simpa [Real.dist_eq, b, abs_of_nonneg hs0] using hs)
    have hc : c s = 1 := c.one_of_mem_closedBall (by simpa [Real.dist_eq, c, abs_of_nonneg hs0] using h1)
    simp [χ, hb, hc]
  · filter_upwards [b.eventuallyEq_one] with s hs
    simp only [χ, hs, Pi.one_apply, sub_self, mul_zero, Pi.zero_apply]

theorem reciprocal_cutoff_smooth (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hz : χ =ᶠ[𝓝 0] 0) :
    ContDiff ℝ ∞ (fun s => χ s / s) ∧ HasCompactSupport (fun s => χ s / s) ∧
      (fun s => χ s / s) =ᶠ[𝓝 0] 0 ∧
      ∀ k, iteratedDeriv k (fun s => χ s / s) 0 = 0 := by
  have hgzero : (fun s => χ s / s) =ᶠ[𝓝 0] 0 := by
    filter_upwards [hz] with s hs
    simp [hs]
  have hg : ContDiff ℝ ∞ (fun s => χ s / s) := by
    rw [contDiff_iff_contDiffAt]
    intro s
    by_cases hs : s = 0
    · subst s
      exact contDiffAt_const.congr_of_eventuallyEq hgzero
    · exact hχ.contDiffAt.div contDiffAt_id hs
  refine ⟨hg, ?_, hgzero, ?_⟩
  · rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
    filter_upwards [hc] with s hs
    simp [hs]
  · intro k
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      RematDiagonalSmooth.zero_germ_zero_jet _ hgzero k, norm_zero]

theorem compact_c2_bound (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, k ≤ 2 → ∀ s, |iteratedDeriv k g s| ≤ B := by
  obtain ⟨K, hK, hb⟩ := RematDiagonalSmooth.compact_derivative_bounds (fun _ => g)
    (fun _ => hg) (fun _ => hc)
  refine ⟨∑ k ∈ Finset.range 3, K k 0, Finset.sum_nonneg (fun k _ => hK k 0), ?_⟩
  intro k hk s
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (hb k 0 s).trans (Finset.single_le_sum (fun i _ => hK i 0)
    (Finset.mem_range.mpr (by omega)))

theorem positive_scaling (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hz : g =ᶠ[𝓝 0] 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ β < ε ∧ β < 1 / 36 ∧
      ContDiff ℝ ∞ (fun s => α * g s) ∧
      (∀ k, iteratedDeriv k (fun s => α * g s) 0 = 0) ∧
      ∀ k : ℕ, k ≤ 2 → ∀ s, |iteratedDeriv k (fun s => α * g s) s| ≤ β := by
  obtain ⟨B, hB, hb⟩ := compact_c2_bound g hg hc
  let β := min (ε / 2) (1 / 72)
  have hβ : 0 < β := lt_min (by positivity) (by norm_num)
  have hden : 0 < 1 + B := by linarith
  let α := β / (1 + B)
  have hα : 0 < α := div_pos hβ hden
  refine ⟨α, β, hα, hβ, (min_le_left _ _).trans_lt (by linarith),
    (min_le_right _ _).trans_lt (by norm_num), contDiff_const.mul hg, ?_, ?_⟩
  · intro k
    rw [iteratedDeriv_const_mul_field]
    have hk : iteratedDeriv k g 0 = 0 := by
      apply norm_eq_zero.mp
      rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        RematDiagonalSmooth.zero_germ_zero_jet _ hz k, norm_zero]
    rw [hk, mul_zero]
  · intro k hk s
    rw [iteratedDeriv_const_mul_field, abs_mul, abs_of_pos hα]
    have hd : α * (1 + B) = β := by dsimp [α]; field_simp
    nlinarith [hb k hk s]


theorem finite_sample_reciprocal_witness (S : Finset ℝ) (hS : S.Nonempty)
    (hpos : ∀ s ∈ S, 0 < s) (hle : ∀ s ∈ S, s ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ α β : ℝ, ∃ χ g h : ℝ → ℝ,
      δ ∈ S ∧ 0 < δ ∧ (∀ s ∈ S, δ ≤ s) ∧ 0 < α ∧
      0 < β ∧ β < ε ∧ β < 1 / 36 ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ s ∈ Set.Icc 0 (δ / 3), χ s = 0) ∧
      (∀ s ∈ Set.Icc δ 1, χ s = 1) ∧
      g 0 = 0 ∧ (∀ s, g s = χ s / s) ∧
      ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      h = (fun s => α * g s) ∧ ContDiff ℝ ∞ h ∧
      (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∀ k : ℕ, k ≤ 2 → ∀ s, |iteratedDeriv k h s| ≤ β) ∧
      (∀ s ∈ S, h s = α / s) ∧ h 0 = 0 := by
  classical
  let δ := S.min' hS
  have hmem : δ ∈ S := S.min'_mem hS
  have hδ : 0 < δ := hpos δ hmem
  have hmin : ∀ s ∈ S, δ ≤ s := fun s hs => S.min'_le s hs
  obtain ⟨χ, hχ, hcχ, hzero, hone, hzχ⟩ := cutoff_exists δ hδ
  let g := fun s => χ s / s
  obtain ⟨hg, hcg, hzg, _⟩ := reciprocal_cutoff_smooth χ hχ hcχ hzχ
  obtain ⟨α, β, hα, hβ, hβε, hβsmall, hh, hj, hb⟩ := positive_scaling g hg hcg hzg ε hε
  refine ⟨δ, α, β, χ, g, (fun s => α * g s), hmem, hδ, hmin, hα,
    hβ, hβε, hβsmall, hχ, hcχ, ?_, ?_, ?_, fun _ => rfl, hg, hcg, rfl, hh, hj, hb, ?_, ?_⟩
  · intro s hs
    exact hzero s (by rw [abs_of_nonneg hs.1]; exact hs.2)
  · intro s hs
    exact hone s hs.1 hs.2
  · simp [g]
  · intro s hs
    simp [g, hone s (hmin s hs) (hle s hs), div_eq_mul_inv]
  · simp [g]

def positiveSamples (A B C : Finset ℕ) : Finset ℝ := by
  classical
  exact A.image (fun j : ℕ => 1 / (4 * (1 + 9 * (j : ℝ)))) ∪
    B.image (fun j : ℕ => 2 / (4 * (4 + 3 * (j : ℝ)))) ∪
    B.image (fun j : ℕ => 1 / (4 * (4 + 3 * (j : ℝ)))) ∪
    C.image (fun j : ℕ => 2 / (4 * (2 + 3 * (j : ℝ)))) ∪
    C.image (fun j : ℕ => 1 / (4 * (2 + 3 * (j : ℝ))))

theorem positive_samples_bounds (A B C : Finset ℕ) (s : ℝ)
    (hs : s ∈ positiveSamples A B C) : 0 < s ∧ s ≤ 1 := by
  classical
  simp only [positiveSamples, Finset.mem_union, Finset.mem_image] at hs
  rcases hs with (((⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) | ⟨j, _, rfl⟩) | ⟨j, _, rfl⟩) | ⟨j, _, rfl⟩
  all_goals constructor
  all_goals try positivity
  all_goals apply (div_le_one (by positivity)).mpr; nlinarith [Nat.cast_nonneg (α := ℝ) j]

theorem positive_samples_empty (A B C : Finset ℕ) :
    positiveSamples A B C = ∅ ↔ A = ∅ ∧ B = ∅ ∧ C = ∅ := by
  classical
  simp [positiveSamples]


def IsReciprocalWitness (S : Finset ℝ) (ε : ℝ) (h : ℝ → ℝ) : Prop :=
    ∃ δ α β : ℝ, ∃ χ g : ℝ → ℝ,
      δ ∈ S ∧ 0 < δ ∧ (∀ s ∈ S, δ ≤ s) ∧ 0 < α ∧
      0 < β ∧ β < ε ∧ β < 1 / 36 ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ s ∈ Set.Icc 0 (δ / 3), χ s = 0) ∧
      (∀ s ∈ Set.Icc δ 1, χ s = 1) ∧
      g 0 = 0 ∧ (∀ s, g s = χ s / s) ∧
      ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      h = (fun s => α * g s) ∧ ContDiff ℝ ∞ h ∧
      (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∀ k : ℕ, k ≤ 2 → ∀ s, |iteratedDeriv k h s| ≤ β) ∧
      (∀ s ∈ S, h s = α / s) ∧ h 0 = 0

def SmallRealization (A B C : Finset ℕ) (ε : ℝ) (h : ℝ → ℝ) : Prop :=
    ContDiff ℝ ∞ h ∧ (∀ k, iteratedDeriv k h 0 = 0) ∧
      (∃ β : ℝ, 0 ≤ β ∧ β < min ε (1 / 36) ∧
        ∀ k : ℕ, k ≤ 2 → ∀ s, |iteratedDeriv k h s| ≤ β) ∧
      MonotoneOn (fun s => (1 / 9 : ℝ) * s ^ 2 + h s) (Set.Icc 0 1) ∧
      ConvexOn ℝ (Set.Icc 0 1) (fun s => ((1 / 9 : ℝ) * s ^ 2 + h s) - (1 / 18 : ℝ) * s ^ 2) ∧
      (∀ j ∈ A, RematTransfer.gridExactIndex (fun s => (1 / 9 : ℝ) * s ^ 2 + h s)
        (4 * (1 + 9 * j)) anchorTarget 1) ∧
      (∀ j ∈ B, RematTransfer.gridExactIndex (fun s => (1 / 9 : ℝ) * s ^ 2 + h s)
        (4 * (4 + 3 * j)) firstTarget 0) ∧
      (∀ j ∈ C, RematTransfer.gridExactIndex (fun s => (1 / 9 : ℝ) * s ^ 2 + h s)
        (4 * (2 + 3 * j)) secondTarget 0)

theorem realization_from_labels (A B C : Finset ℕ) (ε β : ℝ) (hβ : 0 ≤ β)
    (hβε : β < ε) (hsmall : β < 1 / 36) (h : ℝ → ℝ)
    (hsm : ContDiff ℝ ∞ h) (hjet : ∀ k, iteratedDeriv k h 0 = 0)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ s, |iteratedDeriv k h s| ≤ β)
    (ha : ∀ j ∈ A, h 0 < h (1 / (4 * (1 + 9 * (j : ℝ)))))
    (h₁ : ∀ j ∈ B, h (2 / (4 * (4 + 3 * (j : ℝ)))) < h (1 / (4 * (4 + 3 * (j : ℝ)))))
    (h₂ : ∀ j ∈ C, h (2 / (4 * (2 + 3 * (j : ℝ)))) < h (1 / (4 * (2 + 3 * (j : ℝ))))) :
    SmallRealization A B C ε h := by
  have hd := smooth_derivative_data h hsm
  refine ⟨hsm, hjet, ⟨β, hβ, lt_min hβε hsmall, hb⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact RematTransfer.perturbed_penalty_monotone (1 / 9) β (by norm_num) (by linarith)
      h (iteratedDeriv 1 h) (iteratedDeriv 2 h) (fun x _ => hd.1 x) (fun x _ => hd.2 x)
      (hjet 1) (fun x _ => hb 2 (by decide) x)
  · have hc := RematTransfer.perturbed_quantitative_convexity (1 / 9) β (by linarith)
      h (iteratedDeriv 1 h) (iteratedDeriv 2 h) (fun x _ => hd.1 x) (fun x _ => hd.2 x)
      (fun x _ => hb 2 (by decide) x)
    norm_num at hc ⊢
    exact hc
  · exact fun j hj => (anchor_smooth_transfer j β hβ hsmall h hsm hjet hb).mpr (ha j hj)
  · exact fun j hj => (first_smooth_transfer j β hβ hsmall h hsm hjet hb).mpr (h₁ j hj)
  · exact fun j hj => (second_smooth_transfer j β hβ hsmall h hsm hjet hb).mpr (h₂ j hj)

theorem reciprocal_witness_realizes (A B C : Finset ℕ) (ε : ℝ) (h : ℝ → ℝ)
    (hw : IsReciprocalWitness (positiveSamples A B C) ε h) : SmallRealization A B C ε h := by
  classical
  obtain ⟨δ, α, β, χ, g, _, _, _, hα, hβ, hβε, hsmall, _, _, _, _, _, _, _, _, _,
    hsm, hjet, hb, hsample, hz⟩ := hw
  apply realization_from_labels A B C ε β hβ.le hβε hsmall h hsm hjet hb
  · intro j hj
    have hm : 1 / (4 * (1 + 9 * (j : ℝ))) ∈ positiveSamples A B C := by
      simp only [positiveSamples, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl (Or.inl ⟨j, hj, rfl⟩)))
    rw [hz, hsample _ hm]
    positivity
  · intro j hj
    have hlarge : 2 / (4 * (4 + 3 * (j : ℝ))) ∈ positiveSamples A B C := by
      simp only [positiveSamples, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩)))
    have hsmall : 1 / (4 * (4 + 3 * (j : ℝ))) ∈ positiveSamples A B C := by
      simp only [positiveSamples, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩))
    rw [hsample _ hlarge, hsample _ hsmall]
    simpa only [div_eq_mul_inv, one_mul] using mul_lt_mul_of_pos_left
      (RematCompactFamily.positive_reciprocal_strict (4 * (4 + 3 * (j : ℝ))) (by positivity)) hα
  · intro j hj
    have hlarge : 2 / (4 * (2 + 3 * (j : ℝ))) ∈ positiveSamples A B C := by
      simp only [positiveSamples, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
    have hsmall : 1 / (4 * (2 + 3 * (j : ℝ))) ∈ positiveSamples A B C := by
      simp only [positiveSamples, Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨j, hj, rfl⟩
    rw [hsample _ hlarge, hsample _ hsmall]
    simpa only [div_eq_mul_inv, one_mul] using mul_lt_mul_of_pos_left
      (RematCompactFamily.positive_reciprocal_strict (4 * (2 + 3 * (j : ℝ))) (by positivity)) hα

theorem finite_nonempty_reciprocal_realization (A B C : Finset ℕ)
    (hne : (positiveSamples A B C).Nonempty) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, IsReciprocalWitness (positiveSamples A B C) ε h ∧
      SmallRealization A B C ε h := by
  obtain ⟨δ, α, β, χ, g, h, hw⟩ := finite_sample_reciprocal_witness (positiveSamples A B C) hne
    (fun s hs => (positive_samples_bounds A B C s hs).1)
    (fun s hs => (positive_samples_bounds A B C s hs).2) ε hε
  have hfull : IsReciprocalWitness (positiveSamples A B C) ε h := ⟨δ, α, β, χ, g, hw⟩
  exact ⟨h, hfull, reciprocal_witness_realizes A B C ε h hfull⟩

theorem empty_realization (ε : ℝ) (hε : 0 < ε) :
    SmallRealization ∅ ∅ ∅ ε (fun _ => 0) := by
  apply realization_from_labels ∅ ∅ ∅ ε 0 le_rfl hε (by norm_num) (fun _ => 0) contDiff_const
  · intro k
    simp
  · intro k hk s
    simp
  all_goals simp

theorem finite_reciprocal_realization (A B C : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, SmallRealization A B C ε h ∧
      ((positiveSamples A B C).Nonempty → IsReciprocalWitness (positiveSamples A B C) ε h) ∧
      (A = ∅ → B = ∅ → C = ∅ → h = fun _ => 0) := by
  classical
  by_cases hne : (positiveSamples A B C).Nonempty
  · obtain ⟨h, hw, hr⟩ := finite_nonempty_reciprocal_realization A B C hne ε hε
    refine ⟨h, hr, fun _ => hw, ?_⟩
    intro hA hB hC
    have he := (positive_samples_empty A B C).mpr ⟨hA, hB, hC⟩
    rw [he] at hne
    exact (Finset.not_nonempty_empty hne).elim
  · have he : positiveSamples A B C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨rfl, rfl, rfl⟩ := (positive_samples_empty A B C).mp he
    exact ⟨fun _ => 0, empty_realization ε hε, fun hh => (hne hh).elim, fun _ _ _ => rfl⟩


theorem realized_penalty_smooth_same_jet (A B C : Finset ℕ) (ε : ℝ) (h : ℝ → ℝ)
    (hr : SmallRealization A B C ε h) :
    ContDiff ℝ ∞ (fun s => (1 / 9 : ℝ) * s ^ 2 + h s) ∧
      ∀ k, iteratedDeriv k (fun s => (1 / 9 : ℝ) * s ^ 2 + h s) 0 =
        iteratedDeriv k (fun s => (1 / 9 : ℝ) * s ^ 2) 0 := by
  have hp : ContDiff ℝ ∞ (fun s => (1 / 9 : ℝ) * s ^ 2) := by fun_prop
  refine ⟨hp.add hr.1, ?_⟩
  intro k
  have hpk : ContDiffAt ℝ k (fun s => (1 / 9 : ℝ) * s ^ 2) 0 :=
    hp.contDiffAt.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  have hhk : ContDiffAt ℝ k h 0 :=
    hr.1.contDiffAt.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  rw [iteratedDeriv_fun_add hpk hhk, hr.2.1 k, add_zero]

end

end RematReciprocalCutoff

#print axioms RematReciprocalCutoff.cutoff_exists
#print axioms RematReciprocalCutoff.reciprocal_cutoff_smooth
#print axioms RematReciprocalCutoff.compact_c2_bound
#print axioms RematReciprocalCutoff.positive_scaling
#print axioms RematReciprocalCutoff.finite_sample_reciprocal_witness
#print axioms RematReciprocalCutoff.positive_samples_bounds
#print axioms RematReciprocalCutoff.positive_samples_empty
#print axioms RematReciprocalCutoff.realization_from_labels
#print axioms RematReciprocalCutoff.reciprocal_witness_realizes
#print axioms RematReciprocalCutoff.finite_nonempty_reciprocal_realization
#print axioms RematReciprocalCutoff.empty_realization
#print axioms RematReciprocalCutoff.finite_reciprocal_realization
#print axioms RematReciprocalCutoff.realized_penalty_smooth_same_jet
end

section
set_option autoImplicit true
set_option autoImplicit false

open scoped BigOperators

namespace RematRealTargetBridge

noncomputable section

theorem two_profiles_integer_coordinate (H D r : ℕ) (a f : ℝ)
    (hH : 0 < H) (hD : 0 < D) (ha : 0 < a)
    (h0 : Int.fract ((H : ℝ) * r * a) = f)
    (h1 : Int.fract ((H : ℝ) * (r + D) * a) = f) :
    ∃ c : ℕ, 0 < c ∧ (H : ℝ) * D * a = c := by
  obtain ⟨_, _, z0, hz0⟩ := Int.fract_eq_iff.mp h0
  obtain ⟨_, _, z1, hz1⟩ := Int.fract_eq_iff.mp h1
  have he : (H : ℝ) * D * a = ((z1 - z0 : ℤ) : ℝ) := by
    push_cast
    nlinarith
  have hcpos : 0 < z1 - z0 := by
    exact_mod_cast (show (0 : ℝ) < ((z1 - z0 : ℤ) : ℝ) by
      rw [← he]
      exact mul_pos (mul_pos (Nat.cast_pos.mpr hH) (Nat.cast_pos.mpr hD)) ha)
  refine ⟨(z1 - z0).toNat, Int.pos_iff_toNat_pos.mp hcpos, ?_⟩
  rw [he]
  norm_cast
  exact (Int.toNat_of_nonneg hcpos.le).symm

theorem consecutive_profiles_integer_coordinate (H D r j : ℕ) (a f : ℝ)
    (hH : 0 < H) (hD : 0 < D) (ha : 0 < a)
    (h0 : Int.fract (((H * (r + j * D) : ℕ) : ℝ) * a) = f)
    (h1 : Int.fract (((H * (r + (j + 1) * D) : ℕ) : ℝ) * a) = f) :
    ∃ c : ℕ, 0 < c ∧ (H : ℝ) * D * a = c := by
  apply two_profiles_integer_coordinate H D (r + j * D) a f hH hD ha
  · simpa only [Nat.cast_mul] using h0
  · have he : r + (j + 1) * D = (r + j * D) + D := by ring
    rw [he] at h1
    simpa only [Nat.cast_mul, Nat.cast_add] using h1

theorem two_profiles_rational_coordinate (H D r : ℕ) (a f : ℝ)
    (hH : 0 < H) (hD : 0 < D) (ha : 0 < a)
    (h0 : Int.fract ((H : ℝ) * r * a) = f)
    (h1 : Int.fract ((H : ℝ) * (r + D) * a) = f) :
    ∃ b : ℚ, 0 < b ∧ (b : ℝ) = a := by
  obtain ⟨c, hc, he⟩ := two_profiles_integer_coordinate H D r a f hH hD ha h0 h1
  refine ⟨(c : ℚ) / ((H : ℚ) * D), div_pos (by exact_mod_cast hc)
    (mul_pos (by exact_mod_cast hH) (by exact_mod_cast hD)), ?_⟩
  push_cast
  apply (div_eq_iff (mul_ne_zero (by exact_mod_cast hH.ne') (by exact_mod_cast hD.ne'))).mpr
  nlinarith [he]

theorem simplex_rationalization {N : ℕ} (H D r : ℕ) (a f : Fin N → ℝ)
    (hH : 0 < H) (hD : 0 < D) (ha : ∀ i, 0 < a i) (hs : ∑ i, a i = 1)
    (h0 : ∀ i, Int.fract ((H : ℝ) * r * a i) = f i)
    (h1 : ∀ i, Int.fract ((H : ℝ) * (r + D) * a i) = f i) :
    ∃ b : Fin N → ℚ, (∀ i, 0 < b i) ∧ (∑ i, b i = 1) ∧ ∀ i, (b i : ℝ) = a i := by
  choose b hb hba using fun i => two_profiles_rational_coordinate H D r (a i) (f i)
    hH hD (ha i) (h0 i) (h1 i)
  refine ⟨b, hb, ?_, hba⟩
  apply Rat.cast_injective (α := ℝ)
  simpa only [Rat.cast_sum, hba, Rat.cast_one] using hs

theorem real_target_lattice_necessary (H D r : ℕ) (a f : ℝ)
    (hH : 0 < H) (hD : 0 < D) (ha : 0 < a) (hf : 0 < f)
    (h0 : Int.fract ((H : ℝ) * r * a) = f)
    (h1 : Int.fract ((H : ℝ) * (r + D) * a) = f) :
    ∃ c w : ℕ, 0 < c ∧ (H : ℝ) * D * a = c ∧ 0 < w ∧ w < D ∧
      (D : ℝ) * f = w ∧ Nat.ModEq D (r * c) w ∧ Nat.gcd D r ∣ w := by
  obtain ⟨b, hb, he⟩ := two_profiles_rational_coordinate H D r a f hH hD ha h0 h1
  simpa only [he] using RematProfileRealBridge.real_profile_lattice_necessary H D r b f
    hH hD hb hf (by simpa only [he] using h0) (by simpa only [he] using h1)

theorem real_target_minimum_height {N : ℕ} (H D r : ℕ) (a f : Fin N → ℝ)
    (w c : Fin N → ℕ) (hH : 0 < H) (hD : 0 < D)
    (ha : ∀ i, 0 < a i) (hs : ∑ i, a i = 1)
    (hw : ∀ i, 0 < w i ∧ w i < D) (hfw : ∀ i, (D : ℝ) * f i = w i)
    (hc : ∀ i, c i < D / Nat.gcd D r ∧ Nat.ModEq D (r * c i) (w i))
    (h0 : ∀ i, Int.fract ((H : ℝ) * r * a i) = f i)
    (h1 : ∀ i, Int.fract ((H : ℝ) * (r + D) * a i) = f i) :
    Nat.ceil (((∑ i, c i : ℕ) : ℚ) / D) ≤ H := by
  obtain ⟨b, hb, hbs, he⟩ := simplex_rationalization H D r a f hH hD ha hs h0 h1
  exact RematProfileRealBridge.real_profile_minimum_height N H D r b f w c hH hD hb hbs hw hfw hc
    (fun i => by simpa only [he i] using h0 i) (fun i => by simpa only [he i] using h1 i)

def RealProfileAtHeight {N : ℕ} (D r H : ℕ) (f : Fin N → ℝ) : Prop :=
  0 < H ∧ ∃ a : Fin N → ℝ, (∀ i, 0 < a i) ∧ (∑ i, a i = 1) ∧
    ∀ j : ℕ, ∀ i, Int.fract (((H * (r + j * D) : ℕ) : ℝ) * a i) = f i

theorem real_iff_rational {N : ℕ} (D r H : ℕ) (f : Fin N → ℝ) (hD : 0 < D) :
    RealProfileAtHeight D r H f ↔ RematManuscriptInstances.ProfileAtHeight D r H f := by
  constructor
  · rintro ⟨hH, a, ha, hs, hf⟩
    obtain ⟨b, hb, hbs, he⟩ := simplex_rationalization H D r a f hH hD ha hs
      (fun i => by simpa only [Nat.zero_mul, Nat.add_zero, Nat.cast_mul] using hf 0 i)
      (fun i => by simpa only [Nat.one_mul, Nat.cast_mul, Nat.cast_add] using hf 1 i)
    exact ⟨hH, b, hb, hbs, fun j i => by simpa only [he i] using hf j i⟩
  · rintro ⟨hH, b, hb, hs, hf⟩
    refine ⟨hH, (fun i => (b i : ℝ)), fun i => by change (0 : ℝ) < (b i : ℝ); exact_mod_cast hb i, ?_, hf⟩
    change (∑ i, (b i : ℝ)) = 1
    exact_mod_cast hs

theorem real_profile_height_iff {N : ℕ} (hN : 0 < N) (D r t H : ℕ) (w c : Fin N → ℕ)
    (hD : 0 < D) (hw : ∀ i, 0 < w i ∧ w i < D)
    (hc : ∀ i, 0 < c i ∧ c i < D / Nat.gcd D r ∧ Nat.ModEq D (r * c i) (w i))
    (hws : ∑ i, w i = D * t) :
    RealProfileAtHeight D r H (fun i => (w i : ℝ) / D) ↔
      Nat.ceil (((∑ i, c i : ℕ) : ℚ) / D) ≤ H :=
  (real_iff_rational D r H _ hD).trans
    (RematManuscriptInstances.profile_height_iff hN D r t H w c hD hw hc hws)

theorem real_instance_minimum_heights (H : ℕ) :
    (RealProfileAtHeight 9 1 H RematManuscriptInstances.anchorProfile ↔ 1 ≤ H) ∧
    (RealProfileAtHeight 3 1 H RematManuscriptInstances.sixProfile ↔ 2 ≤ H) ∧
    (RealProfileAtHeight 3 2 H RematManuscriptInstances.sixProfile ↔ 4 ≤ H) := by
  exact ⟨(real_iff_rational 9 1 H _ (by norm_num)).trans (RematManuscriptInstances.anchor_minimum_height H),
    (real_iff_rational 3 1 H _ (by norm_num)).trans (RematManuscriptInstances.first_minimum_height H),
    (real_iff_rational 3 2 H _ (by norm_num)).trans (RematManuscriptInstances.second_minimum_height H)⟩

theorem arbitrary_real_lattice_iff {N : ℕ} (hN : 0 < N) (D r : ℕ) (f : Fin N → ℝ)
    (hD : 0 < D) (hf : ∀ i, 0 < f i ∧ f i < 1) (hs : ∃ z : ℤ, ∑ i, f i = z) :
    (∃ H : ℕ, RealProfileAtHeight D r H f) ↔
      ∀ i, ∃ z : ℤ, (D : ℝ) * f i = z ∧ ((Nat.gcd D r : ℕ) : ℤ) ∣ z := by
  constructor
  · rintro ⟨H, hH, a, ha, _, hprof⟩ i
    obtain ⟨_, w, _, _, _, _, hw, _, hgw⟩ := real_target_lattice_necessary H D r (a i) (f i)
      hH hD (ha i) (hf i).1
      (by simpa only [Nat.zero_mul, Nat.add_zero, Nat.cast_mul] using hprof 0 i)
      (by simpa only [Nat.one_mul, Nat.cast_mul, Nat.cast_add] using hprof 1 i)
    refine ⟨w, by exact_mod_cast hw, ?_⟩
    exact_mod_cast hgw
  · intro hint
    obtain ⟨L, hL, _, htarget⟩ := RematProfileRealBridge.real_lattice_profile_all_heights
      (Finset.univ : Finset (Fin N)) ⟨⟨0, hN⟩, by simp⟩ D r f hD (fun i _ => hf i)
      (fun i _ => hint i) hs
    obtain ⟨a, ha, has, hprof⟩ := htarget L le_rfl
    refine ⟨L, (real_iff_rational D r L f hD).mpr ⟨hL, a, fun i => ha i (by simp), has, ?_⟩⟩
    exact fun j i => hprof j i (by simp)

end

end RematRealTargetBridge

#print axioms RematRealTargetBridge.two_profiles_integer_coordinate
#print axioms RematRealTargetBridge.consecutive_profiles_integer_coordinate
#print axioms RematRealTargetBridge.two_profiles_rational_coordinate
#print axioms RematRealTargetBridge.simplex_rationalization
#print axioms RematRealTargetBridge.real_target_lattice_necessary
#print axioms RematRealTargetBridge.real_target_minimum_height
#print axioms RematRealTargetBridge.real_iff_rational
#print axioms RematRealTargetBridge.real_profile_height_iff
#print axioms RematRealTargetBridge.real_instance_minimum_heights
#print axioms RematRealTargetBridge.arbitrary_real_lattice_iff
end
