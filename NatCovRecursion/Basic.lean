import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Common

-- 累積帰納法
theorem cov_recursion { motive : Nat → Sort u } : (∀n, (∀k, (k < n) → motive k) → motive n) → (∀n, motive n) := by
  intro h N
  apply h N
  induction N with
  | zero => intros; contradiction
  | succ K H =>
    have hK := h K H
    intro k hk
    exact if _ : k < K then by
      have : k < K := by assumption
      apply H
      assumption
    else by
      have : ¬ k < K := by assumption
      have : K ≤ k := Nat.ge_of_not_lt ‹¬ k < K›
      apply Nat.le_of_succ_le_succ at hk
      have : k = K := Nat.le_antisymm ‹k ≤ K› ‹K ≤ k›
      rw [this]
      assumption

/-
'Nat.rec' does not depend on any axioms
-/
#print axioms Nat.rec
/-
'cov_recursion' does not depend on any axioms
-/
#print axioms cov_recursion


-- d * d^k = d^(k+1)
theorem d_mul_pow_d_to_k_eq_d_to_pow_succ_k (d k : Nat) : d * d^k = d^(k+1) := by
  match k with
  | 0 => simp
  | k+1 =>
    rw [Nat.mul_comm]
    rfl

/-
'd_mul_pow_d_to_k_eq_d_to_pow_succ_k' depends on axioms: [propext]
-/
#print axioms d_mul_pow_d_to_k_eq_d_to_pow_succ_k

-- d*n/d ≤ d
theorem d_mul_n_div_d_le_d (m n : Nat) : n * (m / n) ≤ m := by
  have h1 : n * (m / n) + m % n = m := Nat.div_add_mod _ _
  have h2 : n * (m / n) ≤ n * (m / n) + m % n := Nat.le_add_right ..
  calc
    n * (m / n) ≤ n * (m / n) + m % n := h2
    _ = m := h1

/-
'd_mul_n_div_d_le_d' depends on axioms: [propext]
-/
#print axioms d_mul_n_div_d_le_d


-- 2^(lg n) ≤ n
theorem power2to_lg_n_le_n : ∀n > 0, 2^(Nat.log2 n) ≤ n := by
  apply cov_recursion
  intro n
  match n with
  | 0 => intros; contradiction
  | 1 => trivial
  | n+2 =>
    intro h _
    set n := n+2
    set log2_n := Nat.log2 n
    let k := n/2
    let log2_k := Nat.log2 k

    have hk := h k
    have : k < n := Nat.bitwise_rec_lemma (Nat.succ_ne_zero _)
    have hk := hk ‹k < n›
    have : 2 ≤ n := Nat.le_add_left ..
    have : 0 < k := Nat.div_pos ‹2 ≤ n› (show 0 < 2 by trivial)
    have hk : 2 ^ log2_k ≤ k := hk ‹0 < k›
    have hk2 : 2 * 2 ^ log2_k ≤ 2 * k := Nat.mul_le_mul_left 2 hk
    have : 2 * 2 ^ log2_k = 2 ^ (log2_k + 1) := d_mul_pow_d_to_k_eq_d_to_pow_succ_k 2 log2_k
    rw [this] at hk2
    have : 2 * k ≤ n := d_mul_n_div_d_le_d ..
    have : log2_n = log2_k + 1 := by
      generalize h: log2_k + 1 = rhs
      unfold Nat.log2
      split
      . rw [←h]
      . contradiction
    rw [‹log2_n = log2_k + 1›]
    show 2 ^ (log2_k+1) ≤ n
    calc
      2 ^ (log2_k+1) ≤ 2 * k := hk2
      _ ≤ n := ‹2*k ≤ n›
    done

/-
'power2to_lg_n_le_n' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#print axioms power2to_lg_n_le_n

def NatInd := ∀P : Nat → Prop, (P 0 → (∀k, P k → P (k+1)) → ∀n, P n)
def NatCompleteInd := ∀P : Nat → Prop, ((∀n, (∀k < n, P k) → P n) → ∀n, P n)
#check (@Nat.rec.{0} : NatInd)
#check (@cov_recursion.{0} : NatCompleteInd)
