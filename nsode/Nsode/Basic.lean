/-
Copyright (c) 2026 Jitse Niesen, University of Leeds. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jitse Niesen
-/

import Mathlib

/-! Basic abbreviations for the Numerical Solution of ODEs package -/

abbrev Rn (n : ℕ) := Fin n → ℝ
abbrev ODE (n : ℕ) := ℝ → Rn n → Rn n

-- The function φ satisfies the ODE y' = f(t,y)
def IsSolutionOnSet {n : ℕ} (f : ODE n) (φ : ℝ → Rn n) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt φ (f t (φ t)) s t

def IsSolutionOnInterval {n : ℕ} (f : ODE n) (φ : ℝ → Rn n) (a b : ℝ) : Prop :=
  IsSolutionOnSet f φ (Set.Icc a b)

-- An increment function defining a one-step method, argument are f, t, y, h
abbrev Increment (n : ℕ) := ODE n → ℝ → Rn n → ℝ → Rn n

-- Iterate a one-step method on the grid t₀ + k * h.
def numerical_method {n : ℕ} (Φ : Increment n) (f : ODE n) (t₀ : ℝ) (y₀ : Rn n) (h : ℝ) : ℕ → Rn n
  | 0 => y₀
  | k + 1 => (numerical_method Φ f t₀ y₀ h k
              + h • Φ f (t₀ + h * k) (numerical_method Φ f t₀ y₀ h k) h)

-- Local error of some method at a time t given the solution
def local_error {n : ℕ} (Φ : Increment n) (f : ODE n) (φ : ℝ → Rn n) (h : ℝ)
    : ℝ → Rn n :=
  fun t => numerical_method Φ f t (φ t) h 1 - φ (t + h)

-- Global error of some method after k steps given the solution
def global_error {n : ℕ} (Φ : Increment n) (f : ODE n) (φ : ℝ → Rn n) (t₀ h : ℝ) (k : ℕ) :=
  numerical_method Φ f t₀ (φ t₀) h k - φ (t₀ + k * h)
