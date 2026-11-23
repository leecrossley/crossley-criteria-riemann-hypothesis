import MobiusRamps
import PrimeWindow
import PositivePole

/-! Exact dyadic reverse formulas reconstructing the ordinary prime-power ramp
(`ZetaShared.rampS` and the centred ramp `ZetaShared.rampG`) from the tent sum
`ThetaTransfer.primePowerSum` and signed margin `RiemannReduction.DivisorBand.D`.

Three finite-window reverse identities are proved, each retaining two boundary terms:

1. **Bottom-anchored reconstruction** (`rampS_dyadic_reconstruction`,
   `rampG_dyadic_reconstruction_bottom`, `rampG_top_down_reconstruction`):
   reconstructs `rampS (2^n * x)` and `rampG (2^n * x)` from `n` dyadic tent evaluations
   and the two lower boundary values at `x` and `x / 2` (both boundary terms vanish for
   `rampS` whenever `x < 2`).
2. **Adjacent two-end bounded-weight reconstruction** (`rampG_dyadic_reconstruction_two_end`):
   reconstructs `(2 - 2^(-n)) * rampG (2^n * x)` from bounded positive weights in `[1/2, 1)`
   on `D (2^(j + 2) * x)` plus positive boundary weights on `rampG x` and `rampG (2^(n + 1) * x)`,
   with zero `2^n` blowup.
3. **Exact Dirichlet Green's identity on `[x, 2^N * x]`** (`rampG_dyadic_dirichlet_green` and
   `rampG_dyadic_power_bound_of_dirichlet`):
   solves the second-order dyadic difference equation `-g_{k+1} + 3 g_k - 2 g_{k-1} = D(2^{k+1} x)`
   at every interior dyadic scale `0 ≤ m ≤ N` in terms of convex-combination weights on the two
   fixed window endpoints `rampG x` and `rampG (2^N * x)` and a nonnegative Green's kernel
   bounded by `min(1, 2^(m - k))`, yielding an `N`-independent `O((2^m * x)^θ)` bound across
   every dyadic scale in `[x, 2^N * x]` whenever `θ ∈ (0, 1)`. -/

open Finset ArithmeticFunction Complex Filter MeasureTheory Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace Crossley

/-! ### 1. Uncentred Prime-Power Ramp Reconstruction from Dyadic Tent Sums -/

/-- First dyadic difference `rampS x - 2 * rampS (x / 2)` of the uncentred prime-power ramp. -/
def uncenteredRampIncrement (x : ℝ) : ℝ :=
  ZetaShared.rampS x - 2 * ZetaShared.rampS (x / 2)

/-- The prime-power tent sum at `x / 4` is the dyadic drop of `uncenteredRampIncrement`. -/
theorem primePowerSum_eq_uncenteredIncrement_sub {x : ℝ} (hx : 0 < x) :
    ThetaTransfer.primePowerSum (x / 4) =
      uncenteredRampIncrement x - uncenteredRampIncrement (x / 2) := by
  have h := ThetaTransfer.primePowerSum_eq_ramps (y := x / 4) (by linarith)
  rw [show 4 * (x / 4) = x by ring, show 2 * (x / 4) = x / 2 by ring] at h
  unfold uncenteredRampIncrement
  rw [show x / 2 / 2 = x / 4 by ring]
  linarith

/-- First dyadic telescoping of the uncentred tent sums. -/
theorem sum_dyadic_primePowerSums {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∑ j ∈ range n, ThetaTransfer.primePowerSum ((2 : ℝ) ^ (j + 1) * x / 4) =
      uncenteredRampIncrement ((2 : ℝ) ^ n * x) - uncenteredRampIncrement x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih,
      primePowerSum_eq_uncenteredIncrement_sub (by positivity : 0 < (2 : ℝ) ^ (n + 1) * x)]
    rw [show (2 : ℝ) ^ (n + 1) * x / 2 = (2 : ℝ) ^ n * x by rw [pow_succ]; ring]
    ring

/-- **Exact finite-window reverse formula for the uncentred ramp `rampS`:**
reconstructs `rampS (2^n * x)` from `n` dyadic tent evaluations and two boundary terms
at `x` and `x / 2`. -/
theorem rampS_dyadic_reconstruction {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ZetaShared.rampS ((2 : ℝ) ^ n * x) =
      (∑ j ∈ range n,
        ((2 : ℝ) ^ (n - j) - 1) * ThetaTransfer.primePowerSum ((2 : ℝ) ^ (j + 1) * x / 4)) +
      ((2 : ℝ) ^ (n + 1) - 1) * ZetaShared.rampS x -
      2 * ((2 : ℝ) ^ n - 1) * ZetaShared.rampS (x / 2) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    have hinc : ZetaShared.rampS ((2 : ℝ) ^ (n + 1) * x) =
        2 * ZetaShared.rampS ((2 : ℝ) ^ n * x) +
          uncenteredRampIncrement ((2 : ℝ) ^ (n + 1) * x) := by
      unfold uncenteredRampIncrement
      rw [show (2 : ℝ) ^ (n + 1) * x / 2 = (2 : ℝ) ^ n * x by rw [pow_succ]; ring]
      ring
    have hsum := sum_dyadic_primePowerSums hx (n + 1)
    have hinc_eq : uncenteredRampIncrement ((2 : ℝ) ^ (n + 1) * x) =
        uncenteredRampIncrement x +
          ∑ j ∈ range (n + 1), ThetaTransfer.primePowerSum ((2 : ℝ) ^ (j + 1) * x / 4) := by
      linarith
    rw [hinc, ih, hinc_eq, sum_range_succ, sum_range_succ]
    have hcomb :
        2 * (∑ j ∈ range n,
            ((2 : ℝ) ^ (n - j) - 1) * ThetaTransfer.primePowerSum ((2 : ℝ) ^ (j + 1) * x / 4)) +
          (∑ j ∈ range n, ThetaTransfer.primePowerSum ((2 : ℝ) ^ (j + 1) * x / 4)) =
        ∑ j ∈ range n,
          ((2 : ℝ) ^ (n + 1 - j) - 1) *
            ThetaTransfer.primePowerSum ((2 : ℝ) ^ (j + 1) * x / 4) := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j hj => ?_
      have hjn : j ≤ n := Nat.le_of_lt (mem_range.mp hj)
      rw [show n + 1 - j = (n - j) + 1 from Nat.succ_sub hjn, pow_succ]
      ring
    unfold uncenteredRampIncrement
    rw [show n + 1 - n = 1 by omega, pow_one]
    have hb1_eq : (2 * ((2 : ℝ) ^ (n + 1) - 1) + 1) * ZetaShared.rampS x =
        ((2 : ℝ) ^ (n + 2) - 1) * ZetaShared.rampS x := by rw [pow_succ]; ring
    have hb2_eq : (4 * ((2 : ℝ) ^ n - 1) + 2) * ZetaShared.rampS (x / 2) =
        2 * ((2 : ℝ) ^ (n + 1) - 1) * ZetaShared.rampS (x / 2) := by rw [pow_succ]; ring
    linarith

/-- `rampS x` vanishes identically for all `x < 2` since `Λ 0 = Λ 1 = 0`. -/
theorem rampS_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : ZetaShared.rampS x = 0 := by
  unfold ZetaShared.rampS IndependentLandau.rampS
  refine sum_eq_zero fun n hn => ?_
  rcases lt_or_ge x 0 with hx0 | hx0
  · have hf : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos hx0.le
    rw [hf] at hn
    have hn0 : n = 0 := by simpa using mem_range.mp hn
    rw [hn0, IndependentLandau.rampT_zero]
  · have hf : ⌊x⌋₊ < 2 := (Nat.floor_lt hx0).mpr (by exact_mod_cast hx)
    have hn2 : n < 2 := lt_of_lt_of_le (mem_range.mp hn) hf
    interval_cases n
    · exact IndependentLandau.rampT_zero x
    · simp [IndependentLandau.rampT]

/-- When `0 < x < 2`, both boundary terms vanish and `rampS (2^n * x)` is reconstructed
purely from dyadic evaluations of the tent sum. -/
theorem rampS_dyadic_reconstruction_of_lt_two {x : ℝ} (hx0 : 0 < x) (hx2 : x < 2) (n : ℕ) :
    ZetaShared.rampS ((2 : ℝ) ^ n * x) =
      ∑ j ∈ range n,
        ((2 : ℝ) ^ (n - j) - 1) * ThetaTransfer.primePowerSum ((2 : ℝ) ^ (j + 1) * x / 4) := by
  rw [rampS_dyadic_reconstruction hx0 n, rampS_eq_zero_of_lt_two hx2,
    rampS_eq_zero_of_lt_two (by linarith : x / 2 < 2)]
  ring

/-- Top-down boundary-free reconstruction of `rampS y` for every `0 < y < 2^(n + 1)`. -/
theorem rampS_top_down_reconstruction {y : ℝ} (hy : 0 < y) (n : ℕ)
    (hyn : y < (2 : ℝ) ^ (n + 1)) :
    ZetaShared.rampS y =
      ∑ k ∈ range n,
        ((2 : ℝ) ^ (k + 1) - 1) * ThetaTransfer.primePowerSum (y / (2 : ℝ) ^ (k + 2)) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hx0 : 0 < y / (2 : ℝ) ^ n := div_pos hy hp
  have hx2 : y / (2 : ℝ) ^ n < 2 := by
    rw [div_lt_iff₀ hp]
    simpa [pow_succ, mul_comm] using hyn
  have hrec := rampS_dyadic_reconstruction_of_lt_two hx0 hx2 n
  rw [mul_div_cancel₀ y hp.ne'] at hrec
  rw [hrec, ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k < n := mem_range.mp hk
  have hsub : n - (n - 1 - k) = k + 1 := by omega
  have hpow : (2 : ℝ) ^ (n - 1 - k + 1) * (y / (2 : ℝ) ^ n) / 4 = y / (2 : ℝ) ^ (k + 2) := by
    have he : n - 1 - k + 1 + (k + 2) = n + 2 := by omega
    field_simp
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_add (2 : ℝ) n 2, ← pow_add, he]
  rw [hsub, hpow]

/-! ### 2. Centred Prime-Power Ramp — Bottom-Anchored Two-Boundary Identity -/

/-- **Bottom-anchored exact reverse formula for the centred ramp `rampG`:**
reconstructs `rampG (2^n * x)` from `n` dyadic evaluations of `D` and the two lower
boundary terms `rampG x` and `rampG (x / 2)`. -/
theorem rampG_dyadic_reconstruction_bottom {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ZetaShared.rampG ((2 : ℝ) ^ n * x) =
      -(∑ j ∈ range n, ((2 : ℝ) ^ (n - j) - 1) * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 1) * x)) +
      ((2 : ℝ) ^ (n + 1) - 1) * ZetaShared.rampG x -
      2 * ((2 : ℝ) ^ n - 1) * ZetaShared.rampG (x / 2) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    have hinc : ZetaShared.rampG ((2 : ℝ) ^ (n + 1) * x) =
        2 * ZetaShared.rampG ((2 : ℝ) ^ n * x) +
          RiemannReduction.DivisorBand.rampIncrement ((2 : ℝ) ^ (n + 1) * x) := by
      unfold RiemannReduction.DivisorBand.rampIncrement
      rw [show (2 : ℝ) ^ (n + 1) * x / 2 = (2 : ℝ) ^ n * x by rw [pow_succ]; ring]
      ring
    have hsum := RiemannReduction.DivisorBand.sum_dyadic_margins hx (n + 1)
    have hinc_eq : RiemannReduction.DivisorBand.rampIncrement ((2 : ℝ) ^ (n + 1) * x) =
        RiemannReduction.DivisorBand.rampIncrement x -
          ∑ j ∈ range (n + 1), RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 1) * x) := by
      linarith
    rw [hinc, ih, hinc_eq, sum_range_succ, sum_range_succ]
    have hcomb :
        2 * (∑ j ∈ range n,
            ((2 : ℝ) ^ (n - j) - 1) * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 1) * x)) +
          (∑ j ∈ range n, RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 1) * x)) =
        ∑ j ∈ range n,
          ((2 : ℝ) ^ (n + 1 - j) - 1) * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 1) * x) := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j hj => ?_
      have hjn : j ≤ n := Nat.le_of_lt (mem_range.mp hj)
      rw [show n + 1 - j = (n - j) + 1 from Nat.succ_sub hjn, pow_succ]
      ring
    unfold RiemannReduction.DivisorBand.rampIncrement
    rw [show n + 1 - n = 1 by omega, pow_one]
    have hb1_eq : (2 * ((2 : ℝ) ^ (n + 1) - 1) + 1) * ZetaShared.rampG x =
        ((2 : ℝ) ^ (n + 2) - 1) * ZetaShared.rampG x := by rw [pow_succ]; ring
    have hb2_eq : (4 * ((2 : ℝ) ^ n - 1) + 2) * ZetaShared.rampG (x / 2) =
        2 * ((2 : ℝ) ^ (n + 1) - 1) * ZetaShared.rampG (x / 2) := by rw [pow_succ]; ring
    linarith

/-- **Top-down finite-window reverse formula for `rampG y`:**
reconstructs `rampG y` from `n` dyadic octaves of `D (y / 2^k)` (`0 ≤ k < n`) and
two surviving lower boundary terms at `y / 2^n` and `y / 2^(n + 1)`. -/
theorem rampG_top_down_reconstruction {y : ℝ} (hy : 0 < y) (n : ℕ) :
    ZetaShared.rampG y =
      -(∑ k ∈ range n, ((2 : ℝ) ^ (k + 1) - 1) * RiemannReduction.DivisorBand.D (y / (2 : ℝ) ^ k)) +
      ((2 : ℝ) ^ (n + 1) - 1) * ZetaShared.rampG (y / (2 : ℝ) ^ n) -
      2 * ((2 : ℝ) ^ n - 1) * ZetaShared.rampG (y / (2 : ℝ) ^ (n + 1)) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hrec := rampG_dyadic_reconstruction_bottom (div_pos hy hp) n
  rw [mul_div_cancel₀ y hp.ne', show y / (2 : ℝ) ^ n / 2 = y / (2 : ℝ) ^ (n + 1) by
    rw [pow_succ, div_div]] at hrec
  rw [hrec, ← sum_range_reflect]
  congr 3
  refine sum_congr rfl fun k hk => ?_
  have hkn : k < n := mem_range.mp hk
  have hsub : n - (n - 1 - k) = k + 1 := by omega
  have hpow : (2 : ℝ) ^ (n - 1 - k + 1) * (y / (2 : ℝ) ^ n) = y / (2 : ℝ) ^ k := by
    have he : n - 1 - k + 1 + k = n := by omega
    field_simp
    rw [← pow_add, he]
  rw [hsub, hpow]

/-! ### 3. Bounded-Weight Two-End Identity and Exact Dirichlet Green's Function -/

private lemma margin_four_mul {z : ℝ} (hz : 0 < z) :
    RiemannReduction.DivisorBand.D (4 * z) =
      -ZetaShared.rampG (4 * z) + 3 * ZetaShared.rampG (2 * z) - 2 * ZetaShared.rampG z := by
  have h := ThetaTransfer.deficit_eq_centered_ramps hz
  unfold RiemannReduction.DivisorBand.D RiemannReduction.DivisorBand.c
  rw [show 4 * z / 4 = z by ring]
  linarith

/-- **Bounded-weight adjacent two-end reverse formula (`0` `2^n` blowup):**
expresses `(2 - 2^(-n)) * rampG (2^n * x)` with positive weights in `[1/2, 1)` on
`D (2^(j + 2) * x)` and positive weights on `rampG x` and `rampG (2^(n + 1) * x)`. -/
theorem rampG_dyadic_reconstruction_two_end {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (2 - 1 / (2 : ℝ) ^ n) * ZetaShared.rampG ((2 : ℝ) ^ n * x) =
      (∑ j ∈ range n,
        (1 - 1 / (2 : ℝ) ^ (j + 1)) * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 2) * x)) +
      ZetaShared.rampG x +
      (1 - 1 / (2 : ℝ) ^ n) * ZetaShared.rampG ((2 : ℝ) ^ (n + 1) * x) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    have hd := margin_four_mul (z := (2 : ℝ) ^ n * x) (by positivity)
    rw [show 4 * ((2 : ℝ) ^ n * x) = (2 : ℝ) ^ (n + 2) * x by rw [pow_succ, pow_succ]; ring,
      show 2 * ((2 : ℝ) ^ n * x) = (2 : ℝ) ^ (n + 1) * x by rw [pow_succ]; ring] at hd
    rw [sum_range_succ, hd]
    have hsum :
        ∑ j ∈ range n,
            (1 - 1 / (2 : ℝ) ^ (j + 1)) * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 2) * x) =
          (2 - 1 / (2 : ℝ) ^ n) * ZetaShared.rampG ((2 : ℝ) ^ n * x) -
            ZetaShared.rampG x -
            (1 - 1 / (2 : ℝ) ^ n) * ZetaShared.rampG ((2 : ℝ) ^ (n + 1) * x) := by
      linarith
    rw [hsum]
    have hp : (2 : ℝ) ^ n ≠ 0 := by positivity
    rw [show (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n by rw [pow_succ]; ring]
    field_simp [hp]
    ring

/-- **Cauchy initial-value formula along dyadic scales (`m : ℕ`):**
expresses `rampG (2^m * x) - rampG x` from `rampG (2 * x) - rampG x` and `D (2^(j + 2) * x)`. -/
theorem rampG_dyadic_cauchy {x : ℝ} (hx : 0 < x) (m : ℕ) :
    ZetaShared.rampG ((2 : ℝ) ^ m * x) - ZetaShared.rampG x =
      ((2 : ℝ) ^ m - 1) * (ZetaShared.rampG (2 * x) - ZetaShared.rampG x) -
      ∑ j ∈ range m,
        ((2 : ℝ) ^ m / (2 : ℝ) ^ (j + 1) - 1) *
          RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 2) * x) := by
  cases m with
  | zero => simp
  | succ r =>
    have hrec := rampG_dyadic_reconstruction_bottom (by positivity : 0 < 2 * x) r
    rw [show (2 : ℝ) ^ r * (2 * x) = (2 : ℝ) ^ (r + 1) * x by rw [pow_succ]; ring,
      show 2 * x / 2 = x by ring] at hrec
    rw [sum_range_succ, div_self (by positivity : (2 : ℝ) ^ (r + 1) ≠ 0), sub_self, zero_mul,
      add_zero]
    have hsum :
        ∑ j ∈ range r,
            ((2 : ℝ) ^ (r + 1) / (2 : ℝ) ^ (j + 1) - 1) *
              RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 2) * x) =
          ∑ j ∈ range r,
            ((2 : ℝ) ^ (r - j) - 1) *
              RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 1) * (2 * x)) := by
      refine sum_congr rfl fun j hj => ?_
      have hjr : j < r := mem_range.mp hj
      have hdiv : (2 : ℝ) ^ (r + 1) / (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ (r - j) := by
        rw [div_eq_iff (by positivity : (2 : ℝ) ^ (j + 1) ≠ 0), ← pow_add,
          show r - j + (j + 1) = r + 1 by omega]
      rw [hdiv, show (2 : ℝ) ^ (j + 2) * x = (2 : ℝ) ^ (j + 1) * (2 * x) by rw [pow_succ]; ring]
    rw [hsum]
    have hbdy :
        ((2 : ℝ) ^ (r + 1) - 1) * ZetaShared.rampG (2 * x) -
          2 * ((2 : ℝ) ^ r - 1) * ZetaShared.rampG x - ZetaShared.rampG x =
        ((2 : ℝ) ^ (r + 1) - 1) * (ZetaShared.rampG (2 * x) - ZetaShared.rampG x) := by
      rw [pow_succ]
      ring
    linarith

/-- Discrete Green's kernel solving `-g_{k+1} + 3 g_k - 2 g_{k-1} = d_k` on `{0, ..., N}`
with fixed boundary values at `0` and `N`. -/
def dyadicGreenKernel (N m k : ℕ) : ℝ :=
  if k ≤ m then
    (((2 : ℝ) ^ N - (2 : ℝ) ^ m) * (1 - 1 / (2 : ℝ) ^ k)) / ((2 : ℝ) ^ N - 1)
  else
    (((2 : ℝ) ^ m - 1) * ((2 : ℝ) ^ N / (2 : ℝ) ^ k - 1)) / ((2 : ℝ) ^ N - 1)

theorem dyadicGreenKernel_nonneg {N m k : ℕ} (hN : 1 ≤ N) (hm : m ≤ N) (hkN : k ≤ N) :
    0 ≤ dyadicGreenKernel N m k := by
  have hden : 0 < (2 : ℝ) ^ N - 1 := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
    linarith
  unfold dyadicGreenKernel
  split_ifs with hkm
  · apply div_nonneg _ hden.le
    refine mul_nonneg ?_ ?_
    · exact sub_nonneg.mpr (pow_le_pow_right₀ (by norm_num) hm)
    · have hk1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      rw [sub_nonneg, div_le_one (by positivity)]
      exact hk1
  · apply div_nonneg _ hden.le
    refine mul_nonneg ?_ ?_
    · exact sub_nonneg.mpr (one_le_pow₀ (by norm_num))
    · rw [sub_nonneg, one_le_div (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) hkN

theorem dyadicGreenKernel_le_one {N m k : ℕ} (hN : 1 ≤ N) (hm : m ≤ m) (hkm : k ≤ m)
    (hmN : m ≤ N) :
    dyadicGreenKernel N m k ≤ 1 := by
  have _ := hm
  have hden : 0 < (2 : ℝ) ^ N - 1 := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
    linarith
  unfold dyadicGreenKernel
  rw [if_pos hkm, div_le_one hden]
  have h1 : (2 : ℝ) ^ N - (2 : ℝ) ^ m ≤ (2 : ℝ) ^ N - 1 := by
    linarith [one_le_pow₀ (n := m) (by norm_num : (1 : ℝ) ≤ 2)]
  have h2 : 1 - 1 / (2 : ℝ) ^ k ≤ 1 := by
    have : 0 ≤ 1 / (2 : ℝ) ^ k := by positivity
    linarith
  have h0 : 0 ≤ (2 : ℝ) ^ N - (2 : ℝ) ^ m :=
    sub_nonneg.mpr (pow_le_pow_right₀ (by norm_num) hmN)
  nlinarith

theorem dyadicGreenKernel_le_pow_sub {N m k : ℕ} (hN : 1 ≤ N) (hmk : m < k) (hkN : k ≤ N) :
    dyadicGreenKernel N m k ≤ 1 / (2 : ℝ) ^ (k - m) := by
  have hden : 0 < (2 : ℝ) ^ N - 1 := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
    linarith
  unfold dyadicGreenKernel
  rw [if_neg (by omega : ¬ k ≤ m), div_le_div_iff₀ hden (by positivity)]
  have hpowN : (2 : ℝ) ^ N / (2 : ℝ) ^ k = (2 : ℝ) ^ (N - k) := by
    rw [div_eq_iff (by positivity : (2 : ℝ) ^ k ≠ 0), ← pow_add, Nat.sub_add_cancel hkN]
  rw [hpowN, one_mul]
  have hmul1 : (2 : ℝ) ^ m * (2 : ℝ) ^ (k - m) = (2 : ℝ) ^ k := by
    rw [← pow_add, Nat.add_sub_of_le hmk.le]
  have hmul2 : (2 : ℝ) ^ (N - k) * (2 : ℝ) ^ k = (2 : ℝ) ^ N := by
    rw [← pow_add, Nat.sub_add_cancel hkN]
  have hm1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hkm1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k - m) := one_le_pow₀ (by norm_num)
  have hNk1 : (1 : ℝ) ≤ (2 : ℝ) ^ (N - k) := one_le_pow₀ (by norm_num)
  nlinarith

/-- **Exact Dirichlet Green's identity for the centred ramp on `[x, 2^N * x]`:**
reconstructs `rampG (2^m * x)` (`0 ≤ m ≤ N`, `1 ≤ N`) from convex boundary weights on
`rampG x` and `rampG (2^N * x)` and the interior tent margins `D (2^(k + 1) * x)` (`1 ≤ k < N`). -/
theorem rampG_dyadic_dirichlet_green {x : ℝ} (hx : 0 < x) {N m : ℕ} (hN : 1 ≤ N) (hm : m ≤ N) :
    ZetaShared.rampG ((2 : ℝ) ^ m * x) =
      (((2 : ℝ) ^ N - (2 : ℝ) ^ m) / ((2 : ℝ) ^ N - 1)) * ZetaShared.rampG x +
      (((2 : ℝ) ^ m - 1) / ((2 : ℝ) ^ N - 1)) * ZetaShared.rampG ((2 : ℝ) ^ N * x) +
      ∑ k ∈ Ico 1 N,
        dyadicGreenKernel N m k * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (k + 1) * x) := by
  have hden : (2 : ℝ) ^ N - 1 ≠ 0 := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
    linarith
  have cm := rampG_dyadic_cauchy hx m
  have cN := rampG_dyadic_cauchy hx N
  have hcomb :
      ((2 : ℝ) ^ N - 1) * (ZetaShared.rampG ((2 : ℝ) ^ m * x) - ZetaShared.rampG x) -
        ((2 : ℝ) ^ m - 1) * (ZetaShared.rampG ((2 : ℝ) ^ N * x) - ZetaShared.rampG x) =
      ((2 : ℝ) ^ m - 1) *
          (∑ j ∈ range N,
            ((2 : ℝ) ^ N / (2 : ℝ) ^ (j + 1) - 1) *
              RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 2) * x)) -
        ((2 : ℝ) ^ N - 1) *
          (∑ j ∈ range m,
            ((2 : ℝ) ^ m / (2 : ℝ) ^ (j + 1) - 1) *
              RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 2) * x)) := by
    linear_combination ((2 : ℝ) ^ N - 1) * cm - ((2 : ℝ) ^ m - 1) * cN
  rw [← sum_range_add_sum_Ico _ hm] at hcomb
  have hgreen_sum :
      ∑ k ∈ Ico 1 N,
          dyadicGreenKernel N m k * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (k + 1) * x) =
        ∑ j ∈ range N,
          dyadicGreenKernel N m (j + 1) * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 2) * x) := by
    have hzero : dyadicGreenKernel N m N = 0 := by
      unfold dyadicGreenKernel
      split_ifs with hNm
      · have hmN_eq : m = N := le_antisymm hm hNm
        simp [hmN_eq]
      · simp
    have hN_pred : N = (N - 1) + 1 := by omega
    conv_rhs => rw [hN_pred, sum_range_succ, ← hN_pred, hzero, zero_mul, add_zero]
    rw [sum_Ico_eq_sum_range]
    refine sum_congr rfl fun j _ => ?_
    rw [show 1 + j = j + 1 by omega, show j + 1 + 1 = j + 2 by omega]
  rw [hgreen_sum, ← sum_range_add_sum_Ico _ hm]
  have hleft :
      ∑ j ∈ range m,
          dyadicGreenKernel N m (j + 1) * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 2) * x) =
        (1 / ((2 : ℝ) ^ N - 1)) *
          (((2 : ℝ) ^ m - 1) *
              (∑ j ∈ range m,
                ((2 : ℝ) ^ N / (2 : ℝ) ^ (j + 1) - 1) *
                  RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 2) * x)) -
            ((2 : ℝ) ^ N - 1) *
              (∑ j ∈ range m,
                ((2 : ℝ) ^ m / (2 : ℝ) ^ (j + 1) - 1) *
                  RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 2) * x))) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hjm : j + 1 ≤ m := Nat.succ_le_of_lt (mem_range.mp hj)
    unfold dyadicGreenKernel
    rw [if_pos hjm]
    have hp : (2 : ℝ) ^ (j + 1) ≠ 0 := by positivity
    field_simp [hden, hp]
    ring
  have hright :
      ∑ j ∈ Ico m N,
          dyadicGreenKernel N m (j + 1) * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 2) * x) =
        (1 / ((2 : ℝ) ^ N - 1)) *
          (((2 : ℝ) ^ m - 1) *
            ∑ j ∈ Ico m N,
              ((2 : ℝ) ^ N / (2 : ℝ) ^ (j + 1) - 1) *
                RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (j + 2) * x)) := by
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hmj : m ≤ j := (mem_Ico.mp hj).1
    unfold dyadicGreenKernel
    rw [if_neg (by omega : ¬ j + 1 ≤ m)]
    field_simp [hden]
  rw [hleft, hright]
  have hdiv := congrArg (fun t => (1 / ((2 : ℝ) ^ N - 1)) * t) hcomb
  field_simp [hden] at hdiv ⊢
  linarith

/-! ### 4. Uniform `N`-Independent Power-Bound Transfer and Good Boundary Points -/

/-- **Uniform `N`-independent dyadic power bound (`θ ∈ (0, 1)`):**
upper bounds `rampG x ≤ c₀ * x^θ` and `rampG (2^N * x) ≤ c₀ * (2^N * x)^θ` at the two ends
of `[x, 2^N * x]`, together with `D (2^(k + 1) * x) ≤ C_D * (2^(k + 1) * x)^θ` at the `N - 1`
interior dyadic scales, imply `rampG (2^m * x) ≤ C(θ) * (2^m * x)^θ` at **every** `0 ≤ m ≤ N`
with constant independent of `N`. -/
theorem rampG_dyadic_power_bound_of_dirichlet {x θ c₀ C_D : ℝ}
    (hx : 0 < x) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hc0 : 0 ≤ c₀) (hCD : 0 ≤ C_D)
    {N m : ℕ} (hN : 1 ≤ N) (hm : m ≤ N)
    (hlo : ZetaShared.rampG x ≤ c₀ * x ^ θ)
    (hhi : ZetaShared.rampG ((2 : ℝ) ^ N * x) ≤ c₀ * ((2 : ℝ) ^ N * x) ^ θ)
    (hint : ∀ k ∈ Ico 1 N,
      RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (k + 1) * x) ≤
        C_D * ((2 : ℝ) ^ (k + 1) * x) ^ θ) :
    ZetaShared.rampG ((2 : ℝ) ^ m * x) ≤
      (2 * c₀ + C_D * ((4 : ℝ) ^ θ / ((2 : ℝ) ^ θ - 1) + (4 : ℝ) ^ θ / (2 - (2 : ℝ) ^ θ))) *
        ((2 : ℝ) ^ m * x) ^ θ := by
  have hden : 0 < (2 : ℝ) ^ N - 1 := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
    linarith
  have h2θ_gt : 1 < (2 : ℝ) ^ θ := Real.one_lt_rpow (by norm_num) hθ0
  have h2θ_lt : (2 : ℝ) ^ θ < 2 := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hθ1
  have hscale_pos : 0 < ((2 : ℝ) ^ m * x) ^ θ := Real.rpow_pos_of_pos (by positivity) θ
  rw [rampG_dyadic_dirichlet_green hx hN hm]
  -- 1. First boundary term ≤ c₀ * (2^m * x)^θ
  have hb1_w0 : 0 ≤ ((2 : ℝ) ^ N - (2 : ℝ) ^ m) / ((2 : ℝ) ^ N - 1) :=
    div_nonneg (sub_nonneg.mpr (pow_le_pow_right₀ (by norm_num) hm)) hden.le
  have hb1_w1 : ((2 : ℝ) ^ N - (2 : ℝ) ^ m) / ((2 : ℝ) ^ N - 1) ≤ 1 := by
    rw [div_le_one hden]
    linarith [one_le_pow₀ (n := m) (by norm_num : (1 : ℝ) ≤ 2)]
  have hx_le_mx : x ^ θ ≤ ((2 : ℝ) ^ m * x) ^ θ := by
    apply Real.rpow_le_rpow hx.le _ hθ0.le
    have : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have hb1 : (((2 : ℝ) ^ N - (2 : ℝ) ^ m) / ((2 : ℝ) ^ N - 1)) * ZetaShared.rampG x ≤
      c₀ * ((2 : ℝ) ^ m * x) ^ θ := by
    calc (((2 : ℝ) ^ N - (2 : ℝ) ^ m) / ((2 : ℝ) ^ N - 1)) * ZetaShared.rampG x
        ≤ (((2 : ℝ) ^ N - (2 : ℝ) ^ m) / ((2 : ℝ) ^ N - 1)) * (c₀ * x ^ θ) :=
          mul_le_mul_of_nonneg_left hlo hb1_w0
      _ ≤ 1 * (c₀ * ((2 : ℝ) ^ m * x) ^ θ) :=
          mul_le_mul hb1_w1 (mul_le_mul_of_nonneg_left hx_le_mx hc0)
            (mul_nonneg hc0 (Real.rpow_nonneg hx.le θ)) zero_le_one
      _ = c₀ * ((2 : ℝ) ^ m * x) ^ θ := one_mul _
  -- 2. Second boundary term ≤ c₀ * (2^m * x)^θ
  have hb2_w0 : 0 ≤ ((2 : ℝ) ^ m - 1) / ((2 : ℝ) ^ N - 1) :=
    div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num))) hden.le
  have hb2_wpow : ((2 : ℝ) ^ m - 1) / ((2 : ℝ) ^ N - 1) ≤ (2 : ℝ) ^ m / (2 : ℝ) ^ N := by
    rw [div_le_div_iff₀ hden (by positivity)]
    have hm_le : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hm
    linarith
  have hpow_N_m : ((2 : ℝ) ^ m / (2 : ℝ) ^ N) * ((2 : ℝ) ^ N * x) ^ θ ≤
      ((2 : ℝ) ^ m * x) ^ θ := by
    rw [Real.mul_rpow (by positivity) hx.le, Real.mul_rpow (by positivity) hx.le]
    have hsub : ((2 : ℝ) ^ m / (2 : ℝ) ^ N) * ((2 : ℝ) ^ N) ^ θ ≤ ((2 : ℝ) ^ m) ^ θ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ N)]
      have hNm : N = m + (N - m) := (Nat.add_sub_of_le hm).symm
      rw [hNm, pow_add (2 : ℝ) m (N - m), Real.mul_rpow (by positivity) (by positivity)]
      have hd_le : ((2 : ℝ) ^ (N - m)) ^ θ ≤ (2 : ℝ) ^ (N - m) := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (N - m) := one_le_pow₀ (by norm_num)
        simpa using Real.rpow_le_rpow_of_exponent_le h1 hθ1.le
      calc (2 : ℝ) ^ m * (((2 : ℝ) ^ m) ^ θ * ((2 : ℝ) ^ (N - m)) ^ θ)
          = (((2 : ℝ) ^ m) ^ θ * (2 : ℝ) ^ m) * ((2 : ℝ) ^ (N - m)) ^ θ := by ring
        _ ≤ (((2 : ℝ) ^ m) ^ θ * (2 : ℝ) ^ m) * (2 : ℝ) ^ (N - m) :=
            mul_le_mul_of_nonneg_left hd_le (by positivity)
        _ = ((2 : ℝ) ^ m) ^ θ * ((2 : ℝ) ^ m * (2 : ℝ) ^ (N - m)) := by ring
    calc ((2 : ℝ) ^ m / (2 : ℝ) ^ N) * (((2 : ℝ) ^ N) ^ θ * x ^ θ)
        = (((2 : ℝ) ^ m / (2 : ℝ) ^ N) * ((2 : ℝ) ^ N) ^ θ) * x ^ θ := by ring
      _ ≤ ((2 : ℝ) ^ m) ^ θ * x ^ θ :=
          mul_le_mul_of_nonneg_right hsub (Real.rpow_nonneg hx.le θ)
  have hb2 : (((2 : ℝ) ^ m - 1) / ((2 : ℝ) ^ N - 1)) * ZetaShared.rampG ((2 : ℝ) ^ N * x) ≤
      c₀ * ((2 : ℝ) ^ m * x) ^ θ := by
    calc (((2 : ℝ) ^ m - 1) / ((2 : ℝ) ^ N - 1)) * ZetaShared.rampG ((2 : ℝ) ^ N * x)
        ≤ (((2 : ℝ) ^ m - 1) / ((2 : ℝ) ^ N - 1)) * (c₀ * ((2 : ℝ) ^ N * x) ^ θ) :=
          mul_le_mul_of_nonneg_left hhi hb2_w0
      _ ≤ ((2 : ℝ) ^ m / (2 : ℝ) ^ N) * (c₀ * ((2 : ℝ) ^ N * x) ^ θ) :=
          mul_le_mul_of_nonneg_right hb2_wpow (mul_nonneg hc0 (by positivity))
      _ = c₀ * (((2 : ℝ) ^ m / (2 : ℝ) ^ N) * ((2 : ℝ) ^ N * x) ^ θ) := by ring
      _ ≤ c₀ * ((2 : ℝ) ^ m * x) ^ θ := mul_le_mul_of_nonneg_left hpow_N_m hc0
  -- 3. Interior Green's sum bound
  have hint_step :
      ∑ k ∈ Ico 1 N,
          dyadicGreenKernel N m k * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (k + 1) * x) ≤
        C_D * ∑ k ∈ Ico 1 N, dyadicGreenKernel N m k * ((2 : ℝ) ^ (k + 1) * x) ^ θ := by
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    have hkN : k ≤ N := (mem_Ico.mp hk).2.le
    have hgk := dyadicGreenKernel_nonneg hN hm hkN
    calc dyadicGreenKernel N m k * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (k + 1) * x)
        ≤ dyadicGreenKernel N m k * (C_D * ((2 : ℝ) ^ (k + 1) * x) ^ θ) :=
          mul_le_mul_of_nonneg_left (hint k hk) hgk
      _ = C_D * (dyadicGreenKernel N m k * ((2 : ℝ) ^ (k + 1) * x) ^ θ) := by ring
  -- Split Ico 1 N into k ≤ m and m < k via filter
  have hsplit_filter :
      ∑ k ∈ Ico 1 N, dyadicGreenKernel N m k * ((2 : ℝ) ^ (k + 1) * x) ^ θ =
        (∑ k ∈ (Ico 1 N).filter (· ≤ m),
            dyadicGreenKernel N m k * ((2 : ℝ) ^ (k + 1) * x) ^ θ) +
        (∑ k ∈ (Ico 1 N).filter (fun k => ¬ k ≤ m),
            dyadicGreenKernel N m k * ((2 : ℝ) ^ (k + 1) * x) ^ θ) :=
    (sum_filter_add_sum_filter_not (Ico 1 N) (· ≤ m) _).symm
  -- 3a. Lower interior sum (k ≤ m)
  have rpow_two_pow (k : ℕ) : ((2 : ℝ) ^ k) ^ θ = ((2 : ℝ) ^ θ) ^ k := by
    rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_natCast ((2 : ℝ) ^ θ) k,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
  have hlow_sub : (Ico 1 N).filter (· ≤ m) ⊆ Ico 1 (m + 1) := by
    intro k hk
    obtain ⟨hk1, hkm⟩ := mem_filter.mp hk
    exact mem_Ico.mpr ⟨(mem_Ico.mp hk1).1, Nat.lt_succ_of_le hkm⟩
  have hlow_bound :
      ∑ k ∈ (Ico 1 N).filter (· ≤ m),
          dyadicGreenKernel N m k * ((2 : ℝ) ^ (k + 1) * x) ^ θ ≤
        ((4 : ℝ) ^ θ / ((2 : ℝ) ^ θ - 1)) * ((2 : ℝ) ^ m * x) ^ θ := by
    calc ∑ k ∈ (Ico 1 N).filter (· ≤ m),
            dyadicGreenKernel N m k * ((2 : ℝ) ^ (k + 1) * x) ^ θ
        ≤ ∑ k ∈ (Ico 1 N).filter (· ≤ m), ((2 : ℝ) ^ (k + 1) * x) ^ θ := by
          refine sum_le_sum fun k hk => ?_
          have hkm : k ≤ m := (mem_filter.mp hk).2
          exact mul_le_of_le_one_left (by positivity) (dyadicGreenKernel_le_one hN le_rfl hkm hm)
      _ ≤ ∑ k ∈ Ico 1 (m + 1), ((2 : ℝ) ^ (k + 1) * x) ^ θ :=
          sum_le_sum_of_subset_of_nonneg hlow_sub (fun _ _ _ => by positivity)
      _ = ∑ j ∈ range m, ((2 : ℝ) ^ (j + 2) * x) ^ θ := by
          rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel]
          refine sum_congr rfl fun j _ => by rw [show 1 + j + 1 = j + 2 by omega]
      _ = (4 : ℝ) ^ θ * x ^ θ * ∑ j ∈ range m, ((2 : ℝ) ^ θ) ^ j := by
          rw [mul_sum]
          refine sum_congr rfl fun j _ => ?_
          have hrewrite : (2 : ℝ) ^ (j + 2) * x = 4 * x * (2 : ℝ) ^ j := by
            rw [pow_add]; norm_num; ring
          rw [hrewrite, Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by norm_num) hx.le, rpow_two_pow j]
      _ = (4 : ℝ) ^ θ * x ^ θ * ((((2 : ℝ) ^ θ) ^ m - 1) / ((2 : ℝ) ^ θ - 1)) := by
          rw [geom_sum_eq (by linarith : (2 : ℝ) ^ θ ≠ 1)]
      _ ≤ (4 : ℝ) ^ θ * x ^ θ * (((2 : ℝ) ^ θ) ^ m / ((2 : ℝ) ^ θ - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_right (by linarith) (by linarith)
      _ = ((4 : ℝ) ^ θ / ((2 : ℝ) ^ θ - 1)) * ((2 : ℝ) ^ m * x) ^ θ := by
          have hm_pow : ((2 : ℝ) ^ θ) ^ m * x ^ θ = ((2 : ℝ) ^ m * x) ^ θ := by
            rw [Real.mul_rpow (by positivity) hx.le, rpow_two_pow m]
          calc (4 : ℝ) ^ θ * x ^ θ * (((2 : ℝ) ^ θ) ^ m / ((2 : ℝ) ^ θ - 1))
              = ((4 : ℝ) ^ θ / ((2 : ℝ) ^ θ - 1)) * (((2 : ℝ) ^ θ) ^ m * x ^ θ) := by ring
            _ = ((4 : ℝ) ^ θ / ((2 : ℝ) ^ θ - 1)) * ((2 : ℝ) ^ m * x) ^ θ := by rw [hm_pow]
  -- 3b. Upper interior sum (m < k < N)
  have hhigh_sub : (Ico 1 N).filter (fun k => ¬ k ≤ m) ⊆ Ico (m + 1) (m + 1 + N) := by
    intro k hk
    obtain ⟨hk1, hkm⟩ := mem_filter.mp hk
    have hkN := (mem_Ico.mp hk1).2
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hhigh_bound :
      ∑ k ∈ (Ico 1 N).filter (fun k => ¬ k ≤ m),
          dyadicGreenKernel N m k * ((2 : ℝ) ^ (k + 1) * x) ^ θ ≤
        ((4 : ℝ) ^ θ / (2 - (2 : ℝ) ^ θ)) * ((2 : ℝ) ^ m * x) ^ θ := by
    let q : ℝ := (2 : ℝ) ^ θ / 2
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hq1 : q < 1 := by dsimp [q]; rw [div_lt_one (by norm_num)]; exact h2θ_lt
    calc ∑ k ∈ (Ico 1 N).filter (fun k => ¬ k ≤ m),
            dyadicGreenKernel N m k * ((2 : ℝ) ^ (k + 1) * x) ^ θ
        ≤ ∑ k ∈ (Ico 1 N).filter (fun k => ¬ k ≤ m),
            (1 / (2 : ℝ) ^ (k - m)) * ((2 : ℝ) ^ (k + 1) * x) ^ θ := by
          refine sum_le_sum fun k hk => ?_
          obtain ⟨hk1, hkm⟩ := mem_filter.mp hk
          exact mul_le_mul_of_nonneg_right
            (dyadicGreenKernel_le_pow_sub hN (by omega) (mem_Ico.mp hk1).2.le) (by positivity)
      _ ≤ ∑ k ∈ Ico (m + 1) (m + 1 + N),
            (1 / (2 : ℝ) ^ (k - m)) * ((2 : ℝ) ^ (k + 1) * x) ^ θ :=
          sum_le_sum_of_subset_of_nonneg hhigh_sub (fun _ _ _ => by positivity)
      _ = ∑ r ∈ range N,
            (1 / (2 : ℝ) ^ (r + 1)) * ((2 : ℝ) ^ (m + 2 + r) * x) ^ θ := by
          rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
          refine sum_congr rfl fun r _ => ?_
          rw [show m + 1 + r - m = r + 1 by omega, show m + 1 + r + 1 = m + 2 + r by omega]
      _ = ((4 : ℝ) ^ θ / 2) * ((2 : ℝ) ^ m * x) ^ θ * ∑ r ∈ range N, q ^ r := by
          rw [mul_sum]
          refine sum_congr rfl fun r _ => ?_
          have hrewrite : (2 : ℝ) ^ (m + 2 + r) * x = ((2 : ℝ) ^ m * x) * 4 * (2 : ℝ) ^ r := by
            rw [pow_add, pow_add]; norm_num; ring
          have hr_pow : ((2 : ℝ) ^ r) ^ θ / (2 : ℝ) ^ r = q ^ r := by
            dsimp [q]
            rw [div_pow, rpow_two_pow r]
          rw [hrewrite, Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by norm_num), pow_succ]
          calc (1 / ((2 : ℝ) ^ r * 2)) * (((2 : ℝ) ^ m * x) ^ θ * (4 : ℝ) ^ θ * ((2 : ℝ) ^ r) ^ θ)
              = ((4 : ℝ) ^ θ / 2) * ((2 : ℝ) ^ m * x) ^ θ * (((2 : ℝ) ^ r) ^ θ / (2 : ℝ) ^ r) := by
                field_simp
            _ = ((4 : ℝ) ^ θ / 2) * ((2 : ℝ) ^ m * x) ^ θ * q ^ r := by rw [hr_pow]
      _ = ((4 : ℝ) ^ θ / 2) * ((2 : ℝ) ^ m * x) ^ θ * ((1 - q ^ N) / (1 - q)) := by
          rw [geom_sum_eq (by linarith : q ≠ 1),
            show (q ^ N - 1) / (q - 1) = (1 - q ^ N) / (1 - q) by
              have : q - 1 ≠ 0 := by linarith
              have : 1 - q ≠ 0 := by linarith
              field_simp; ring]
      _ ≤ ((4 : ℝ) ^ θ / 2) * ((2 : ℝ) ^ m * x) ^ θ * (1 / (1 - q)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine div_le_div_of_nonneg_right ?_ (by linarith)
          have : 0 ≤ q ^ N := pow_nonneg hq0 N
          linarith
      _ = ((4 : ℝ) ^ θ / (2 - (2 : ℝ) ^ θ)) * ((2 : ℝ) ^ m * x) ^ θ := by
          dsimp [q]
          have : 2 - (2 : ℝ) ^ θ ≠ 0 := by linarith
          field_simp
  have hint_total :
      ∑ k ∈ Ico 1 N,
          dyadicGreenKernel N m k * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (k + 1) * x) ≤
        C_D * (((4 : ℝ) ^ θ / ((2 : ℝ) ^ θ - 1) + (4 : ℝ) ^ θ / (2 - (2 : ℝ) ^ θ)) *
          ((2 : ℝ) ^ m * x) ^ θ) := by
    calc ∑ k ∈ Ico 1 N,
            dyadicGreenKernel N m k * RiemannReduction.DivisorBand.D ((2 : ℝ) ^ (k + 1) * x)
        ≤ C_D * ∑ k ∈ Ico 1 N, dyadicGreenKernel N m k * ((2 : ℝ) ^ (k + 1) * x) ^ θ := hint_step
      _ = C_D * ((∑ k ∈ (Ico 1 N).filter (· ≤ m),
              dyadicGreenKernel N m k * ((2 : ℝ) ^ (k + 1) * x) ^ θ) +
            (∑ k ∈ (Ico 1 N).filter (fun k => ¬ k ≤ m),
              dyadicGreenKernel N m k * ((2 : ℝ) ^ (k + 1) * x) ^ θ)) := by rw [hsplit_filter]
      _ ≤ C_D * (((4 : ℝ) ^ θ / ((2 : ℝ) ^ θ - 1)) * ((2 : ℝ) ^ m * x) ^ θ +
            ((4 : ℝ) ^ θ / (2 - (2 : ℝ) ^ θ)) * ((2 : ℝ) ^ m * x) ^ θ) :=
          mul_le_mul_of_nonneg_left (add_le_add hlow_bound hhigh_bound) hCD
      _ = C_D * (((4 : ℝ) ^ θ / ((2 : ℝ) ^ θ - 1) + (4 : ℝ) ^ θ / (2 - (2 : ℝ) ^ θ)) *
            ((2 : ℝ) ^ m * x) ^ θ) := by ring
  linarith

/-! ### 5. Unconditional Existence of Good Boundary Points on Late Power Windows -/

private theorem neg_poleData {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
    (p : ZetaShared.PoleData g Φ Z) (h : ∀ z ∈ Z, z.im ≠ 0) :
    ZetaShared.PoleData (fun u => -g u) (fun s => -Φ s) Z := by
  obtain ⟨C, hC⟩ := p.growth
  refine ⟨p.meas.neg, ⟨C, fun u hu => by simpa using hC u hu⟩, ?_, p.pos, p.diff.neg, p.iso, ?_⟩
  · intro s hs
    simpa [p.laplace s hs] using
      (integral_neg (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (fun u : ℝ => (g u : ℂ) * cexp (-s * u))).symm
  · intro ρ hρ
    obtain ⟨a, ha, _, f, hf, he⟩ := p.pole ρ hρ
    refine ⟨-a, neg_ne_zero.mpr ha, fun hi => False.elim (h ρ hρ hi), fun s => -f s, hf.neg, ?_⟩
    filter_upwards [he] with s hs
    rw [hs]; ring

private theorem add_exp_pole {g : ℝ → ℝ} {F : ℂ → ℂ} {Z : Set ℂ}
    (p : ZetaShared.PoleData g F Z) {a c : ℝ} (ha : 0 < a) (ha2 : a < 2) (hc : 0 < c)
    (regular : (a : ℂ) ∉ Z) :
    ZetaShared.PoleData (fun u => g u + c * Real.exp (a * u))
      (fun s => F s + (c : ℂ) / (s - a)) (insert (a : ℂ) Z) := by
  obtain ⟨C, growth⟩ := p.growth
  have reg : AnalyticAt ℂ F (a : ℂ) := by
    apply p.diff.analyticAt
    filter_upwards [isOpen_lt continuous_const continuous_re |>.mem_nhds
      (show 0 < (a : ℂ).re from ha), eventually_nhdsWithin_iff.mp (p.iso a ha)] with z hz hz'
    exact ⟨hz, by rcases eq_or_ne z a with rfl | h; exact regular; exact hz' h⟩
  refine ⟨p.meas.add (by fun_prop), ⟨C + c, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have e := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha2.le hu)
    exact (abs_add_le _ _).trans (by
      rw [abs_of_pos (mul_pos hc (Real.exp_pos _)), add_mul]
      exact add_le_add (growth _ hu) (mul_le_mul_of_nonneg_left e hc.le))
  · intro s hs
    have hi : IntegrableOn (fun u : ℝ => (g u : ℂ) * cexp (-s * u)) (Set.Ioi 0) := by
      let b := s.re - 2
      have hb : 0 < b := by dsimp [b]; linarith
      apply Integrable.mono' ((ZetaShared.iteratedDeriv_laplace_int 0 b hb).const_mul C)
      · apply Measurable.aestronglyMeasurable
        have := p.meas
        fun_prop
      · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => by
          simpa using ZetaShared.iteratedDeriv_laplace_bound g C growth 0 b s
            (by dsimp [b]; linarith) u hu)
    have neg : ((a : ℂ) - s).re < 0 := by simp; linarith
    have he (u : ℝ) : ((g u + c * Real.exp (a * u) : ℝ) : ℂ) * cexp (-s * u) =
        (g u : ℂ) * cexp (-s * u) + (c : ℂ) * cexp (((a : ℂ) - s) * u) := by
      push_cast
      rw [add_mul, mul_assoc, ← Complex.exp_add]
      congr 3
      ring
    simp_rw [he]
    rw [integral_add hi ((integrableOn_exp_mul_complex_Ioi neg 0).const_mul (c : ℂ)),
      ← p.laplace s hs, integral_const_mul, integral_exp_mul_complex_Ioi neg]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show (a : ℂ) - s = -(s - a) by ring]
    simp only [div_eq_mul_inv, inv_neg, neg_mul, mul_neg, neg_neg, one_mul]
  · intro z hz
    rcases hz with h | h
    · simpa [h] using ha
    · exact p.pos z h
  · intro z hz
    have hza : z ≠ (a : ℂ) := fun e => hz.2 (Or.inl e)
    have divdiff : DifferentiableAt ℂ (fun s : ℂ => (c : ℂ) / (s - a)) z := by
      fun_prop (disch := exact sub_ne_zero.mpr hza)
    exact (p.diff z ⟨hz.1, fun h => hz.2 (Or.inr h)⟩).mono
      (fun _ h => ⟨h.1, fun hZ => h.2 (Or.inr hZ)⟩) |>.add
        divdiff.differentiableWithinAt
  · intro z hz
    have avoid : ∀ᶠ w in 𝓝[≠] z, w ≠ (a : ℂ) := by
      rcases eq_or_ne z a with rfl | ne
      · exact self_mem_nhdsWithin
      · exact eventually_ne_nhdsWithin ne
    filter_upwards [p.iso z hz, avoid] with w hw hn
    exact fun h => h.elim hn hw
  · intro z hz
    rcases hz with h | hz
    · subst z
      exact ⟨c, ofReal_ne_zero.mpr hc.ne', fun _ => ⟨hc, rfl⟩, F, reg,
        Eventually.of_forall fun _ => add_comm _ _⟩
    · have hza : z ≠ (a : ℂ) := fun e => regular (e ▸ hz)
      obtain ⟨r, hr, hreal, f, hf, he⟩ := p.pole z hz
      refine ⟨r, hr, hreal, fun s => f s + (c : ℂ) / (s - a),
        hf.add (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)), ?_⟩
      filter_upwards [he] with s hs
      rw [hs, add_assoc]

/-- Unconditionally (no zero-location hypothesis), every sufficiently late multiplicative
window `[Y, Y^(1 + δ)]` contains a point `x` with `rampG x < c * x^θ` (`0 < θ < 1`),
supplying good boundary points for the two-end Dirichlet reconstruction. -/
theorem good_rampG_point_on_late_windows {θ c δ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∃ x ∈ Set.Icc Y (Y ^ (1 + δ)), ZetaShared.rampG x < c * x ^ θ := by
  have hlog : ∃ U₀ : ℝ, ∀ U ≥ U₀, ∃ u ∈ Set.Icc U ((1 + δ) * U),
      ZetaShared.rampG (Real.exp u) < c * Real.exp (θ * u) := by
    obtain ⟨F, p⟩ := ZetaShared.zeta_poleData
    have reg : (θ : ℂ) ∉ ZetaShared.zetaZeros := fun mem =>
      ZetaShared.zetaZeros_not_real (θ : ℂ) mem (by simp)
    have pole := add_exp_pole (neg_poleData p ZetaShared.zetaZeros_not_real)
      hθ0 (by linarith : θ < 2) hc reg
    by_contra! bad
    have window : ZetaShared.WindowHypU
        (fun u => -(ZetaShared.zetaLogRamp u) + c * Real.exp (θ * u)) (θ / 2) δ := by
      intro η _ U₀
      obtain ⟨U, hU, h⟩ := bad U₀
      refine ⟨U, hU, fun _ => 0, by simp, fun u hu => ⟨le_rfl, ?_⟩,
        by simpa using (Real.exp_pos (η * U)).le⟩
      have h' := h u hu
      unfold ZetaShared.zetaLogRamp
      linarith
    have impossible := ZetaShared.landau_window pole (half_pos hθ0) (by linarith) hδ window
      (θ : ℂ) (Set.mem_insert _ _)
    change θ ≤ θ / 2 at impossible
    linarith
  obtain ⟨U₀, all⟩ := hlog
  refine ⟨Real.exp U₀, fun Y hY => ?_⟩
  have pos : 0 < Y := (Real.exp_pos _).trans_le hY
  have late : U₀ ≤ Real.log Y := (Real.le_log_iff_exp_le pos).2 hY
  obtain ⟨u, hu, hg⟩ := all (Real.log Y) late
  refine ⟨Real.exp u, ⟨(Real.log_le_iff_le_exp pos).1 hu.1, ?_⟩, ?_⟩
  · rw [Real.rpow_def_of_pos pos]
    exact Real.exp_le_exp.mpr (by linarith [hu.2])
  · simpa [Real.rpow_def_of_pos (Real.exp_pos _), mul_comm] using hg

#print axioms rampS_dyadic_reconstruction
#print axioms rampS_top_down_reconstruction
#print axioms rampG_dyadic_reconstruction_bottom
#print axioms rampG_top_down_reconstruction
#print axioms rampG_dyadic_reconstruction_two_end
#print axioms rampG_dyadic_dirichlet_green
#print axioms rampG_dyadic_power_bound_of_dirichlet
#print axioms good_rampG_point_on_late_windows

end Crossley
end
