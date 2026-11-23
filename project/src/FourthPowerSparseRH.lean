import ArchiveFreeBadMeasure
import ArchiveFreeWindowTo298
import DirectRampConvexity

/-!
# Fourth-Power (`k^4`) Sparse-Failure Characterization of `RiemannHypothesis` and `2.98` Transfer

This module extends sparse sample-failure counting for `IndependentLandau.rampG` from fifteenth
powers (`θ > 13/15`, which cannot reach `θ → 1/2`) to **fourth powers `x_k = (k : ℝ)^4`** across
the entire critical strip `θ ∈ (1/2, 1)`, and more generally to **arbitrary integer powers `k^r`**
(`r ≥ 4`, `1 - 2 / r < θ < 1`), 100% from Mathlib `0df444a360ea` and first-party Mathlib-only
modules:

1. **Why `k^4` Reaches `θ > 1/2` (`fourthPower_step_le`, `fourthPower_secant_excess_le`):**
   On `[k^4, (k + 1)^4]` (`k ≥ 1`), the step is `(k + 1)^4 - k^4 ≤ 15 * k^3`, so by
   `DirectRampConvexity.rampG_le_max_add_sq` the secant excess is at most
   `((k + 1)^4 - k^4)^2 / (4 * k^4) ≤ (225 / 4) * k^2 = (225 / 4) * ((k^4)^(1/2))`, which is
   `o((k^4)^θ)` for **every** `θ ∈ (1/2, 1)`.
2. **Unified `r`-th Power & Fourth-Power Zero-Free Criteria
   (`general_power_zeroFree_of_sparse_failures`, `zeroFree_of_fourthPower_sparse_failures`):**
   For any `r ≥ 4` and `1 - 2 / r < θ < 1` (recovering `r = 4 → θ > 1/2` and `r = 15 → θ > 13/15`),
   at most `L^(3 - ε)` sample failures on `Finset.Icc (L^2) (L^3)` along cofinally many `L` forces
   `riemannZeta s ≠ 0` on `Re s > θ`.
3. **Full `RiemannHypothesis` Equivalence (`rh_iff_fourthPower_sparse_failures`,
   `rh_iff_fourthPower_sparse_failures_fixed`, `rh_iff_fourthPower_eventually_zero`):**
   Characterizes `RiemannHypothesis` both existentially (`∃ ε > 0, ∃ c ≥ 0`) and at any fixed
   `c > 0`, `ε ∈ (0, 3)` (under `RiemannHypothesis`, `fourthPowerFailures θ c L = 0` for all
   sufficiently large `L`).
4. **Archive-Free `2.98` (`149/50`) Shell Benchmark Transfer
   (`archiveFree_298_of_fourthPower_sparse_failures`,
   `archiveFree_298_of_fourthPower_sparse_08699`):**
   Deduces both `∀ᶠ x in atTop, |rampG x| ≤ (1/2) * x^(87/100)` and
   `∀ᶠ m in atTop, weighted uniformShellScore m ≤ m^(149/50)` from `≤ L^(299/100)` fourth-power
   sample failures at `θ = 8699/10000`, `c = 1/2`.
-/

open MeasureTheory Complex Set Filter Topology Finset
open RiemannReduction.ShortTail.LossFrequency

noncomputable section

namespace FourthPowerSparseRH

/-! ### 1. Sample-Failure Definitions and Fourth-Power Secant Geometry -/

/-- Indices `k ∈ [L, H]` where the `r`-th power sample `(k : ℝ)^r` exceeds `c * ((k : ℝ)^r)^θ`. -/
def powerBadIndices (r : ℕ) (θ c : ℝ) (L H : ℕ) : Finset ℕ :=
  (Finset.Icc L H).filter
    (fun k : ℕ => c * ((k : ℝ) ^ r) ^ θ < IndependentLandau.rampG ((k : ℝ) ^ r))

/-- Count of `r`-th power sample failures on `Finset.Icc (L^2) (L^3)`. -/
def powerFailures (r : ℕ) (θ c : ℝ) (L : ℕ) : ℕ :=
  ((Finset.Icc (L ^ 2) (L ^ 3)).filter
    (fun k : ℕ => c * ((k : ℝ) ^ r) ^ θ < IndependentLandau.rampG ((k : ℝ) ^ r))).card

/-- Count of fourth-power (`k^4`) sample failures on `Finset.Icc (L^2) (L^3)`, spanning
`[L^8, L^12] = [Y, Y^(3/2)]` with `Y = (L : ℝ)^8`. -/
def fourthPowerFailures (θ c : ℝ) (L : ℕ) : ℕ :=
  ((Finset.Icc (L ^ 2) (L ^ 3)).filter
    (fun k : ℕ => c * ((k : ℝ) ^ 4) ^ θ < IndependentLandau.rampG ((k : ℝ) ^ 4))).card

lemma fourthPowerFailures_eq_powerFailures (θ c : ℝ) (L : ℕ) :
    fourthPowerFailures θ c L = powerFailures 4 θ c L := rfl

lemma powerFailures_eq_card (r : ℕ) (θ c : ℝ) (L : ℕ) :
    powerFailures r θ c L = (powerBadIndices r θ c (L ^ 2) (L ^ 3)).card := rfl

/-- Exact fourth-power step bound `(u + 1)^4 - u^4 = 4u^3 + 6u^2 + 4u + 1 ≤ 15 * u^3` for `u ≥ 1`. -/
theorem fourthPower_step_le {u : ℝ} (hu : 1 ≤ u) :
    (u + 1) ^ 4 - u ^ 4 ≤ 15 * u ^ 3 := by
  have hu2 : u ^ 2 ≤ u ^ 3 := by nlinarith
  have hu1 : u ≤ u ^ 3 := by nlinarith
  have hu0 : 1 ≤ u ^ 3 := by nlinarith
  have hexp : (u + 1) ^ 4 - u ^ 4 = 4 * u ^ 3 + 6 * u ^ 2 + 4 * u + 1 := by ring
  linarith

/-- On `[k^4, (k + 1)^4]` (`k ≥ 1`), `DirectRampConvexity.rampG_le_max_add_sq` bounds the secant
excess of `rampG` by `(225 / 4) * ((k^4)^(1/2))`, which is `o((k^4)^θ)` for every `θ > 1/2`. -/
theorem fourthPower_secant_excess_le {k : ℕ} {x : ℝ}
    (hk : 1 ≤ k) (hx : x ∈ Set.Icc ((k : ℝ) ^ 4) (((k : ℝ) + 1) ^ 4)) :
    IndependentLandau.rampG x ≤
      max (IndependentLandau.rampG ((k : ℝ) ^ 4))
          (IndependentLandau.rampG (((k : ℝ) + 1) ^ 4)) +
        (225 / 4 : ℝ) * (((k : ℝ) ^ 4) ^ (1 / 2 : ℝ)) := by
  let u : ℝ := (k : ℝ)
  have hu1 : 1 ≤ u := by dsimp [u]; exact_mod_cast hk
  have hu_pos : 0 < u := zero_lt_one.trans_le hu1
  have hu4_pos : 0 < u ^ 4 := pow_pos hu_pos 4
  have hmain := DirectRampConvexity.rampG_le_max_add_sq hu4_pos hx.1 hx.2
  have hstep_nn : 0 ≤ (u + 1) ^ 4 - u ^ 4 :=
    sub_nonneg.mpr (pow_le_pow_left₀ hu_pos.le (by linarith) 4)
  have hstep_sq : ((u + 1) ^ 4 - u ^ 4) ^ 2 ≤ (15 * u ^ 3) ^ 2 :=
    pow_le_pow_left₀ hstep_nn (fourthPower_step_le hu1) 2
  have herr : ((u + 1) ^ 4 - u ^ 4) ^ 2 / (4 * u ^ 4) ≤ (225 / 4 : ℝ) * u ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * u ^ 4)).mpr
    calc ((u + 1) ^ 4 - u ^ 4) ^ 2 ≤ (15 * u ^ 3) ^ 2 := hstep_sq
      _ = (225 / 4 : ℝ) * u ^ 2 * (4 * u ^ 4) := by ring
  have hrpow : (u ^ 4) ^ (1 / 2 : ℝ) = u ^ 2 := by
    rw [← Real.rpow_natCast_mul hu_pos.le]
    norm_num
  rw [hrpow]
  linarith

/-! ### 2. General `r`-th Power Cell Cover and Sparse-Failure Theorem (`r ≥ 4`) -/

/-- Secant-error constant `((r * 2^(r - 1))^2) / 4` for `r`-th power cells. -/
def powerGridCost (r : ℕ) : ℝ := ((r : ℝ) * (2 : ℝ) ^ (r - 1)) ^ 2 / 4

/-- Maximum cell width `r * (H + 1)^(r - 1)` across `k ≤ H`. -/
def powerGridRadius (r H : ℕ) : ℝ := (r : ℝ) * ((H : ℝ) + 1) ^ (r - 1)

private lemma power_step_le_radius {r k H : ℕ} (hkh : k ≤ H) :
    ((k : ℝ) + 1) ^ r - (k : ℝ) ^ r ≤ powerGridRadius r H := by
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk1_0 : 0 ≤ (k : ℝ) + 1 := by positivity
  have hinc : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hdif : 0 ≤ ((k : ℝ) + 1) ^ r - (k : ℝ) ^ r :=
    sub_nonneg.mpr (pow_le_pow_left₀ hk0 hinc r)
  have hp := abs_pow_sub_pow_le ((k : ℝ) + 1) (k : ℝ) r
  rw [abs_of_nonneg hdif, abs_of_nonneg hk1_0, abs_of_nonneg hk0,
    max_eq_left hinc, show (k : ℝ) + 1 - k = 1 by ring, abs_one, one_mul] at hp
  refine hp.trans ?_
  unfold powerGridRadius
  have hkH : (k : ℝ) + 1 ≤ (H : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hkh
  gcongr

private lemma power_secant_cost {r : ℕ} {u : ℝ} (hr : 2 ≤ r) (hu : 1 ≤ u) :
    ((u + 1) ^ r - u ^ r) ^ 2 / (4 * u ^ r) ≤ powerGridCost r * u ^ (r - 2) := by
  have u0 : 0 ≤ u := zero_le_one.trans hu
  have up : 0 < u := zero_lt_one.trans_le hu
  have u1 : 0 ≤ u + 1 := by positivity
  have inc : u ≤ u + 1 := by linarith
  have d : 0 ≤ (u + 1) ^ r - u ^ r := sub_nonneg.mpr (pow_le_pow_left₀ u0 inc r)
  have hp := abs_pow_sub_pow_le (u + 1) u r
  rw [abs_of_nonneg d, abs_of_nonneg u1, abs_of_nonneg u0,
    max_eq_left inc, show u + 1 - u = 1 by ring, abs_one, one_mul] at hp
  have du : (u + 1) ^ r - u ^ r ≤ ((r : ℝ) * (2 : ℝ) ^ (r - 1)) * u ^ (r - 1) := by
    calc (u + 1) ^ r - u ^ r
        ≤ (r : ℝ) * (u + 1) ^ (r - 1) := hp
      _ ≤ (r : ℝ) * (2 * u) ^ (r - 1) := by gcongr; linarith
      _ = ((r : ℝ) * (2 : ℝ) ^ (r - 1)) * u ^ (r - 1) := by rw [mul_pow]; ring
  have hsq := pow_le_pow_left₀ d du 2
  have hexp : (r - 1) * 2 = (r - 2) + r := by omega
  have hpow_u : (u ^ (r - 1)) ^ 2 = u ^ (r - 2) * u ^ r := by
    rw [← pow_mul, hexp, pow_add]
  apply (div_le_iff₀ (by positivity : 0 < 4 * u ^ r)).mpr
  calc ((u + 1) ^ r - u ^ r) ^ 2
      ≤ (((r : ℝ) * (2 : ℝ) ^ (r - 1)) * u ^ (r - 1)) ^ 2 := hsq
    _ = ((r : ℝ) * (2 : ℝ) ^ (r - 1)) ^ 2 * (u ^ (r - 1)) ^ 2 := by ring
    _ = ((r : ℝ) * (2 : ℝ) ^ (r - 1)) ^ 2 * (u ^ (r - 2) * u ^ r) := by rw [hpow_u]
    _ = powerGridCost r * u ^ (r - 2) * (4 * u ^ r) := by unfold powerGridCost; ring

/-- Cell majorant on `[u^r, (u + 1)^r]` directly from `DirectRampConvexity.rampG_le_max_add_sq`. -/
private lemma power_cell_majorant {r : ℕ} {u x c θ : ℝ}
    (hr : 2 ≤ r) (hu : 1 ≤ u) (hc : 0 ≤ c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hx : x ∈ Set.Icc (u ^ r) ((u + 1) ^ r))
    (hleft : IndependentLandau.rampG (u ^ r) ≤ c * (u ^ r) ^ θ)
    (hright : IndependentLandau.rampG ((u + 1) ^ r) ≤ c * ((u + 1) ^ r) ^ θ) :
    IndependentLandau.rampG x ≤ ((2 : ℝ) ^ r * c) * x ^ θ + powerGridCost r * u ^ (r - 2) := by
  have up : 0 < u := zero_lt_one.trans_le hu
  have ha_pos : 0 < u ^ r := pow_pos up r
  have hx_pos : 0 < x := ha_pos.trans_le hx.1
  have h1_2r : 1 ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hmain := DirectRampConvexity.rampG_le_max_add_sq ha_pos hx.1 hx.2
  have hm1 : IndependentLandau.rampG (u ^ r) ≤ ((2 : ℝ) ^ r * c) * x ^ θ := by
    have h1 : c * (u ^ r) ^ θ ≤ c * x ^ θ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha_pos.le hx.1 hθ0) hc
    have h2 : c * x ^ θ ≤ ((2 : ℝ) ^ r * c) * x ^ θ := by
      calc c * x ^ θ = 1 * (c * x ^ θ) := by ring
        _ ≤ (2 : ℝ) ^ r * (c * x ^ θ) :=
            mul_le_mul_of_nonneg_right h1_2r (mul_nonneg hc (Real.rpow_nonneg hx_pos.le θ))
        _ = ((2 : ℝ) ^ r * c) * x ^ θ := by ring
    exact hleft.trans (h1.trans h2)
  have hm2 : IndependentLandau.rampG ((u + 1) ^ r) ≤ ((2 : ℝ) ^ r * c) * x ^ θ := by
    have hb_le : (u + 1) ^ r ≤ (2 : ℝ) ^ r * x := by
      calc (u + 1) ^ r ≤ (2 * u) ^ r := pow_le_pow_left₀ (by positivity) (by linarith) r
        _ = (2 : ℝ) ^ r * u ^ r := by rw [mul_pow]
        _ ≤ (2 : ℝ) ^ r * x := mul_le_mul_of_nonneg_left hx.1 (by positivity)
    have h2r_θ : ((2 : ℝ) ^ r) ^ θ ≤ (2 : ℝ) ^ r := by
      calc ((2 : ℝ) ^ r) ^ θ ≤ ((2 : ℝ) ^ r) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1_2r hθ1
        _ = (2 : ℝ) ^ r := Real.rpow_one _
    have hrpow : ((u + 1) ^ r) ^ θ ≤ (2 : ℝ) ^ r * x ^ θ := by
      calc ((u + 1) ^ r) ^ θ ≤ ((2 : ℝ) ^ r * x) ^ θ :=
            Real.rpow_le_rpow (by positivity) hb_le hθ0
        _ = ((2 : ℝ) ^ r) ^ θ * x ^ θ := Real.mul_rpow (by positivity) hx_pos.le
        _ ≤ (2 : ℝ) ^ r * x ^ θ :=
            mul_le_mul_of_nonneg_right h2r_θ (Real.rpow_nonneg hx_pos.le θ)
    calc IndependentLandau.rampG ((u + 1) ^ r)
        ≤ c * ((u + 1) ^ r) ^ θ := hright
      _ ≤ c * ((2 : ℝ) ^ r * x ^ θ) := mul_le_mul_of_nonneg_left hrpow hc
      _ = ((2 : ℝ) ^ r * c) * x ^ θ := by ring
  have hmax := max_le hm1 hm2
  have hcost := power_secant_cost hr hu
  linarith

private lemma power_cell_budget {r : ℕ} {θ : ℝ} (hr : 2 ≤ r) (hθ : 1 - 2 / (r : ℝ) < θ) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ k ≥ J, powerGridCost r * (k : ℝ) ^ (r - 2) ≤ ((k : ℝ) ^ r) ^ θ := by
  have hr_pos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hgap : ((r - 2 : ℕ) : ℝ) < (r : ℝ) * θ := by
    rw [Nat.cast_sub hr, Nat.cast_ofNat]
    have hmul := mul_lt_mul_of_pos_left hθ hr_pos
    field_simp [hr_pos.ne'] at hmul
    linarith
  obtain ⟨W, hW⟩ := ArchiveFreeBadMeasure.eventual_power_absorption hgap (powerGridCost r)
  refine ⟨max 1 ⌈W⌉₊, le_max_left _ _, fun k hk => ?_⟩
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast ((le_max_left _ _).trans hk)
  have hkW : W ≤ (k : ℝ) :=
    (Nat.le_ceil W).trans (by exact_mod_cast ((le_max_right _ _).trans hk))
  have hpay := hW (k : ℝ) hkW hk1
  rw [Real.rpow_natCast] at hpay
  rwa [← Real.rpow_natCast_mul (Nat.cast_nonneg k)]

private lemma locate_power {r L H : ℕ} {x : ℝ}
    (hr : 1 ≤ r) (lo : (L : ℝ) ^ r ≤ x) (hi : x < (H : ℝ) ^ r) :
    ∃ k : ℕ, L ≤ k ∧ k + 1 ≤ H ∧ x ∈ Set.Icc ((k : ℝ) ^ r) (((k : ℝ) + 1) ^ r) := by
  have hr_ne : r ≠ 0 := by omega
  have x0 : 0 ≤ x := (pow_nonneg (Nat.cast_nonneg L) r).trans lo
  let u := x ^ ((r : ℝ)⁻¹)
  have u0 : 0 ≤ u := Real.rpow_nonneg x0 _
  have ux : u ^ r = x := Real.rpow_inv_natCast_pow x0 hr_ne
  have lu : (L : ℝ) ≤ u :=
    (pow_le_pow_iff_left₀ (Nat.cast_nonneg L) u0 hr_ne).mp (ux.symm ▸ lo)
  have uh : u < (H : ℝ) := by
    by_contra! h
    have p := pow_le_pow_left₀ (Nat.cast_nonneg H) h r
    linarith only [p, ux, hi]
  refine ⟨⌊u⌋₊, Nat.le_floor lu, ?_, ?_, ?_⟩
  · have p : (⌊u⌋₊ : ℝ) < (H : ℝ) := (Nat.floor_le u0).trans_lt uh
    exact_mod_cast p
  · rw [← ux]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le u0) r
  · rw [← ux]
    exact pow_le_pow_left₀ u0 (Nat.lt_floor_add_one _).le r

/-- Covering the exceptional real set `{x ∈ [L^r, H^r] | (2^r * c + 1) * x^θ < rampG x}` by
intervals of radius `powerGridRadius r H` centered at failing `r`-th power samples. -/
theorem power_finite_cover_measure {r : ℕ} {θ c : ℝ}
    (hr : 2 ≤ r) (hθ : 1 - 2 / (r : ℝ) < θ) (hθ1 : θ ≤ 1) (hc : 0 ≤ c) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ L ≥ J, ∀ H ≥ L,
      MeasureTheory.volume.real
        {x ∈ Set.Icc ((L : ℝ) ^ r) ((H : ℝ) ^ r) |
          ((2 : ℝ) ^ r * c + 1) * x ^ θ < IndependentLandau.rampG x} ≤
        2 * powerGridRadius r H * ((powerBadIndices r θ c L H).card : ℝ) := by
  obtain ⟨J, hj1, pay⟩ := power_cell_budget hr hθ
  have hθ0 : 0 ≤ θ := by
    have h2r : (2 : ℝ) / r ≤ 1 := by
      rw [div_le_one (by exact_mod_cast (by omega : 0 < r))]
      exact_mod_cast hr
    linarith
  have h1_2r : 1 ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  refine ⟨J, hj1, fun L hJL H hLH => ?_⟩
  let R := powerGridRadius r H
  let E := powerBadIndices r θ c L H
  let box (k : ℕ) := Set.Icc ((k : ℝ) ^ r - R) ((k : ℝ) ^ r + R)
  have hR0 : 0 ≤ R := by dsimp [R, powerGridRadius]; positivity
  have cover :
      {x ∈ Set.Icc ((L : ℝ) ^ r) ((H : ℝ) ^ r) |
        ((2 : ℝ) ^ r * c + 1) * x ^ θ < IndependentLandau.rampG x} ⊆
      ⋃ k ∈ E, box k := by
    intro x hx
    have bad : ((2 : ℝ) ^ r * c + 1) * x ^ θ < IndependentLandau.rampG x := hx.2
    rcases lt_or_eq_of_le hx.1.2 with hi | endpoint
    · obtain ⟨k, hLk, hkH, cell⟩ := locate_power (by omega) hx.1.1 hi
      have hkJ : J ≤ k := hJL.trans hLk
      have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hj1.trans hkJ
      have dist := power_step_le_radius (r := r) (show k ≤ H by omega)
      by_cases left : c * ((k : ℝ) ^ r) ^ θ < IndependentLandau.rampG ((k : ℝ) ^ r)
      · have ke : k ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hLk, by omega⟩, left⟩
        refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨ke, ?_⟩⟩
        exact ⟨by linarith only [cell.1, hR0], by linarith only [cell.2, dist]⟩
      · have right : c * (((k : ℝ) + 1) ^ r) ^ θ < IndependentLandau.rampG (((k : ℝ) + 1) ^ r) := by
          by_contra! nr
          have pc := power_cell_majorant hr hkr hc hθ0 hθ1 cell (le_of_not_gt left) nr
          have exp := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg k) r) cell.1 hθ0
          have hpay_x := (pay k hkJ).trans exp
          linarith only [pc, hpay_x, bad]
        have ke : k + 1 ∈ E := Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨by omega, hkH⟩, by simpa only [Nat.cast_add_one] using right⟩
        refine Set.mem_iUnion.mpr ⟨k + 1, Set.mem_iUnion.mpr ⟨ke, ?_⟩⟩
        change ((k + 1 : ℕ) : ℝ) ^ r - R ≤ x ∧ x ≤ ((k + 1 : ℕ) : ℝ) ^ r + R
        rw [Nat.cast_add_one]
        exact ⟨by linarith only [cell.1, dist], by linarith only [cell.2, hR0]⟩
    · have hxp : 0 ≤ (((H : ℝ) ^ r) ^ θ) := Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg H) r) θ
      rw [endpoint] at bad
      have hc_le : c * ((H : ℝ) ^ r) ^ θ ≤ ((2 : ℝ) ^ r * c + 1) * ((H : ℝ) ^ r) ^ θ := by
        have hmul : 1 * (c * ((H : ℝ) ^ r) ^ θ) ≤ (2 : ℝ) ^ r * (c * ((H : ℝ) ^ r) ^ θ) :=
          mul_le_mul_of_nonneg_right h1_2r (mul_nonneg hc hxp)
        linarith
      have mem : H ∈ E := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hLH, le_rfl⟩, lt_of_le_of_lt hc_le bad⟩
      refine Set.mem_iUnion.mpr ⟨H, Set.mem_iUnion.mpr ⟨mem, ?_⟩⟩
      exact ⟨by linarith only [endpoint, hR0], by linarith only [endpoint, hR0]⟩
  have finite : MeasureTheory.volume (⋃ k ∈ E, box k) ≠ ⊤ :=
    (E.isCompact_biUnion (fun _ _ => isCompact_Icc)).measure_lt_top.ne
  have each (k : ℕ) : MeasureTheory.volume.real (box k) = 2 * R := by
    rw [show box k = Set.Icc ((k : ℝ) ^ r - R) ((k : ℝ) ^ r + R) from rfl,
      Real.volume_real_Icc_of_le (by linarith)]
    ring
  calc MeasureTheory.volume.real
        {x ∈ Set.Icc ((L : ℝ) ^ r) ((H : ℝ) ^ r) |
          ((2 : ℝ) ^ r * c + 1) * x ^ θ < IndependentLandau.rampG x}
      ≤ MeasureTheory.volume.real (⋃ k ∈ E, box k) := measureReal_mono cover finite
    _ ≤ ∑ k ∈ E, MeasureTheory.volume.real (box k) := measureReal_biUnion_finset_le E box
    _ = 2 * R * (E.card : ℝ) := by
        simp only [each, Finset.sum_const, nsmul_eq_mul]
        ring

private lemma power_radius_upper {r L : ℕ} (hl1 : 1 ≤ L) :
    2 * powerGridRadius r (L ^ 3) ≤
      (2 * (r : ℝ) * (2 : ℝ) ^ (r - 1)) * (L : ℝ) ^ (3 * (r - 1)) := by
  have hlr : (1 : ℝ) ≤ L := by exact_mod_cast hl1
  have hthree : (1 : ℝ) ≤ (L : ℝ) ^ 3 := one_le_pow₀ hlr
  unfold powerGridRadius
  rw [Nat.cast_pow]
  calc 2 * ((r : ℝ) * ((L : ℝ) ^ 3 + 1) ^ (r - 1))
      ≤ 2 * ((r : ℝ) * (2 * (L : ℝ) ^ 3) ^ (r - 1)) := by gcongr; linarith
    _ = (2 * (r : ℝ) * (2 : ℝ) ^ (r - 1)) * ((L : ℝ) ^ 3) ^ (r - 1) := by rw [mul_pow]; ring
    _ = (2 * (r : ℝ) * (2 : ℝ) ^ (r - 1)) * (L : ℝ) ^ (3 * (r - 1)) := by rw [← pow_mul]

/-- Any zeta zero strictly right of `θ` (`r ≥ 4`, `1 - 2 / r < θ`) forces strictly more than
`L^(3 - ε)` sample failures among `(k : ℝ)^r` on every sufficiently late `Finset.Icc (L^2) (L^3)`. -/
theorem near_full_count_general_power {r : ℕ} {ρ : ℂ} {θ c ε : ℝ}
    (hr : 4 ≤ r) (hz : riemannZeta ρ = 0)
    (hθ_lo : 1 - 2 / (r : ℝ) < θ) (hright : θ < ρ.re)
    (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ L ≥ N, (L : ℝ) ^ (3 - ε) < (powerFailures r θ c L : ℝ) := by
  have hr2 : 2 ≤ r := by omega
  have hr1 : 1 ≤ r := by omega
  have hr_pos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hθ1 : θ ≤ 1 :=
    hright.le.trans (le_of_not_gt (fun bad => riemannZeta_ne_zero_of_one_le_re bad.le hz))
  have hhalf : 1 / 2 ≤ θ := by
    have h2r : 2 / (r : ℝ) ≤ 2 / 4 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hr)
    linarith
  obtain ⟨J, hj1, cover⟩ := power_finite_cover_measure hr2 hθ_lo hθ1 hc
  obtain ⟨M, large⟩ := ArchiveFreeBadMeasure.near_full_measureReal_every_window_mathlib
    hz hhalf hright (by positivity : 0 ≤ (2 : ℝ) ^ r * c + 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (div_pos hε (by positivity : 0 < 4 * (r : ℝ)))
  let C_r : ℝ := 2 * (r : ℝ) * (2 : ℝ) ^ (r - 1)
  have hC_nonneg : 0 ≤ C_r := by dsimp [C_r]; positivity
  obtain ⟨W, pay⟩ := ArchiveFreeBadMeasure.eventual_power_absorption
    (by linarith : 3 * (r : ℝ) - ε < 3 * (r : ℝ) - ε / 2) C_r
  refine ⟨max J (max ⌈M⌉₊ ⌈W⌉₊), fun L hlate => ?_⟩
  have hJL : J ≤ L := (le_max_left _ _).trans hlate
  have hl1 : 1 ≤ L := hj1.trans hJL
  have hlr : (1 : ℝ) ≤ L := by exact_mod_cast hl1
  have hlp : 0 < (L : ℝ) := zero_lt_one.trans_le hlr
  have hlo : L ≤ L ^ 2 := le_self_pow₀ hl1 (by decide)
  have hhi : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hl1 (by decide)
  have htop := (le_max_right _ _).trans hlate
  have hLM : M ≤ (L : ℝ) :=
    (Nat.le_ceil M).trans (by exact_mod_cast ((le_max_left _ _).trans htop))
  have hLW : W ≤ (L : ℝ) :=
    (Nat.le_ceil W).trans (by exact_mod_cast ((le_max_right _ _).trans htop))
  have hextent : (L : ℝ) ≤ (L : ℝ) ^ (2 * r) := le_self_pow₀ hlr (by omega)
  have hlower := large ((L : ℝ) ^ (2 * r)) (hLM.trans hextent)
  have hcv := cover (L ^ 2) (hJL.trans hlo) (L ^ 3) hhi
  have hfirst : ((L ^ 2 : ℕ) : ℝ) ^ r = (L : ℝ) ^ (2 * r) := by
    rw [Nat.cast_pow, ← pow_mul]
  have hlast : ((L ^ 3 : ℕ) : ℝ) ^ r = ((L : ℝ) ^ (2 * r)) ^ (1 + (1 / 2 : ℝ)) := by
    rw [Nat.cast_pow, ← pow_mul, ← Real.rpow_natCast_mul (Nat.cast_nonneg L)]
    push_cast
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hexponent :
      ((L : ℝ) ^ (2 * r)) ^ (1 + (1 / 2 : ℝ) - ε / (4 * (r : ℝ))) =
        (L : ℝ) ^ (3 * (r : ℝ) - ε / 2) := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg L)]
    congr 1
    push_cast
    field_simp [hr_pos.ne']
    ring
  rw [hfirst, hlast] at hcv
  rw [hexponent] at hlower
  by_contra! small
  rw [powerFailures_eq_card] at small
  have harea := mul_le_mul (power_radius_upper (r := r) hl1) small
    (Nat.cast_nonneg _) (mul_nonneg hC_nonneg (pow_nonneg hlp.le _))
  have hcombine :
      C_r * (L : ℝ) ^ (3 * (r - 1)) * (L : ℝ) ^ (3 - ε) = C_r * (L : ℝ) ^ (3 * (r : ℝ) - ε) := by
    rw [mul_assoc, ← Real.rpow_natCast (L : ℝ) (3 * (r - 1)), ← Real.rpow_add hlp]
    congr 2
    rw [Nat.cast_mul, Nat.cast_sub hr1]
    push_cast
    ring
  rw [hcombine] at harea
  exact (not_le_of_gt hlower) (hcv.trans (harea.trans (pay (L : ℝ) hLW hlr)))

/-- **Unified `r`-th Power Sparse-Failure Theorem (`general_power_zeroFree_of_sparse_failures`):**
For any integer `r ≥ 4`, `1 - 2 / (r : ℝ) < θ < 1`, `0 ≤ c`, and `0 < ε`, at most `L^(3 - ε)`
failures of `rampG ((k : ℝ)^r) > c * ((k : ℝ)^r)^θ` on `Finset.Icc (L^2) (L^3)` along cofinally
many `L` excludes all zeros of `riemannZeta` in `Re s > θ`.
Specializes to `r = 4` (`θ > 1/2`) and `r = 15` (`θ > 13/15`). -/
theorem general_power_zeroFree_of_sparse_failures {r : ℕ} {θ c ε : ℝ}
    (hr : 4 ≤ r) (hθ_lo : 1 - 2 / (r : ℝ) < θ) (_hθ_hi : θ < 1)
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hsparse : ∀ L₀ : ℕ, ∃ L ≥ L₀, (powerFailures r θ c L : ℝ) ≤ (L : ℝ) ^ (3 - ε)) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  intro s hs hz
  obtain ⟨N, hall⟩ := near_full_count_general_power hr hz hθ_lo hs hc hε
  obtain ⟨L, hL, hsmall⟩ := hsparse N
  exact (not_le_of_gt (hall L hL)) hsmall

/-- **Fourth-Power Sparse-Failure Converse (`zeroFree_of_fourthPower_sparse_failures`):**
For any `1 / 2 < θ < 1`, `0 ≤ c`, and `0 < ε`, if `(fourthPowerFailures θ c L : ℝ) ≤ L^(3 - ε)`
holds on cofinally many `L`, then `riemannZeta s ≠ 0` for all `s` with `θ < s.re`. -/
theorem zeroFree_of_fourthPower_sparse_failures {θ c ε : ℝ}
    (hθ_lo : 1 / 2 < θ) (hθ_hi : θ < 1) (hc : 0 ≤ c) (hε : 0 < ε)
    (hsparse : ∀ L₀ : ℕ, ∃ L ≥ L₀, (fourthPowerFailures θ c L : ℝ) ≤ (L : ℝ) ^ (3 - ε)) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  apply general_power_zeroFree_of_sparse_failures (r := 4) (by decide)
    (by norm_num; linarith) hθ_hi hc hε
  simpa only [fourthPowerFailures_eq_powerFailures] using hsparse

/-- Fifteenth-power (`r = 15`, `θ > 13/15`) corollary recovered directly from
`general_power_zeroFree_of_sparse_failures`. -/
theorem zeroFree_of_fifteenthPower_sparse_failures {θ c ε : ℝ}
    (hθ_lo : 13 / 15 < θ) (hθ_hi : θ < 1) (hc : 0 ≤ c) (hε : 0 < ε)
    (hsparse : ∀ L₀ : ℕ, ∃ L ≥ L₀, (powerFailures 15 θ c L : ℝ) ≤ (L : ℝ) ^ (3 - ε)) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 :=
  general_power_zeroFree_of_sparse_failures (r := 15) (by decide)
    (by norm_num; linarith) hθ_hi hc hε hsparse

/-! ### 3. Forward Vanishing of `fourthPowerFailures` & Full `RiemannHypothesis` Equivalence -/

/-- Forward direction: if `riemannZeta` is zero-free on `Re s > θ₀` (`1/2 ≤ θ₀ < θ < 1`), then
for every `c > 0`, `fourthPowerFailures θ c L = 0` for all sufficiently large `L`. -/
theorem fourthPowerFailures_eventually_eq_zero_of_zeroFree {θ₀ θ c : ℝ}
    (hθ₀ : 1 / 2 ≤ θ₀) (hθ₀θ : θ₀ < θ) (hθ1 : θ < 1) (hc : 0 < c)
    (hz : ∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0) :
    ∀ᶠ L : ℕ in atTop, fourthPowerFailures θ c L = 0 := by
  let θ₁ : ℝ := (θ₀ + θ) / 2
  have hθ₀₁ : θ₀ < θ₁ := by dsimp [θ₁]; linarith
  have hθ₁θ : θ₁ < θ := by dsimp [θ₁]; linarith
  have hθ₁1 : θ₁ < 1 := hθ₁θ.trans hθ1
  obtain ⟨C, _, hC⟩ := DirectRampEquivalence.abs_rampG_le_of_zeroFree hθ₀ hθ₀₁ hθ₁1 hz
  obtain ⟨W, hW⟩ := ArchiveFreeBadMeasure.eventual_power_absorption hθ₁θ (C / c)
  filter_upwards [eventually_ge_atTop (max 1 ⌈W⌉₊)] with L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLW : W ≤ (L : ℝ) :=
    (Nat.le_ceil W).trans (by exact_mod_cast ((le_max_right _ _).trans hL))
  unfold fourthPowerFailures
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk
  rw [not_lt]
  have hkL : L ≤ k := (le_self_pow₀ hL1 (by decide : 2 ≠ 0)).trans (Finset.mem_Icc.mp hk).1
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (hL1.trans hkL)
  have hk4_ge_k : (k : ℝ) ≤ (k : ℝ) ^ 4 := le_self_pow₀ hk1 (by decide)
  have hk4_1 : 1 ≤ (k : ℝ) ^ 4 := hk1.trans hk4_ge_k
  have hk4_W : W ≤ (k : ℝ) ^ 4 := hLW.trans ((by exact_mod_cast hkL : (L : ℝ) ≤ k).trans hk4_ge_k)
  have hbd := (le_abs_self _).trans (hC ((k : ℝ) ^ 4) hk4_1)
  have habs := mul_le_mul_of_nonneg_left (hW ((k : ℝ) ^ 4) hk4_W hk4_1) hc.le
  have heq : c * (C / c * ((k : ℝ) ^ 4) ^ θ₁) = C * ((k : ℝ) ^ 4) ^ θ₁ := by
    field_simp [hc.ne']
  rw [heq] at habs
  exact hbd.trans habs

/-- Under `RiemannHypothesis`, for every `θ ∈ (1/2, 1)` and `c > 0`, `fourthPowerFailures θ c L = 0`
for all sufficiently large `L : ℕ`. -/
theorem fourthPowerFailures_eventually_eq_zero_of_rh
    (hrh : RiemannHypothesis) {θ c : ℝ} (hθ : θ ∈ Set.Ioo (1 / 2 : ℝ) 1) (hc : 0 < c) :
    ∀ᶠ L : ℕ in atTop, fourthPowerFailures θ c L = 0 := by
  have hzf : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → riemannZeta s ≠ 0 :=
    (DirectRampEquivalence.ordinaryWindow_three_way_iff ⟨le_rfl, by norm_num⟩).1.mp
      (DirectRampEquivalence.rh_iff_ordinaryWindowUnit_above_half.mp hrh)
  exact fourthPowerFailures_eventually_eq_zero_of_zeroFree le_rfl hθ.1 hθ.2 hc hzf

/-- **Full `RiemannHypothesis` Fourth-Power Sparse-Failure Equivalence
(`rh_iff_fourthPower_sparse_failures`):**
`RiemannHypothesis` holds if and only if for every `θ ∈ (1/2, 1)` there exist `ε > 0` and `c ≥ 0`
with `(fourthPowerFailures θ c L : ℝ) ≤ L^(3 - ε)` on cofinally many `L`. -/
theorem rh_iff_fourthPower_sparse_failures :
    RiemannHypothesis ↔
      ∀ θ ∈ Set.Ioo (1 / 2 : ℝ) 1, ∃ ε > 0, ∃ c ≥ 0,
        ∀ L₀ : ℕ, ∃ L ≥ L₀, (fourthPowerFailures θ c L : ℝ) ≤ (L : ℝ) ^ (3 - ε : ℝ) := by
  constructor
  · intro hrh θ hθ
    refine ⟨(1 : ℝ), zero_lt_one, (1 : ℝ), zero_le_one, fun L₀ => ?_⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (fourthPowerFailures_eventually_eq_zero_of_rh hrh hθ zero_lt_one)
    refine ⟨max L₀ N, le_max_left _ _, ?_⟩
    rw [hN (max L₀ N) (le_max_right _ _), Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · intro hsparse
    rw [DirectRampEquivalence.rh_iff_ordinaryWindowUnit_above_half,
      (DirectRampEquivalence.ordinaryWindow_three_way_iff ⟨le_rfl, by norm_num⟩).1]
    intro s hs
    rcases le_or_gt 1 s.re with hs1 | hs1
    · exact riemannZeta_ne_zero_of_one_le_re hs1
    · let θ : ℝ := (1 / 2 + s.re) / 2
      have hθ_mem : θ ∈ Set.Ioo (1 / 2 : ℝ) 1 := ⟨by dsimp [θ]; linarith, by dsimp [θ]; linarith⟩
      obtain ⟨ε, hε, c, hc, hL⟩ := hsparse θ hθ_mem
      exact zeroFree_of_fourthPower_sparse_failures hθ_mem.1 hθ_mem.2 hc hε hL s
        (by dsimp [θ]; linarith)

/-- **Fixed-`(c, ε)` `RiemannHypothesis` Equivalence (`rh_iff_fourthPower_sparse_failures_fixed`):**
For any fixed `c > 0` and any fixed `ε ∈ (0, 3)`, `RiemannHypothesis` holds if and only if for
every `θ ∈ (1/2, 1)`, `(fourthPowerFailures θ c L : ℝ) ≤ L^(3 - ε)` holds on cofinally many `L`. -/
theorem rh_iff_fourthPower_sparse_failures_fixed {c ε : ℝ}
    (hc : 0 < c) (hε : ε ∈ Set.Ioo (0 : ℝ) 3) :
    RiemannHypothesis ↔
      ∀ θ ∈ Set.Ioo (1 / 2 : ℝ) 1,
        ∀ L₀ : ℕ, ∃ L ≥ L₀, (fourthPowerFailures θ c L : ℝ) ≤ (L : ℝ) ^ (3 - ε) := by
  constructor
  · intro hrh θ hθ L₀
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (fourthPowerFailures_eventually_eq_zero_of_rh hrh hθ hc)
    refine ⟨max L₀ N, le_max_left _ _, ?_⟩
    rw [hN (max L₀ N) (le_max_right _ _), Nat.cast_zero]
    have _ : ε < 3 := hε.2
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · intro hfixed
    exact rh_iff_fourthPower_sparse_failures.mpr fun θ hθ =>
      ⟨ε, hε.1, c, hc.le, hfixed θ hθ⟩

/-- **Eventual-Zero `RiemannHypothesis` Equivalence (`rh_iff_fourthPower_eventually_zero`):**
For any fixed `c > 0`, `RiemannHypothesis` holds if and only if for every `θ ∈ (1/2, 1)`,
`fourthPowerFailures θ c L = 0` for all sufficiently large `L`. -/
theorem rh_iff_fourthPower_eventually_zero {c : ℝ} (hc : 0 < c) :
    RiemannHypothesis ↔
      ∀ θ ∈ Set.Ioo (1 / 2 : ℝ) 1, ∀ᶠ L : ℕ in atTop, fourthPowerFailures θ c L = 0 := by
  constructor
  · exact fun hrh θ hθ => fourthPowerFailures_eventually_eq_zero_of_rh hrh hθ hc
  · intro hev
    refine (rh_iff_fourthPower_sparse_failures_fixed hc ⟨zero_lt_one, by norm_num⟩).mpr ?_
    intro θ hθ L₀
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hev θ hθ)
    refine ⟨max L₀ N, le_max_left _ _, ?_⟩
    rw [hN (max L₀ N) (le_max_right _ _), Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-! ### 4. Eventual Global Ramp Bound and Archive-Free `2.98` (`149/50`) Shell Transfer -/

/-- Sparse fourth-power failures at `θ` yield a global eventual two-sided bound
`|rampG x| ≤ a * x^σ` for any `σ ∈ (θ, 1)` and any `a > 0`. -/
theorem eventual_abs_rampG_of_fourthPower_sparse_failures {θ σ c ε a : ℝ}
    (hθ_lo : 1 / 2 < θ) (hθσ : θ < σ) (hσ1 : σ < 1)
    (hc : 0 ≤ c) (hε : 0 < ε) (ha : 0 < a)
    (hsparse : ∀ L₀ : ℕ, ∃ L ≥ L₀, (fourthPowerFailures θ c L : ℝ) ≤ (L : ℝ) ^ (3 - ε)) :
    ∀ᶠ x : ℝ in atTop, |IndependentLandau.rampG x| ≤ a * x ^ σ := by
  have hzf := zeroFree_of_fourthPower_sparse_failures hθ_lo (hθσ.trans hσ1) hc hε hsparse
  obtain ⟨q, hθq, hqσ⟩ := exists_between hθσ
  obtain ⟨C, _, hall⟩ := DirectRampEquivalence.abs_rampG_le_of_zeroFree
    hθ_lo.le hθq (hqσ.trans hσ1) hzf
  obtain ⟨W, hpay⟩ := ArchiveFreeBadMeasure.eventual_power_absorption hqσ (C / a)
  filter_upwards [eventually_ge_atTop (max 1 W)] with x hx
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hxW : W ≤ x := (le_max_right _ _).trans hx
  have hbd := hall x hx1
  have habs := mul_le_mul_of_nonneg_left (hpay x hxW hx1) ha.le
  have heq : a * (C / a * x ^ q) = C * x ^ q := by field_simp [ha.ne']
  rw [heq] at habs
  exact hbd.trans habs

/-- **General Archive-Free `2.98` (`149 / 50`) Transfer from Fourth-Power Sparse Failures
(`archiveFree_298_of_fourthPower_sparse_failures_general`):**
For any `1 / 2 < θ < 349 / 400`, `0 ≤ c`, and `0 < ε`, cofinal fourth-power failure sparsity
`fourthPowerFailures θ c L ≤ L^(3 - ε)` implies both eventual two-sided `a * x^σ` ramp bounds
for all `σ ∈ (θ, 1)` and the `149 / 50 = 2.98` weighted uniform shell moment bound. -/
theorem archiveFree_298_of_fourthPower_sparse_failures_general {θ c ε : ℝ}
    (hθ_lo : 1 / 2 < θ) (hθ_hi : θ < 349 / 400) (hc : 0 ≤ c) (hε : 0 < ε)
    (hsparse : ∀ L₀ : ℕ, ∃ L ≥ L₀, (fourthPowerFailures θ c L : ℝ) ≤ (L : ℝ) ^ (3 - ε)) :
    (∀ σ ∈ Set.Ioo θ 1, ∀ a > 0, ∀ᶠ x : ℝ in atTop, |IndependentLandau.rampG x| ≤ a * x ^ σ) ∧
    (∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m : ℝ) ^ (149 / 50 : ℝ)) := by
  refine ⟨fun σ hσ a ha =>
    eventual_abs_rampG_of_fourthPower_sparse_failures hθ_lo hσ.1 hσ.2 hc hε ha hsparse, ?_⟩
  have hzf := zeroFree_of_fourthPower_sparse_failures hθ_lo (by linarith) hc hε hsparse
  let θ' : ℝ := (θ + 349 / 400) / 2
  have hW : DirectRampEquivalence.OrdinaryWindowUnit θ' :=
    (DirectRampEquivalence.ordinaryWindow_three_way_iff ⟨hθ_lo.le, by linarith⟩).1.mpr hzf
      θ' ⟨by dsimp [θ']; linarith, by dsimp [θ']; linarith⟩
  exact DirectRampEquivalence.archiveFree_moment_of_ordinaryWindow
    (by dsimp [θ']; linarith) (by dsimp [θ']; linarith) hW

/-- **Archive-Free `0.87` Ramp + `2.98` Shell Transfer (`archiveFree_087_and_298_of_fourthPower_sparse`):**
For any `1 / 2 < θ < 87 / 100`, `0 ≤ c`, and `0 < ε`, cofinal fourth-power failure sparsity
`fourthPowerFailures θ c L ≤ L^(3 - ε)` yields BOTH
`∀ᶠ x in atTop, |rampG x| ≤ (1 / 2) * x^(87 / 100)` AND
`∀ᶠ m in atTop, weighted uniformShellScore m ≤ m^(149 / 50)`. -/
theorem archiveFree_087_and_298_of_fourthPower_sparse {θ c ε : ℝ}
    (hθ_lo : 1 / 2 < θ) (hθ_hi : θ < 87 / 100) (hc : 0 ≤ c) (hε : 0 < ε)
    (hsparse : ∀ L₀ : ℕ, ∃ L ≥ L₀, (fourthPowerFailures θ c L : ℝ) ≤ (L : ℝ) ^ (3 - ε)) :
    (∀ᶠ x : ℝ in atTop, |IndependentLandau.rampG x| ≤ (1 / 2) * x ^ (87 / 100 : ℝ)) ∧
    (∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m : ℝ) ^ (149 / 50 : ℝ)) := by
  have hgen := archiveFree_298_of_fourthPower_sparse_failures_general
    hθ_lo (by linarith) hc hε hsparse
  exact ⟨hgen.1 (87 / 100) ⟨hθ_hi, by norm_num⟩ (1 / 2) (by norm_num), hgen.2⟩

/-- **Concrete Benchmark Transfer (`archiveFree_298_of_fourthPower_sparse_failures`):**
At `θ = 8699 / 10000`, `c = 1 / 2`, `ε = 1 / 100` (at most `L^(299 / 100)` fourth-power sample
failures on `Finset.Icc (L^2) (L^3)` along cofinally many `L`), we obtain BOTH:
1. `∀ᶠ x : ℝ in atTop, |IndependentLandau.rampG x| ≤ (1 / 2) * x ^ (87 / 100 : ℝ)`, and
2. `∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m : ℝ) ^ (149 / 50 : ℝ)`. -/
theorem archiveFree_298_of_fourthPower_sparse_failures
    (hsparse : ∀ L₀ : ℕ, ∃ L ≥ L₀,
      (fourthPowerFailures (8699 / 10000) (1 / 2) L : ℝ) ≤ (L : ℝ) ^ (299 / 100 : ℝ)) :
    (∀ᶠ x : ℝ in atTop, |IndependentLandau.rampG x| ≤ (1 / 2) * x ^ (87 / 100 : ℝ)) ∧
    (∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m : ℝ) ^ (149 / 50 : ℝ)) := by
  apply archiveFree_087_and_298_of_fourthPower_sparse
    (θ := 8699 / 10000) (c := 1 / 2) (ε := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa only [show (3 - 1 / 100 : ℝ) = 299 / 100 by norm_num] using hsparse

end FourthPowerSparseRH

export FourthPowerSparseRH (
  powerBadIndices
  powerFailures
  fourthPowerFailures
  fourthPower_step_le
  fourthPower_secant_excess_le
  power_finite_cover_measure
  near_full_count_general_power
  general_power_zeroFree_of_sparse_failures
  zeroFree_of_fourthPower_sparse_failures
  zeroFree_of_fifteenthPower_sparse_failures
  fourthPowerFailures_eventually_eq_zero_of_zeroFree
  fourthPowerFailures_eventually_eq_zero_of_rh
  rh_iff_fourthPower_sparse_failures
  rh_iff_fourthPower_sparse_failures_fixed
  rh_iff_fourthPower_eventually_zero
  eventual_abs_rampG_of_fourthPower_sparse_failures
  archiveFree_298_of_fourthPower_sparse_failures_general
  archiveFree_087_and_298_of_fourthPower_sparse
  archiveFree_298_of_fourthPower_sparse_failures
)

#print axioms general_power_zeroFree_of_sparse_failures
#print axioms zeroFree_of_fourthPower_sparse_failures
#print axioms rh_iff_fourthPower_sparse_failures
#print axioms archiveFree_298_of_fourthPower_sparse_failures
