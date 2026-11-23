import SparseTentCell
import PrimeCentreBudget
import PrimeExcessMean
import ZeroFreeShellMoment
import RampWindowEquivalence

/-!
# Fourth-Power Ordinary-Prime Tent Quadrature and Full RH Equivalence Across `(1/2, 1)`

Replaces fifteenth-power sampling `A_k = k^{15}` (`13/15 < θ`, saving `43/15000 ≈ 0.00287` at
`θ = 0.8724`) with **fourth-power** sampling `A_k = k^4` (`Y = K^8`, `A_{K^2} = K^8`,
`A_{K^3} = K^{12} = Y^{3/2}`):

1. On `[k^4, (k + 1)^4]`, `(k + 1)^4 - k^4 ≤ 15 * k^3` for `k ≥ 1`, so `SparseTentCell.cell` yields
   interpolation error `3 * log((k + 1)^4) * ((k + 1)^4 - k^4)^2 / k^4 ≤ 5400 * k^2 * log k`, which
   is `o((k^4)^σ)` for **every `1/2 < σ`** (lowering `13/15` all the way down to `1/2`).
2. `fourth_quadrature` & `fourth_quadrature_at_08724`: Unconditional whole-window quadrature bound
   on `[logStart4 K, (3/2) * logStart4 K]`; at `θ = 2181/2500 = 0.8724` and
   `σ = (1/2 + 2181/2500)/2`, the deterministic error is
   `(logStart4 K / 2) * exp(-(931/5000) * logStart4 K) → 0` (65x larger exponent `931/5000 = 0.1862`
   than `43/15000`).
3. `excessMean_of_fourthSamples` & `shell298_of_fourthSamples`: Valid for **every `1/2 < θ`**
   (and `1/2 < θ < 349/400` for the `2.98` full-shell moment).
4. `subpowerFourthSamples_of_zeroFree` & `rh_iff_subpowerFourthSamples`: Converse bound (actually
   holding `eventually` for all sufficiently large `K`) and complete `RiemannHypothesis` equivalence
   `RiemannHypothesis ↔ ∀ θ ∈ Set.Ioo (1 / 2 : ℝ) 1, SubpowerFourthSamples θ`.
-/

open Finset Filter MeasureTheory Set Topology
open RiemannReduction.ShortTail.LossFrequency

noncomputable section

namespace PrimeCentreMean.Sparse

/-! ### 1. Fourth-Power Grid and Cell Interpolation Error -/

/-- Fourth-power sample point `A_k = k^4`. -/
def sample4 (k : ℕ) : ℝ := (k : ℝ) ^ 4

/-- Explicit cell-interpolation constant `3 * 8 * 15^2 = 5400` on `[k^4, (k + 1)^4]`. -/
def fourthErrorConstant : ℝ := 5400

/-- Logarithmic start `log(A_{K^2}) = log(K^8) = 8 * log K` of the aligned `[Y, Y^{3/2}]` window. -/
def logStart4 (K : ℕ) : ℝ := Real.log (sample4 (K ^ 2))

/-- Gap-weighted ordinary-prime excess sum across `[K^8, K^{12}]` at consecutive fourth powers. -/
def fourthSampleBudget (θ : ℝ) (K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (K ^ 3 - K ^ 2),
    PrimeCentreMean.gapCost θ (sample4 (K ^ 2 + i)) (sample4 (K ^ 2 + i + 1))

/-- Subpower growth hypothesis for the fourth-power ordinary-prime tent budget at exponent `θ`. -/
def SubpowerFourthSamples (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ J : ℕ, ∃ K ≥ J,
    fourthSampleBudget θ K ≤ Real.exp (ε * logStart4 K)

theorem sample4_pos {k : ℕ} (hk : 0 < k) : 0 < sample4 k := by
  unfold sample4
  positivity

theorem sample4_mono : Monotone sample4 := by
  intro i j hij
  unfold sample4
  gcongr

private theorem width4 {k : ℝ} (hk : 1 ≤ k) :
    (k + 1) ^ 4 - k ^ 4 ≤ 15 * k ^ 3 := by
  have hfac : 15 * k ^ 3 - ((k + 1) ^ 4 - k ^ 4) =
      (k - 1) * (11 * k ^ 2 + 5 * k + 1) := by ring
  have hnonneg : 0 ≤ (k - 1) * (11 * k ^ 2 + 5 * k + 1) :=
    mul_nonneg (by linarith) (by positivity)
  linarith

/-- Uniform interpolation bound for the ordinary-prime tent on `[k^4, (k + 1)^4]` (`k ≥ 2`), with
explicit error `5400 * k^2 * log k`. -/
theorem fourth_cell {k : ℕ} (hk : 2 ≤ k) {x : ℝ}
    (hx : x ∈ Icc (sample4 k) (sample4 (k + 1))) :
    excess x ≤ max (excess (sample4 k)) (excess (sample4 (k + 1))) +
      fourthErrorConstant * (k : ℝ) ^ 2 * Real.log k := by
  have kn : 0 < k := by omega
  have two : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have k0 : 0 < (k : ℝ) := Nat.cast_pos.mpr kn
  have k1 : (1 : ℝ) ≤ (k : ℝ) := by linarith
  have natural := cell (A := k ^ 4) (B := (k + 1) ^ 4) (pow_pos kn 4)
    (Nat.pow_lt_pow_left (Nat.lt_succ_self k) (by decide))
    (x := x) (by simpa only [Nat.cast_pow, sample4] using hx)
  simp only [Nat.cast_pow, Nat.cast_add_one] at natural
  have gap0 : 0 ≤ ((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4 :=
    sub_nonneg.mpr (pow_le_pow_left₀ k0.le (by linarith) 4)
  have logs : Real.log (((k : ℝ) + 1) ^ 4) ≤ 8 * Real.log k := by
    have ksq : (k : ℝ) + 1 ≤ (k : ℝ) ^ 2 := by nlinarith
    have h := Real.log_le_log (by positivity) ksq
    rw [Real.log_pow] at h ⊢
    norm_num at h ⊢
    linarith only [h]
  have dsq := pow_le_pow_left₀ gap0 (width4 k1) 2
  have bound := mul_le_mul logs dsq (sq_nonneg _) (by positivity : 0 ≤ 8 * Real.log (k : ℝ))
  have eq : 3 * (8 * Real.log (k : ℝ) * (15 * (k : ℝ) ^ 3) ^ 2) =
      (fourthErrorConstant * (k : ℝ) ^ 2 * Real.log k) * (k : ℝ) ^ 4 := by
    dsimp [fourthErrorConstant]
    ring
  have cert : 3 * Real.log (((k : ℝ) + 1) ^ 4) * (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) ^ 2 /
      (k : ℝ) ^ 4 ≤ fourthErrorConstant * (k : ℝ) ^ 2 * Real.log k := by
    apply (div_le_iff₀ (pow_pos k0 4)).mpr
    rw [← eq]
    linarith only [bound]
  simpa only [sample4, Nat.cast_add_one] using natural.trans (add_le_add le_rfl cert)

/-- For every `1 / 2 < σ` and `η > 0`, the fourth-power cell interpolation error is eventually at
most `η * (k^4)^σ`. -/
theorem eventually_fourth_cost {σ η : ℝ} (s : 1 / 2 < σ) (allow : 0 < η) :
    ∀ᶠ k : ℕ in atTop, fourthErrorConstant * (k : ℝ) ^ 2 * Real.log k ≤ η * (sample4 k) ^ σ := by
  have dc : 0 < fourthErrorConstant := by norm_num [fourthErrorConstant]
  have positive : 0 < 4 * σ - 2 := by linarith
  have bound := (isLittleO_log_rpow_atTop positive).bound (div_pos allow dc)
  have cast := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually bound
  filter_upwards [cast, eventually_ge_atTop 1] with k h big
  have k1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast big
  have kp : 0 < (k : ℝ) := by linarith
  change ‖Real.log (k : ℝ)‖ ≤ η / fourthErrorConstant * ‖(k : ℝ) ^ (4 * σ - 2)‖ at h
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg k1),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg kp.le _)] at h
  have scaled := mul_le_mul_of_nonneg_left h (mul_nonneg dc.le (pow_nonneg kp.le 2))
  have eq : (k : ℝ) ^ 2 * (k : ℝ) ^ (4 * σ - 2) = (sample4 k) ^ σ := by
    rw [← Real.rpow_natCast (k : ℝ) 2, ← Real.rpow_add kp]
    unfold sample4
    rw [← Real.rpow_natCast_mul kp.le]
    congr 1
    norm_num
  calc fourthErrorConstant * (k : ℝ) ^ 2 * Real.log k
      ≤ (fourthErrorConstant * (k : ℝ) ^ 2) * (η / fourthErrorConstant * (k : ℝ) ^ (4 * σ - 2)) :=
        scaled
    _ = η * (sample4 k) ^ σ := by
        rw [← eq]
        field_simp [dc.ne']

theorem eventually_fourth_cell {σ : ℝ} (s : 1 / 2 < σ) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ Icc (sample4 k) (sample4 (k + 1)),
      excess x ≤ max (excess (sample4 k)) (excess (sample4 (k + 1))) + x ^ σ := by
  filter_upwards [eventually_fourth_cost s (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop 2]
    with k pay two
  intro x hx
  have h := (fourth_cell two hx).trans (add_le_add le_rfl pay)
  rw [one_mul] at h
  exact h.trans (add_le_add le_rfl
    (Real.rpow_le_rpow (sample4_pos (by omega)).le hx.1 (by linarith)))

/-! ### 2. Unconditional Whole-Window Quadrature Above `1 / 2` -/

theorem continuous_excessDensity (θ : ℝ) : Continuous (excessDensity θ) := by
  have h : Continuous excess := continuous_iff_continuousAt.mpr fun x =>
    ((excess_continuousOn (x - 1) (x + 1)) x (show x ∈ Icc (x - 1) (x + 1) by
      constructor <;> linarith)).continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  unfold excessDensity
  fun_prop

private theorem local_integral4 {a b l σ θ : ℝ} (ha : 0 < a) (order : a ≤ b)
    (hl : l ≤ Real.log a) (θ0 : 0 ≤ θ) (sθ : σ ≤ θ)
    (cover : ∀ x ∈ Icc a b, excess x ≤ max (excess a) (excess b) + x ^ σ) :
    (∫ u in Real.log a..Real.log b, excessDensity θ u) ≤
      PrimeCentreMean.gapCost θ a b + (Real.log b - Real.log a) * Real.exp ((σ - θ) * l) := by
  have hb := ha.trans_le order
  have lord := Real.log_le_log ha order
  let M := max (excess a) (excess b)
  let V := M * Real.exp (-θ * Real.log a) + Real.exp ((σ - θ) * l)
  have M0 : 0 ≤ M := (le_max_left 0 _ : 0 ≤ excess a).trans (le_max_left _ _)
  calc (∫ u in Real.log a..Real.log b, excessDensity θ u)
      ≤ ∫ _ in Real.log a..Real.log b, V := by
          apply intervalIntegral.integral_mono_on lord
            ((continuous_excessDensity θ).intervalIntegrable ..) intervalIntegrable_const
          intro u hu
          have xmem : Real.exp u ∈ Icc a b := by
            constructor
            · simpa only [Real.exp_log ha] using Real.exp_le_exp.mpr hu.1
            · simpa only [Real.exp_log hb] using Real.exp_le_exp.mpr hu.2
          have pay := mul_le_mul_of_nonneg_right (cover _ xmem) (Real.exp_pos (-θ * u)).le
          have m := mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hu.1 (neg_nonpos.mpr θ0))) M0
          have e := Real.exp_le_exp.mpr
            (mul_le_mul_of_nonpos_left (hl.trans hu.1) (sub_nonpos.mpr sθ))
          have eq : (Real.exp u) ^ σ * Real.exp (-θ * u) = Real.exp ((σ - θ) * u) := by
            rw [← Real.exp_mul, ← Real.exp_add]
            congr 1
            ring
          change excess (Real.exp u) * Real.exp (-θ * u) ≤ M * Real.exp (-θ * Real.log a) + _
          rw [add_mul, eq] at pay
          exact pay.trans (add_le_add m e)
    _ = PrimeCentreMean.gapCost θ a b + (Real.log b - Real.log a) * Real.exp ((σ - θ) * l) := by
          rw [intervalIntegral.integral_const]
          dsimp [V, M, PrimeCentreMean.gapCost]
          ring

private theorem widths4 (t : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, (t (i + 1) - t i) = t N - t 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem logStart4_eq (K : ℕ) : logStart4 K = 8 * Real.log K := by
  simp only [logStart4, sample4, Nat.cast_pow, Real.log_pow]
  norm_num
  ring

theorem logStart4_tendsto : Tendsto logStart4 atTop atTop := by
  simp_rw [show logStart4 = (fun K : ℕ => 8 * Real.log K) from funext logStart4_eq]
  exact (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop
    (by norm_num)

/-- **Unconditional Fourth-Power Quadrature (`fourth_quadrature`):**
For any `1 / 2 < σ` and `σ ≤ θ`, on every sufficiently late aligned block `[K^8, K^{12}]`
(`u ∈ [logStart4 K, (3/2) * logStart4 K]`), the continuous ordinary-prime excess integral is bounded
by `fourthSampleBudget θ K` plus `(logStart4 K / 2) * exp((σ - θ) * logStart4 K)`. -/
theorem fourth_quadrature {σ θ : ℝ} (s : 1 / 2 < σ) (sθ : σ ≤ θ) :
    ∀ᶠ K : ℕ in atTop,
      (∫ u in Set.Icc (logStart4 K) ((3 / 2) * logStart4 K),
        PrimeCentreMean.excessDensity θ u) ≤
        fourthSampleBudget θ K + (logStart4 K / 2) * Real.exp ((σ - θ) * logStart4 K) := by
  obtain ⟨J, cells⟩ := eventually_atTop.mp (eventually_fourth_cell s)
  filter_upwards [eventually_ge_atTop (max J 2)] with K late
  have k2 : 2 ≤ K := (le_max_right _ _).trans late
  have k1 : 1 ≤ K := by omega
  have order : K ^ 2 ≤ K ^ 3 := pow_le_pow_right₀ k1 (by decide)
  have kj : J ≤ K ^ 2 := ((le_max_left _ _).trans late).trans (le_self_pow₀ k1 (by decide))
  let N := K ^ 3 - K ^ 2
  let t (i : ℕ) := Real.log (sample4 (K ^ 2 + i))
  have p (i : ℕ) : 0 < sample4 (K ^ 2 + i) :=
    sample4_pos (by have := pow_pos (by omega : 0 < K) 2; omega)
  have mono : Monotone t := by
    intro i j ij
    exact Real.log_le_log (p i) (sample4_mono (by omega))
  have t0 : t 0 = logStart4 K := by simp [t, logStart4]
  have tN : t N = (3 / 2) * logStart4 K := by
    dsimp [t, N]
    rw [Nat.add_sub_of_le order]
    simp only [sample4, logStart4, Nat.cast_pow, Real.log_pow]
    norm_num
    ring
  have w : t N - t 0 = logStart4 K / 2 := by rw [t0, tN]; ring
  calc (∫ u in Set.Icc (logStart4 K) ((3 / 2) * logStart4 K), PrimeCentreMean.excessDensity θ u)
      = ∫ u in t 0..t N, PrimeCentreMean.excessDensity θ u := by
          rw [← tN, ← t0, intervalIntegral.integral_of_le (mono (Nat.zero_le N)),
            integral_Icc_eq_integral_Ioc]
    _ = ∑ i ∈ Finset.range N, ∫ u in t i..t (i + 1), PrimeCentreMean.excessDensity θ u :=
        (intervalIntegral.sum_integral_adjacent_intervals
          (fun _ _ => (continuous_excessDensity θ).intervalIntegrable ..)).symm
    _ ≤ ∑ i ∈ Finset.range N,
          (PrimeCentreMean.gapCost θ (sample4 (K ^ 2 + i)) (sample4 (K ^ 2 + i + 1)) +
            (t (i + 1) - t i) * Real.exp ((σ - θ) * logStart4 K)) := by
        apply Finset.sum_le_sum
        intro i _
        exact local_integral4 (p i) (sample4_mono (by omega)) (t0 ▸ mono (Nat.zero_le i))
          (by linarith) sθ (cells _ (by omega))
    _ = fourthSampleBudget θ K + (logStart4 K / 2) * Real.exp ((σ - θ) * logStart4 K) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, widths4, w]
        rfl

/-- At `θ = 2181 / 2500 = 0.8724` and `σ = (1 / 2 + 2181 / 2500) / 2`, the deterministic fourth-power
interpolation loss is `(logStart4 K / 2) * exp(-(931 / 5000) * logStart4 K)` (65x larger decay
exponent `931 / 5000 = 0.1862` than fifteenth-power sampling's `43 / 15000 ≈ 0.00287`). -/
theorem fourth_quadrature_at_08724 :
    ∀ᶠ K : ℕ in atTop,
      (∫ u in Set.Icc (logStart4 K) ((3 / 2) * logStart4 K),
        PrimeCentreMean.excessDensity (2181 / 2500) u) ≤
        fourthSampleBudget (2181 / 2500) K +
          (logStart4 K / 2) * Real.exp (-(931 / 5000) * logStart4 K) := by
  have h := fourth_quadrature (σ := (1 / 2 + 2181 / 2500) / 2) (θ := 2181 / 2500)
    (by norm_num) (by norm_num)
  rw [show ((1 / 2 + 2181 / 2500) / 2 - 2181 / 2500 : ℝ) = -(931 / 5000) by norm_num] at h
  exact h

theorem fourth_quadrature_error_tends_to_zero :
    Tendsto (fun K : ℕ => (logStart4 K / 2) * Real.exp (-(931 / 5000) * logStart4 K))
      atTop (nhds 0) := by
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (931 / 5000) (by norm_num)).comp
    logStart4_tendsto).div_const 2
  simpa only [Function.comp_def, Real.rpow_one, zero_div, div_mul_eq_mul_div] using h

/-! ### 3. Zero-Free Half-Plane and `2.98` Shell Transfer for All `1 / 2 < θ` -/

/-- For **any** `1 / 2 < θ`, subpower growth of the fourth-power sample budget implies the
continuous ordinary-prime excess mean criterion `SmallExcessMean θ (1 / 2)`. -/
theorem excessMean_of_fourthSamples {θ : ℝ} (half : 1 / 2 < θ) (small : SubpowerFourthSamples θ) :
    PrimeCentreMean.SmallExcessMean θ (1 / 2) := by
  intro ε ep U₀
  let τ := ε / 2
  have tp : 0 < τ := by dsimp [τ]; linarith
  have room : ∀ᶠ U : ℝ in atTop, 0 < U ∧ U / 2 ≤ Real.exp (τ * U) ∧ 2 ≤ Real.exp (τ * U) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (tendsto_exp_mul_div_rpow_atTop 1 τ tp).eventually_ge_atTop 1,
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop tp)).eventually_ge_atTop 2]
      with U hu h r
    have pay : U ≤ Real.exp (τ * U) := by
      have := (le_div_iff₀ hu).mp (show (1 : ℝ) ≤ Real.exp (τ * U) / U by simpa using h)
      linarith
    exact ⟨hu, by linarith, r⟩
  have good := (fourth_quadrature half (le_rfl : θ ≤ θ)).and
    ((logStart4_tendsto.eventually_ge_atTop U₀).and (logStart4_tendsto.eventually room))
  obtain ⟨J, all⟩ := eventually_atTop.mp good
  obtain ⟨K, late, spend⟩ := small τ tp J
  obtain ⟨bound, start, _, pay, twice⟩ := all K late
  simp only [sub_self, zero_mul, Real.exp_zero, mul_one] at bound
  refine ⟨logStart4 K, start, (continuous_excessDensity θ).continuousOn.integrableOn_Icc, ?_⟩
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num]
  have charge := bound.trans (add_le_add spend pay)
  have eq : Real.exp (ε * logStart4 K) = Real.exp (τ * logStart4 K) * Real.exp (τ * logStart4 K) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [τ]
    ring
  rw [eq]
  nlinarith only [charge, mul_nonneg (Real.exp_pos (τ * logStart4 K)).le (sub_nonneg.mpr twice)]

/-- For any `1 / 2 < θ < 1`, `SubpowerFourthSamples θ` excludes all zeros of `riemannZeta` in
`Re s > θ`. -/
theorem zeroFree_of_fourthSamples {θ : ℝ} (half : 1 / 2 < θ) (one : θ < 1)
    (small : SubpowerFourthSamples θ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 :=
  PrimeCentreMean.zeroFree_of_excessMean half.le one (by norm_num)
    (excessMean_of_fourthSamples half small)

/-- For any `1 / 2 < θ < 349 / 400`, `SubpowerFourthSamples θ` implies the `m^{149/50} = m^{2.98}`
full signed-shell moment bound for all sufficiently large `m`. -/
theorem shell298_of_fourthSamples {θ : ℝ} (half : 1 / 2 < θ) (below : θ < 349 / 400)
    (small : SubpowerFourthSamples θ) :
    ∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m : ℝ) ^ (149 / 50 : ℝ) :=
  full_shell_moment_of_zero_free half.le (by linarith)
    (zeroFree_of_fourthSamples half (by linarith) small) (by linarith)

theorem shell298_of_fourthSamples_at_08724 (small : SubpowerFourthSamples (2181 / 2500)) :
    ∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m : ℝ) ^ (149 / 50 : ℝ) :=
  shell298_of_fourthSamples (by norm_num) (by norm_num) small

/-! ### 4. Converse from Zero-Free Half-Planes and Full `RiemannHypothesis` Equivalence -/

private theorem excess_le_six_rampG4 {C q : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hG : ∀ t : ℝ, 1 ≤ t → |IndependentLandau.rampG t| ≤ C * t ^ q)
    {x : ℝ} (hx : 4 ≤ x) :
    excess x ≤ 6 * C * x ^ q := by
  have hx0 : 0 ≤ x := by linarith
  have hxq : 0 ≤ x ^ q := Real.rpow_nonneg hx0 q
  unfold excess
  apply max_le (by positivity)
  have hp : ThetaTransfer.primeSum (x / 4) ≤ ThetaTransfer.primePowerSum (x / 4) :=
    ThetaTransfer.primeSum_le_primePowerSum (x / 4)
  have hd := ThetaTransfer.deficit_eq_centered_ramps (y := x / 4) (by linarith)
  rw [show 4 * (x / 4) = x by ring, show 2 * (x / 4) = x / 2 by ring,
    show 2 * Real.log 2 * (x / 4) = (x / 2) * Real.log 2 by ring] at hd
  have hb1 : IndependentLandau.rampG x ≤ C * x ^ q :=
    (le_abs_self _).trans (hG x (by linarith))
  have hb2 : -IndependentLandau.rampG (x / 2) ≤ C * x ^ q := by
    calc -IndependentLandau.rampG (x / 2)
        ≤ |IndependentLandau.rampG (x / 2)| := neg_le_abs _
      _ ≤ C * (x / 2) ^ q := hG (x / 2) (by linarith)
      _ ≤ C * x ^ q :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) hq) hC
  have hb4 : IndependentLandau.rampG (x / 4) ≤ C * x ^ q := by
    calc IndependentLandau.rampG (x / 4)
        ≤ |IndependentLandau.rampG (x / 4)| := le_abs_self _
      _ ≤ C * (x / 4) ^ q := hG (x / 4) (by linarith)
      _ ≤ C * x ^ q :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) hq) hC
  linarith

/-- If `1 / 2 ≤ θ < 1` and `riemannZeta` is zero-free in `Re s > θ`, then for every `ε > 0`,
`fourthSampleBudget θ K ≤ exp(ε * logStart4 K)` holds **eventually for all large `K`**. -/
theorem eventually_fourthSampleBudget_of_zeroFree_same {θ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1)
    (hz : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop, fourthSampleBudget θ K ≤ Real.exp (ε * logStart4 K) := by
  let η : ℝ := min ((1 - θ) / 2) (ε / 4)
  have hη_pos : 0 < η := lt_min (by linarith) (by linarith)
  have hθη_lt : θ + η < 1 := by
    have : η ≤ (1 - θ) / 2 := min_le_left _ _
    linarith
  have hη_eps : η * (3 / 2) ≤ ε / 2 := by
    have : η ≤ ε / 4 := min_le_right _ _
    linarith
  obtain ⟨C, hC_pos, hG⟩ :=
    DirectRampEquivalence.abs_rampG_le_of_zeroFree hθ (by linarith : θ < θ + η) hθη_lt hz
  let q : ℝ := θ + η
  have hq_nonneg : 0 ≤ q := by dsimp [q]; linarith
  let M : ℝ := 6 * C * (16 : ℝ) ^ q
  have hM_pos : 0 < M := by dsimp [M]; positivity
  have hroom : ∀ᶠ U : ℝ in atTop, 0 < U ∧ (U / 2) * M ≤ Real.exp ((ε / 2) * U) := by
    have ha : 0 < ε / 2 := half_pos hε
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (tendsto_exp_mul_div_rpow_atTop 1 (ε / 2) ha).eventually_ge_atTop (M / 2)]
      with U hU0 hlin
    have h1 : (M / 2) * U ≤ Real.exp ((ε / 2) * U) :=
      (le_div_iff₀ hU0).mp (by simpa using hlin)
    exact ⟨hU0, by linarith⟩
  filter_upwards [eventually_ge_atTop 2, logStart4_tendsto.eventually hroom] with K hK2 hU
  obtain ⟨hU_pos, hUM⟩ := hU
  have hK1 : 1 ≤ K := by omega
  have horder : K ^ 2 ≤ K ^ 3 := pow_le_pow_right₀ hK1 (by decide)
  let N : ℕ := K ^ 3 - K ^ 2
  let t (i : ℕ) : ℝ := Real.log (sample4 (K ^ 2 + i))
  have ht0 : t 0 = logStart4 K := by simp [t, logStart4]
  have htN : t N = (3 / 2) * logStart4 K := by
    dsimp [t, N]
    rw [Nat.add_sub_of_le horder]
    simp only [sample4, logStart4, Nat.cast_pow, Real.log_pow]
    norm_num
    ring
  have hterm : ∀ i ∈ Finset.range N,
      PrimeCentreMean.gapCost θ (sample4 (K ^ 2 + i)) (sample4 (K ^ 2 + i + 1)) ≤
        (t (i + 1) - t i) * (M * Real.exp ((ε / 2) * logStart4 K)) := by
    intro i hi_mem
    have hi : i < N := Finset.mem_range.mp hi_mem
    let k : ℕ := K ^ 2 + i
    have hk_ge4 : 4 ≤ k := by
      have : 4 ≤ K ^ 2 := by nlinarith
      dsimp [k]; omega
    have hk_le : k ≤ K ^ 3 := by dsimp [k, N] at hi ⊢; omega
    let a : ℝ := sample4 k
    let b : ℝ := sample4 (k + 1)
    have ha4 : 4 ≤ a := by
      have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 2 ≤ k by omega)
      calc (4 : ℝ) ≤ (2 : ℝ) ^ 4 := by norm_num
        _ ≤ (k : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hk_real 4
    have hb4 : 4 ≤ b := by
      have hab_mono : a ≤ b := sample4_mono (Nat.le_succ k)
      linarith
    have ha_pos : 0 < a := by linarith
    have hab : a ≤ b := sample4_mono (Nat.le_succ k)
    have hb16a : b ≤ 16 * a := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      have h2k : ((k + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by push_cast; linarith
      calc b = ((k + 1 : ℕ) : ℝ) ^ 4 := rfl
        _ ≤ (2 * (k : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) h2k 4
        _ = 16 * a := by dsimp [a, sample4]; ring
    have hlog_nonneg : 0 ≤ t (i + 1) - t i :=
      sub_nonneg.mpr (Real.log_le_log ha_pos hab)
    have hea : excess a ≤ M * a ^ q := by
      calc excess a
          ≤ 6 * C * a ^ q := excess_le_six_rampG4 hC_pos.le hq_nonneg hG ha4
        _ ≤ 6 * C * (16 * a) ^ q :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha_pos.le (by linarith) hq_nonneg)
              (by positivity)
        _ = M * a ^ q := by
            dsimp [M]
            rw [Real.mul_rpow (by norm_num) ha_pos.le]
            ring
    have heb : excess b ≤ M * a ^ q := by
      calc excess b
          ≤ 6 * C * b ^ q := excess_le_six_rampG4 hC_pos.le hq_nonneg hG hb4
        _ ≤ 6 * C * (16 * a) ^ q :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hb16a hq_nonneg)
              (by positivity)
        _ = M * a ^ q := by
            dsimp [M]
            rw [Real.mul_rpow (by norm_num) ha_pos.le]
            ring
    have hmax : max (excess a) (excess b) ≤ M * a ^ q := max_le hea heb
    have hlog_a_le : Real.log a ≤ (3 / 2) * logStart4 K := by
      rw [← htN]
      dsimp [a, t, N]
      rw [Nat.add_sub_of_le horder]
      exact Real.log_le_log ha_pos (sample4_mono hk_le)
    have hweight : Real.exp (-θ * Real.log a) * max (excess a) (excess b) ≤
        M * Real.exp ((ε / 2) * logStart4 K) := by
      calc Real.exp (-θ * Real.log a) * max (excess a) (excess b)
          ≤ Real.exp (-θ * Real.log a) * (M * a ^ q) :=
            mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le
        _ = M * Real.exp (η * Real.log a) := by
            rw [Real.rpow_def_of_pos ha_pos]
            have hexp : Real.exp (-θ * Real.log a) * Real.exp (Real.log a * q) =
                Real.exp (η * Real.log a) := by
              rw [← Real.exp_add]
              congr 1
              dsimp [q]
              ring
            calc Real.exp (-θ * Real.log a) * (M * Real.exp (Real.log a * q))
                = M * (Real.exp (-θ * Real.log a) * Real.exp (Real.log a * q)) := by ring
              _ = M * Real.exp (η * Real.log a) := by rw [hexp]
        _ ≤ M * Real.exp ((ε / 2) * logStart4 K) := by
            apply mul_le_mul_of_nonneg_left _ hM_pos.le
            apply Real.exp_le_exp.mpr
            calc η * Real.log a
                ≤ η * ((3 / 2) * logStart4 K) := mul_le_mul_of_nonneg_left hlog_a_le hη_pos.le
              _ = (η * (3 / 2)) * logStart4 K := by ring
              _ ≤ (ε / 2) * logStart4 K := mul_le_mul_of_nonneg_right hη_eps hU_pos.le
    change PrimeCentreMean.gapCost θ a b ≤ (t (i + 1) - t i) * _
    unfold PrimeCentreMean.gapCost
    exact mul_le_mul_of_nonneg_left hweight hlog_nonneg
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul, widths4 t N, ht0, htN,
    show (3 / 2) * logStart4 K - logStart4 K = logStart4 K / 2 by ring] at hsum
  calc fourthSampleBudget θ K
      ≤ (logStart4 K / 2) * (M * Real.exp ((ε / 2) * logStart4 K)) := hsum
    _ = ((logStart4 K / 2) * M) * Real.exp ((ε / 2) * logStart4 K) := by ring
    _ ≤ Real.exp ((ε / 2) * logStart4 K) * Real.exp ((ε / 2) * logStart4 K) :=
        mul_le_mul_of_nonneg_right hUM (Real.exp_pos _).le
    _ = Real.exp (ε * logStart4 K) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- If `1 / 2 ≤ θ < 1` and `riemannZeta` is zero-free in `Re s > θ`, then
`SubpowerFourthSamples θ` holds at the same `θ`. -/
theorem subpowerFourthSamples_of_zeroFree_same {θ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1)
    (hz : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    SubpowerFourthSamples θ := by
  intro ε hε J
  obtain ⟨K₀, hK₀⟩ :=
    eventually_atTop.mp (eventually_fourthSampleBudget_of_zeroFree_same hθ hθ1 hz hε)
  exact ⟨max J K₀, le_max_left J K₀, hK₀ (max J K₀) (le_max_right J K₀)⟩

/-- If `1 / 2 ≤ θ₀ < θ < 1` and `riemannZeta` is zero-free in `Re s > θ₀`, then for every `ε > 0`,
`fourthSampleBudget θ K ≤ exp(ε * logStart4 K)` holds eventually for all large `K`. -/
theorem eventually_fourthSampleBudget_of_zeroFree {θ₀ θ : ℝ}
    (hθ₀ : 1 / 2 ≤ θ₀) (hθ₀θ : θ₀ < θ) (hθ1 : θ < 1)
    (hz : ∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop, fourthSampleBudget θ K ≤ Real.exp (ε * logStart4 K) :=
  eventually_fourthSampleBudget_of_zeroFree_same (hθ₀.trans hθ₀θ.le) hθ1
    (fun s hs => hz s (hθ₀θ.trans hs)) hε

/-- If `1 / 2 ≤ θ₀ < θ < 1` and `riemannZeta` is zero-free in `Re s > θ₀`, then
`SubpowerFourthSamples θ` holds. -/
theorem subpowerFourthSamples_of_zeroFree {θ₀ θ : ℝ}
    (hθ₀ : 1 / 2 ≤ θ₀) (hθ₀θ : θ₀ < θ) (hθ1 : θ < 1)
    (hz : ∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0) :
    SubpowerFourthSamples θ :=
  subpowerFourthSamples_of_zeroFree_same (hθ₀.trans hθ₀θ.le) hθ1
    (fun s hs => hz s (hθ₀θ.trans hs))

/-- **Pointwise Equivalence (`subpowerFourthSamples_iff_zeroFree`):**
At every single exponent `θ ∈ (1 / 2, 1)`, `SubpowerFourthSamples θ` is equivalent to zero-freeness
of `riemannZeta` in `Re s > θ`. -/
theorem subpowerFourthSamples_iff_zeroFree {θ : ℝ} (half : 1 / 2 < θ) (one : θ < 1) :
    SubpowerFourthSamples θ ↔ ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 :=
  ⟨zeroFree_of_fourthSamples half one, subpowerFourthSamples_of_zeroFree_same half.le one⟩

/-- **Three-Way Half-Plane Equivalence (`fourthSamples_three_way_iff`):**
For any `1 / 2 ≤ θ₀ < 1` (and in fact any `1 / 2 ≤ θ₀`), the following three conditions are
equivalent:
1. `∀ θ ∈ Set.Ioo θ₀ 1, SubpowerFourthSamples θ`,
2. `∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0`,
3. `∀ θ ∈ Set.Ioo θ₀ 1, PrimeCentreMean.SmallExcessMean θ (1 / 2)`. -/
theorem fourthSamples_three_way_iff {θ₀ : ℝ} (hθ₀ : 1 / 2 ≤ θ₀) :
    ((∀ θ ∈ Set.Ioo θ₀ 1, SubpowerFourthSamples θ) ↔
      (∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0)) ∧
    ((∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0) ↔
      (∀ θ ∈ Set.Ioo θ₀ 1, PrimeCentreMean.SmallExcessMean θ (1 / 2))) := by
  have h13 : (∀ θ ∈ Set.Ioo θ₀ 1, SubpowerFourthSamples θ) →
      (∀ θ ∈ Set.Ioo θ₀ 1, PrimeCentreMean.SmallExcessMean θ (1 / 2)) :=
    fun hS θ hθ => excessMean_of_fourthSamples (lt_of_le_of_lt hθ₀ hθ.1) (hS θ hθ)
  have h32 : (∀ θ ∈ Set.Ioo θ₀ 1, PrimeCentreMean.SmallExcessMean θ (1 / 2)) →
      (∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0) := by
    intro hE s hs
    rcases le_or_gt 1 s.re with hs1 | hs1
    · exact riemannZeta_ne_zero_of_one_le_re hs1
    · let θ : ℝ := (θ₀ + s.re) / 2
      have hθ_mem : θ ∈ Set.Ioo θ₀ 1 := ⟨by dsimp [θ]; linarith, by dsimp [θ]; linarith⟩
      exact PrimeCentreMean.zeroFree_of_excessMean (by linarith [hθ_mem.1]) hθ_mem.2
        (by norm_num) (hE θ hθ_mem) s (by dsimp [θ]; linarith)
  have h21 : (∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0) →
      (∀ θ ∈ Set.Ioo θ₀ 1, SubpowerFourthSamples θ) :=
    fun hz θ hθ => subpowerFourthSamples_of_zeroFree hθ₀ hθ.1 hθ.2 hz
  exact ⟨⟨fun h1 => h32 (h13 h1), h21⟩, ⟨fun h2 => h13 (h21 h2), h32⟩⟩

/-- `List.TFAE` formulation of `fourthSamples_three_way_iff`. -/
theorem fourthSamples_three_way_tfae {θ₀ : ℝ} (hθ₀ : 1 / 2 ≤ θ₀) :
    List.TFAE
      [ ∀ θ ∈ Set.Ioo θ₀ 1, SubpowerFourthSamples θ
      , ∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0
      , ∀ θ ∈ Set.Ioo θ₀ 1, PrimeCentreMean.SmallExcessMean θ (1 / 2) ] := by
  obtain ⟨h12, h23⟩ := fourthSamples_three_way_iff hθ₀
  tfae_have 1 ↔ 2 := h12
  tfae_have 2 ↔ 3 := h23
  tfae_finish

/-- **Riemann Hypothesis Fourth-Power Tent Equivalence (`rh_iff_subpowerFourthSamples`):**
`RiemannHypothesis` holds if and only if `SubpowerFourthSamples θ` holds for every `θ ∈ (1/2, 1)`. -/
theorem rh_iff_subpowerFourthSamples :
    RiemannHypothesis ↔ ∀ θ ∈ Set.Ioo (1 / 2 : ℝ) 1, SubpowerFourthSamples θ := by
  rw [(fourthSamples_three_way_iff (θ₀ := 1 / 2) le_rfl).1]
  rw [← (DirectRampEquivalence.ordinaryWindow_three_way_iff (θ₀ := 1 / 2) ⟨le_rfl, by norm_num⟩).1]
  exact DirectRampEquivalence.rh_iff_ordinaryWindowUnit_above_half

end PrimeCentreMean.Sparse
