import PrimeCentreCells
import ZeroFreeShellMoment

open MeasureTheory Set Filter
open RiemannReduction.ShortTail.LossFrequency

noncomputable section
namespace PrimeCentreMean

def centre (p : ℕ) : ℝ := 2*(p:ℝ)

def gapCost (θ a b : ℝ) : ℝ :=
  (Real.log b - Real.log a) *
  (Real.exp (-θ * Real.log a) * max (excess a) (excess b))

def budget (θ : ℝ) (p : ℕ → ℕ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, gapCost θ (centre (p i)) (centre (p (i+1)))

/-- Only indices through k are used. The last centre may lie past the right window edge. -/
def SmallPrimeCentreBudget (θ δ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ U₀ : ℝ, ∃ (p : ℕ → ℕ) (k : ℕ),
    (∀ i ≤ k, (p i).Prime) ∧
    (∀ i < k, p i < p (i+1) ∧ ∀ r : ℕ, r.Prime → r ≤ p i ∨ p (i+1) ≤ r) ∧
    U₀ ≤ Real.log (centre (p 0)) ∧
    (1+δ) * Real.log (centre (p 0)) ≤ Real.log (centre (p k)) ∧
    budget θ p k ≤ Real.exp (ε * Real.log (centre (p 0)))

private theorem continuous_density (θ : ℝ) : Continuous (excessDensity θ) := by
  have h : Continuous excess := continuous_iff_continuousAt.mpr fun x =>
    ((excess_continuousOn (x-1) (x+1)) x (show x ∈ Icc (x-1) (x+1) by
      constructor <;> linarith)).continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  unfold excessDensity
  fun_prop

private theorem density_nonneg (θ u : ℝ) : 0 ≤ excessDensity θ u :=
  mul_nonneg (le_max_left ..) (Real.exp_pos _).le

/-- An unconditional bound for the mass of the excess across one prime gap. -/
theorem integral_on_prime_gap {θ a b : ℝ} (ht : 0 ≤ θ) (ha : 0 < a) (hab : a ≤ b)
    (noCentre : ∀ p : ℕ, p.Prime → 2*(p:ℝ) ≤ a ∨ b ≤ 2*(p:ℝ)) :
    (∫ u in Real.log a..Real.log b, excessDensity θ u) ≤ gapCost θ a b := by
  have hb := ha.trans_le hab
  have ord := Real.log_le_log ha hab
  have convex := excess_convex_between_centres noCentre
  let cap := Real.exp (-θ*Real.log a) * max (excess a) (excess b)
  calc
    (∫ u in Real.log a..Real.log b, excessDensity θ u)
      ≤ ∫ _ in Real.log a..Real.log b, cap := by
        apply intervalIntegral.integral_mono_on ord
          ((continuous_density θ).intervalIntegrable ..) intervalIntegrable_const
        intro u hu
        have mem : Real.exp u ∈ Icc a b := by
          constructor
          · simpa only [Real.exp_log ha] using Real.exp_le_exp.mpr hu.1
          · simpa only [Real.exp_log hb] using Real.exp_le_exp.mpr hu.2
        have bound := convex.le_max_of_mem_Icc (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) mem
        have decay := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hu.1 (neg_nonpos.mpr ht))
        calc excessDensity θ u ≤ max (excess a) (excess b) * Real.exp (-θ*Real.log a) :=
               mul_le_mul bound decay (Real.exp_pos _).le
                 ((le_max_left 0 _ : 0 ≤ excess a).trans (le_max_left _ _))
             _ = cap := mul_comm _ _
    _ = gapCost θ a b := by rw [intervalIntegral.integral_const]; rfl

/-- The finite sum over consecutive doubled primes controls the continuous common window. -/
theorem excessMean_of_primeCentreBudget {θ δ : ℝ} (ht : 0 ≤ θ) (width : 0 < δ)
    (small : SmallPrimeCentreBudget θ δ) : SmallExcessMean θ δ := by
  intro ε hε U₀
  obtain ⟨p,k,primes,gaps,start,stop,bound⟩ := small ε hε (max U₀ 0)
  let t (i : ℕ) := Real.log (centre (p i))
  have c := continuous_density θ
  have positive (i : ℕ) (hi : i ≤ k) : 0 < centre (p i) := by
    have h : 0 < (p i : ℝ) := by exact_mod_cast (primes i hi).pos
    unfold centre; positivity
  have start0 : 0 ≤ t 0 := (le_max_right _ _).trans start
  have full : t 0 ≤ t k := (show t 0 ≤ (1+δ)*t 0 by
    nlinarith only [mul_nonneg width.le start0]).trans stop
  have hsub : Icc (t 0) ((1+δ)*t 0) ⊆ Icc (t 0) (t k) :=
    Icc_subset_Icc_right stop
  refine ⟨t 0, (le_max_left _ _).trans start, c.continuousOn.integrableOn_Icc, ?_⟩
  calc
    (∫ u in Icc (t 0) ((1+δ)*t 0), excessDensity θ u) ≤
        ∫ u in Icc (t 0) (t k), excessDensity θ u :=
      setIntegral_mono_set c.continuousOn.integrableOn_Icc
        (Filter.Eventually.of_forall (density_nonneg θ)) (Filter.Eventually.of_forall hsub)
    _ = ∫ u in t 0..t k, excessDensity θ u := by
      rw [intervalIntegral.integral_of_le full, integral_Icc_eq_integral_Ioc]
    _ = ∑ i ∈ Finset.range k, ∫ u in t i..t (i+1), excessDensity θ u :=
      (intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => c.intervalIntegrable ..)).symm
    _ ≤ budget θ p k := by
      apply Finset.sum_le_sum
      intro i hi
      have ik := Finset.mem_range.mp hi
      have pair := gaps i ik
      apply integral_on_prime_gap ht (positive i ik.le)
      · unfold centre; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr pair.1.le) (by norm_num)
      · intro r hr
        rcases pair.2 r hr with left | right
        · exact Or.inl (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr left) (by norm_num))
        · exact Or.inr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr right) (by norm_num))
    _ ≤ Real.exp (ε * t 0) := bound

/-- The arithmetic input is the gap-weighted excess of the actual primes. -/
theorem shell298_of_primeCentreBudget {θ δ : ℝ} (half : 1/2 ≤ θ) (line : θ < 349/400)
    (width : 0 < δ) (small : SmallPrimeCentreBudget θ δ) :
    ∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m:ℝ)^(149/50:ℝ) :=
  full_shell_moment_of_zero_free half (by linarith)
    (zeroFree_of_excessMean half (by linarith) width
      (excessMean_of_primeCentreBudget (by linarith) width small)) (by linarith)

theorem no_small_budget_of_zero {θ δ : ℝ} {ρ : ℂ} (half : 1/2 ≤ θ) (one : θ < 1)
    (width : 0 < δ) (right : θ < ρ.re) (zero : riemannZeta ρ = 0) :
    ¬ SmallPrimeCentreBudget θ δ := fun small =>
  zeroFree_of_excessMean half one width
    (excessMean_of_primeCentreBudget (by linarith) width small) ρ right zero

theorem shell298_at_08724 {δ : ℝ} (width : 0 < δ)
    (small : SmallPrimeCentreBudget (2181/2500) δ) :
    ∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m:ℝ)^(149/50:ℝ) :=
  shell298_of_primeCentreBudget (by norm_num) (by norm_num) width small

end PrimeCentreMean
