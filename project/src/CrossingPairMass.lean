import UniformShellCriterion

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real

private theorem worst_exists (n : ℕ) :
    ∃ j : ℕ, j ∈ range (bandCount n 0) ∧
      uniformShellScore n = -fullFirstShell n j / share n 0 1 := by
  exact exists_mem_eq_sup' (nonempty_range_iff.mpr (by unfold bandCount; omega)) _

/-- Pick the first maximizer so that each sample uses the same shell at every threshold. -/
def worstShell (n : ℕ) : ℕ := by
  classical
  exact Nat.find (worst_exists n)

theorem worst_shell_spec (n : ℕ) : worstShell n < bandCount n 0 ∧
    uniformShellScore n = -fullFirstShell n (worstShell n) / share n 0 1 := by
  classical
  have spec := Nat.find_spec (worst_exists n)
  exact ⟨mem_range.mp spec.1,spec.2⟩

theorem worst_shell_pos_of_crossing {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hit : t < uniformShellScore n) : 1 ≤ worstShell n := by
  by_contra! h
  have eq := (worst_shell_spec n).2
  rw [show worstShell n = 0 by omega,full_first_zero_bin,neg_zero,zero_div] at eq
  linarith

def shellScale (n : ℕ) : ℝ := 4*(bandCount n 0 : ℝ)/(n:ℝ)^2

private theorem scaled_square (n : ℕ) (hn : 1 ≤ n) :
    (shellScale n)^2 * (fullFirstShell n (worstShell n))^2 = (uniformShellScore n)^2 := by
  have np : (n:ℝ) ≠ 0 := (Nat.cast_pos (α:=ℝ).mpr hn).ne'
  have bp : (bandCount n 0:ℝ) ≠ 0 := by unfold bandCount; positivity
  rw [(worst_shell_spec n).2]
  unfold share shellScale
  field_simp
  ring

/-- A signed part of the square, counted only at genuine one-sided crossings. -/
def crossingPairMass (part : ℕ → ℕ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Icc m (m^2), if t < uniformShellScore n then
    ((t / (uniformShellScore n)^2) * (shellScale n)^2 * part n (worstShell n)) * (n:ℝ)⁻¹
    else 0

/-- Division by the observed squared score makes this an identity for the original
weak frequency, even when the positive and negative tails have different sizes. -/
theorem crossing_pair_mass_split (p q : ℕ → ℕ → ℝ)
    (decomp : ∀ n j, (fullFirstShell n j)^2 = p n j + q n j)
    {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) :
    t * frequency uniformShellScore m t = crossingPairMass p m t + crossingPairMass q m t := by
  unfold frequency crossingPairMass
  rw [mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  split_ifs with hit
  · have nonzero := (ht.trans hit).ne'
    have eq := scaled_square n (hm.trans (mem_Icc.mp hn).1)
    rw [decomp] at eq
    have cancel : (t / (uniformShellScore n)^2) * (uniformShellScore n)^2 = t :=
      div_mul_cancel₀ _ (pow_ne_zero _ nonzero)
    calc
      _ = ((t / (uniformShellScore n)^2) * (uniformShellScore n)^2) * (n:ℝ)⁻¹ := by rw [cancel]
      _ = _ := by rw [←eq]; ring
  · simp

private theorem capped_multiplier {z t : ℝ} (one : 1 ≤ t) (hit : t < z) :
    0 ≤ t/z^2 ∧ t/z^2*t ≤ 1 := by
  have zp : 0 < z := by linarith
  refine ⟨div_nonneg (by linarith) (sq_nonneg _),?_⟩
  rw [div_mul_eq_mul_div,←sq,(div_le_one (sq_pos_of_pos zp))]
  exact pow_le_pow_left₀ (zero_le_one.trans one) hit.le 2

private theorem scaled_part_bound {p : ℕ → ℕ → ℝ} {C η : ℝ} (cp : 0 ≤ C)
    (cap : ∀ n j, 1 ≤ n → 1 ≤ j → |p n j| ≤ C*(n:ℝ)^4*(n:ℝ)^η)
    {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    (shellScale n)^2 * |p n j| ≤ (16*C)*(1+8*log n)^2*(n:ℝ)^η := by
  have np : (n:ℝ) ≠ 0 := (Nat.cast_pos (α:=ℝ).mpr hn).ne'
  have bb := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (bandCount n 0)) (band_count_log hn) 2
  calc
    _ ≤ (shellScale n)^2 * (C*(n:ℝ)^4*(n:ℝ)^η) :=
      mul_le_mul_of_nonneg_left (cap n j hn hj) (sq_nonneg _)
    _ = (16*C)*(bandCount n 0:ℝ)^2*(n:ℝ)^η := by unfold shellScale; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bb (by positivity)) (by positivity)

/-- A raw pair contribution of size O(t*n^(4+η)) passes every threshold on
every sufficiently late block at all exponents δ > 2η. -/
theorem crossing_pair_part_subpower {p : ℝ → ℕ → ℕ → ℝ} {C η δ : ℝ}
    (cp : 0 ≤ C) (hp : 0 ≤ η) (gap : 2*η < δ)
    (cap : ∀ t : ℝ, 1 ≤ t → ∀ n j, 1 ≤ n → 1 ≤ j →
      |p t n j| ≤ (C*t)*(n:ℝ)^4*(n:ℝ)^η) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 1 ≤ t → |crossingPairMass (p t) m t| ≤ (m:ℝ)^δ := by
  let κ := (δ-2*η)/3
  have kp : 0 < κ := by dsimp [κ]; linarith
  obtain ⟨N, absorb⟩ := eventually_atTop.mp (absorb_log_square (16*C) (by positivity) kp)
  filter_upwards [eventually_ge_atTop N,eventually_ge_atTop (1:ℕ),absorb_log_square 1 zero_le_one kp]
    with m late hm hlog t one
  have mp := Nat.cast_pos (α:=ℝ).mpr hm
  let H := (m:ℝ)^(2*(η+κ))
  have hnon : 0 ≤ H := by dsimp [H]; positivity
  have term (n : ℕ) (hn : n ∈ Icc m (m^2)) :
      |if t < uniformShellScore n then
        (t / (uniformShellScore n)^2 * (shellScale n)^2 * p t n (worstShell n)) * (n:ℝ)⁻¹
        else 0| ≤ H*(n:ℝ)⁻¹ := by
    obtain ⟨mn,nm⟩ := mem_Icc.mp hn
    have np := Nat.cast_pos (α:=ℝ).mpr (hm.trans mn)
    split_ifs with hit
    · have mult := capped_multiplier one hit
      have point := scaled_part_bound (mul_nonneg cp (zero_le_one.trans one)) (cap t one) (hm.trans mn)
        (worst_shell_pos_of_crossing (zero_le_one.trans one) hit)
      have scaled := mul_le_mul_of_nonneg_right (absorb n (late.trans mn)) (rpow_nonneg np.le η)
      have up : (n:ℝ) ≤ (m:ℝ)^2 := by exact_mod_cast nm
      have power := rpow_le_rpow np.le up (show 0 ≤ η+κ by linarith)
      rw [←rpow_natCast_mul mp.le] at power
      norm_num only [Nat.cast_ofNat] at power
      rw [←rpow_add np,add_comm κ η] at scaled
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)⁻¹),abs_mul,abs_mul,
        abs_of_nonneg mult.1,abs_of_nonneg (sq_nonneg _)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [mul_assoc]
      apply le_trans _ (scaled.trans power)
      calc
        _ ≤ _ := mul_le_mul_of_nonneg_left point mult.1
        _ = (t/(uniformShellScore n)^2*t)*((16*C)*(1+8*log n)^2*(n:ℝ)^η) := by ring
        _ ≤ _ := mul_le_of_le_one_left (by positivity) mult.2
    · rw [abs_zero]; positivity
  have lm := log_natCast_nonneg m
  have harm : (∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹) ≤ (m:ℝ)^κ :=
    (harmonic_window hm).trans (by nlinarith only [lm,sq_nonneg (8*log m),hlog])
  calc
    _ ≤ _ := abs_sum_le_sum_abs ..
    _ ≤ ∑ n ∈ Icc m (m^2), H*(n:ℝ)⁻¹ := sum_le_sum term
    _ = H*(∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹) := (mul_sum ..).symm
    _ ≤ H*(m:ℝ)^κ := mul_le_mul_of_nonneg_left harm hnon
    _ = _ := by dsimp [H]; rw [←rpow_add mp]; congr 1; dsimp [κ]; ring

end RiemannReduction.ShortTail.LossFrequency
