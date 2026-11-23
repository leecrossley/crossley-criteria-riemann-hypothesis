import CrossingPairMass
import LargeGcdShells

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real

/-- The two kernel factors and the length of the shell save three powers of its quotient. -/
def rayCut (η t : ℝ) (n j : ℕ) : ℕ :=
  ⌊t * (n:ℝ)^η * ((2:ℝ)^j)^3 / (1+log ((2:ℝ)^j))^2⌋₊

theorem ray_kernel_budget (η t : ℝ) (ht : 0 ≤ t) (n j : ℕ) :
    (2*(rayCut η t n j:ℝ)*(n^4/2^j:ℕ))*
      (kernelConstant*(1+log ((2:ℝ)^j))/(2:ℝ)^j)^2 ≤
      (2*kernelConstant^2*t)*(n:ℝ)^4*(n:ℝ)^η := by
  let Q : ℝ := 2^j
  let L : ℝ := 1+log Q
  have qp : 0 < Q := by dsimp [Q]; positivity
  have lg : 0 ≤ log Q := log_nonneg (one_le_pow₀ (by norm_num))
  have lp : 0 < L := by dsimp [L]; linarith
  have cut : (rayCut η t n j : ℝ) ≤ t * (n:ℝ)^η * Q^3 / L^2 :=
    Nat.floor_le (by positivity : 0 ≤ t * (n:ℝ)^η * Q^3 / L^2)
  have endpoint : ((n^4/2^j:ℕ):ℝ) ≤ (n:ℝ)^4 / Q := by
    apply (le_div_iff₀ qp).mpr
    dsimp [Q]
    exact_mod_cast Nat.div_mul_le_self (n^4) (2^j)
  have product := mul_le_mul (mul_le_mul_of_nonneg_left cut (by norm_num : (0:ℝ)≤2)) endpoint
    (Nat.cast_nonneg _) (by positivity)
  have budget := mul_le_mul_of_nonneg_right product (sq_nonneg (kernelConstant*L/Q))
  apply budget.trans_eq
  field_simp

/-- The contribution of every reduced divisor ratio up to rayCut is paid
unconditionally on the same block at every real threshold t ≥ 1. -/
theorem bounded_ray_frequency {η δ : ℝ} (hp : 0 ≤ η) (gap : 2*η < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 1 ≤ t →
      |crossingPairMass (fun n j => largeGcdShellContribution n j (rayCut η t n j)) m t| ≤ (m:ℝ)^δ :=
  crossing_pair_part_subpower (C:=2*kernelConstant^2) (by positivity) hp gap
    (fun t ht n j _ jp => (large_gcd_shell_bound n j (rayCut η t n j) jp).trans
      (ray_kernel_budget η t (zero_le_one.trans ht) n j))

/-- The signed part left after removing the small reduced ratios.
Only the negative maximizer at actual threshold crossings enters the sum. -/
def remainingRayMass (δ : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  crossingPairMass (fun n j => smallGcdShellContribution n j (rayCut (δ/4) t n j)) m t

def sameBlockUpper (mass : ℕ → ℝ → ℝ) (δ : ℝ) : Prop :=
  ∃ C > (0:ℝ), ∀ A : ℕ, ∃ m ≥ A, ∀ k : ℕ, mass m ((2:ℝ)^k) ≤ C*(m:ℝ)^δ

abbrev sameBlockRayUpper (δ : ℝ) : Prop := sameBlockUpper (remainingRayMass δ) δ

theorem frequency_minus_remaining_rays {δ : ℝ} (ep : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 1 ≤ t →
      |t*frequency uniformShellScore m t - remainingRayMass δ m t| ≤ (m:ℝ)^δ := by
  filter_upwards [bounded_ray_frequency (η:=δ/4) (by positivity) (by linarith : 2*(δ/4)<δ),
    eventually_ge_atTop (1:ℕ)] with m paid hm t ht
  rw [crossing_pair_mass_split
    (fun n j => largeGcdShellContribution n j (rayCut (δ/4) t n j))
    (fun n j => smallGcdShellContribution n j (rayCut (δ/4) t n j))
    (fun n j => full_shell_gcd_square n j _) hm (zero_lt_one.trans_le ht)]
  simpa only [remainingRayMass,add_sub_cancel_right] using paid t ht

theorem uniform_frequency_iff_approximation (mass : ℝ → ℕ → ℝ → ℝ)
    (estimate : ∀ δ > (0:ℝ), ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 1 ≤ t →
      |t*frequency uniformShellScore m t - mass δ m t| ≤ (m:ℝ)^δ) :
    sameBlockWeak uniformShellScore ↔ ∀ δ > (0:ℝ), sameBlockUpper (mass δ) δ := by
  constructor <;> intro h δ ep <;> obtain ⟨C,cp,blocks⟩ := h δ ep <;>
    obtain ⟨N,error⟩ := eventually_atTop.mp (estimate δ ep) <;>
    refine ⟨C+1,by linarith,fun A => ?_⟩ <;>
    obtain ⟨m,hm,all⟩ := blocks (max A N) <;>
    refine ⟨m,(le_max_left ..).trans hm,fun k => ?_⟩ <;>
    have close := abs_le.mp (error m ((le_max_right ..).trans hm) ((2:ℝ)^k)
      (one_le_pow₀ (by norm_num : (1:ℝ)≤2))) <;>
    linarith only [close.1,close.2,all k]

/-- The remaining signed correlation has exactly the same common-block
upper-bound requirement as the one-sided shell frequency. -/
theorem uniform_frequency_iff_remaining_rays :
    sameBlockWeak uniformShellScore ↔ ∀ δ > (0:ℝ), sameBlockRayUpper δ :=
  uniform_frequency_iff_approximation remainingRayMass (fun _ ep => frequency_minus_remaining_rays ep)

theorem rh_of_remaining_rays (remaining : ∀ δ > (0:ℝ), sameBlockRayUpper δ) : RiemannHypothesis :=
  rh_of_uniform_shell_score (uniform_frequency_iff_remaining_rays.mpr remaining)

end RiemannReduction.ShortTail.LossFrequency
