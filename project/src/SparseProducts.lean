import Reflection
import PrimeBandWeights
import PrimeWindow
import TurningPoints

namespace RiemannReduction.PrimeGrid

private lemma exp_mem_block {N : ℕ} (pos : 0 < (N:ℝ)) {u : ℝ}
    (hu : u ∈ Set.Icc (Real.log N) ((1+1)*Real.log N)) :
    Real.exp u ∈ Set.Icc (N:ℝ) (↑(N*N : ℕ) : ℝ) := by
  refine ⟨(Real.log_le_iff_le_exp pos).mp hu.1, ?_⟩
  have h : u ≤ Real.log N + Real.log N := by linarith [hu.2]
  simpa [Real.exp_add, Real.exp_log pos] using Real.exp_le_exp.mpr h

/-- An unbounded sequence of whole passing blocks of integers suffices for RH. -/
theorem rh_of_integer_product_blocks
    (blocks : ∀ m : ℕ, ∃ N ≥ m, ∀ j ∈ Finset.Icc N (N*N), Passes j) :
    RiemannHypothesis := by
  apply RiemannReduction.rh_of_right
  intro s hs _
  apply ThetaTransfer.zeroFree_of_prime_sign_windows (δ := 1) (by norm_num) _ s hs
  intro U₀
  obtain ⟨N, hN, checks⟩ := blocks ⌈Real.exp U₀⌉₊
  have lo : Real.exp U₀ ≤ (N : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hN)
  have pos : 0 < (N : ℝ) := (Real.exp_pos _).trans_le lo
  refine ⟨Real.log N, (Real.le_log_iff_exp_le pos).mpr lo, fun u hu => ?_⟩
  have mem := exp_mem_block pos hu
  have b := block_bound checks mem.1 mem.2
  rw [sumTo_eq_primeSum] at b
  unfold ThetaTransfer.primeDeficit
  linarith

#print axioms rh_of_integer_product_blocks

/-- It is enough to prove the prime-product inequality at the two endpoints and
at the interior doubled primes on arbitrarily late square intervals. -/
theorem rh_of_doubled_prime_blocks
    (blocks : ∀ m : ℕ, ∃ N ≥ m, Passes N ∧ Passes (N*N) ∧
      ∀ p : ℕ, p.Prime → N < 2*p → 2*p < N*N → Passes (2*p)) : RiemannHypothesis := by
  apply rh_of_integer_product_blocks
  intro m
  obtain ⟨N,lo,tests⟩ := blocks m
  have h : N ≤ N*N := Nat.le_self_pow (by decide : 2 ≠ 0) N |>.trans_eq (pow_two N)
  exact ⟨N,lo,(block_passes_iff_endpoints_and_double_primes h).mpr tests⟩

#print axioms rh_of_doubled_prime_blocks

/-- If RH failed, every sufficiently late square-length block would contain both outcomes. -/
theorem mixed_blocks_of_not_rh (h : ¬ RiemannHypothesis) :
    ∃ M : ℕ, ∀ N ≥ M, (∃ j ∈ Finset.Icc N (N*N), Passes j) ∧
      (∃ k ∈ Finset.Icc N (N*N), ¬ Passes k) := by
  have fails := mt rh_of_integer_product_blocks h
  push Not at fails
  obtain ⟨m, hf⟩ := fails
  have zero : ¬ (∀ s : ℂ, 1/2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :=
    fun right => h (RiemannReduction.rh_of_right right)
  push Not at zero
  obtain ⟨s, hs, _, hz⟩ := zero
  obtain ⟨U₀, hits⟩ := ThetaTransfer.prime_deficit_on_every_late_window
    (θ := 1/2) (δ := 1) hz (by norm_num) (by norm_num) (by norm_num) hs
  refine ⟨max m ⌈Real.exp U₀⌉₊, fun N hN => ⟨?_, hf N ((le_max_left _ _).trans hN)⟩⟩
  have lo : Real.exp U₀ ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hN))
  have pos := (Real.exp_pos U₀).trans_le lo
  obtain ⟨u, hu, high⟩ := hits (Real.log N) ((Real.le_log_iff_exp_le pos).mpr lo)
  have mem := exp_mem_block pos hu
  apply exists_pass_of_strict_bound mem.1 mem.2
  rw [sumTo_eq_primeSum]
  have strict := (Real.exp_pos _).trans high
  unfold ThetaTransfer.primeDeficit at strict
  linarith

#print axioms mixed_blocks_of_not_rh
end RiemannReduction.PrimeGrid
