import Mathlib
import ZetaClassical.RampPNT

/-! Centred prime-power ramp `Compat.rampSz`, `Compat.rampGz`, continuity, and prime number
theorem error bound from `ZetaClassical.rampPNTStatement` (Mathlib + `classical-zeta` only). -/

open scoped ArithmeticFunction.vonMangoldt
open Complex Set Filter Topology

noncomputable section

namespace Compat

def rampSz (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)

def rampGz (x : ℝ) : ℝ := rampSz x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

theorem rampSz_eq_rampS (x : ℝ) : rampSz x = IndependentLandau.rampS x := by
  unfold rampSz IndependentLandau.rampS
  have hsub : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.range (⌊x⌋₊ + 1) := fun n hn =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
  rw [← Finset.sum_subset hsub (fun n hn hnot => ?_)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr h1
    have hle : (n : ℝ) ≤ x := (Nat.le_floor_iff' (by omega)).mp h2
    unfold IndependentLandau.rampT
    rw [max_eq_left (sub_nonneg.mpr ((one_le_div hn0).mpr hle))]
  · have h0 : n = 0 := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨by omega, Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)⟩)
    rw [h0, IndependentLandau.rampT_zero]

theorem rampGz_eq_rampG (x : ℝ) : rampGz x = IndependentLandau.rampG x := by
  rw [rampGz, rampSz_eq_rampS, IndependentLandau.rampG_eq]

def RampGzPNT : Prop :=
  ∃ c K : ℝ, 0 < c ∧ ∀ y : ℝ, 2 ≤ y →
    |Compat.rampGz y| ≤ K * y * Real.exp (-c * Real.sqrt (Real.log y))

/-- Prime number theorem for the centred ramp, from `ZetaClassical.rampPNTStatement`. -/
theorem gzPNT : RampGzPNT := by
  obtain ⟨c, K, hc, h⟩ := ZetaClassical.rampPNTStatement
  exact ⟨c, K, hc, fun y hy => by rw [rampGz_eq_rampG]; exact h y hy⟩

lemma perron_Sz_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) : Compat.rampSz x = 0 := by
  unfold Compat.rampSz
  refine Finset.sum_eq_zero fun n hn => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  obtain rfl : n = 1 := le_antisymm (h2.trans (Nat.floor_le_one_of_le_one hx)) h1
  simp

private lemma rampS_extend {x z : ℝ} (hxz : x ≤ z) :
    IndependentLandau.rampS x = ∑ n ∈ Finset.range (⌊z⌋₊ + 1), IndependentLandau.rampT n x := by
  unfold IndependentLandau.rampS
  refine Finset.sum_subset
    (Finset.range_subset_range.mpr (Nat.succ_le_succ (Nat.floor_le_floor hxz))) ?_
  intro n _ hn
  exact IndependentLandau.rampT_eq_zero_of_floor_lt
    (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hn)

lemma perron_Sz_continuousAt (y : ℝ) : ContinuousAt (fun x => (Compat.rampSz x : ℂ)) y := by
  have hfin : ContinuousAt
      (fun x : ℝ => ∑ n ∈ Finset.range (⌊y + 1⌋₊ + 1), IndependentLandau.rampT n x) y := by
    refine Continuous.continuousAt (continuous_finsetSum _ fun n _ => ?_)
    unfold IndependentLandau.rampT
    exact continuous_const.mul
      (((continuous_id.div_const _).sub continuous_const).max continuous_const)
  have hS : ContinuousAt Compat.rampSz y := by
    refine hfin.congr ?_
    filter_upwards [Iio_mem_nhds (lt_add_one y)] with x hx
    rw [rampSz_eq_rampS, rampS_extend (le_of_lt hx)]
  exact Complex.continuous_ofReal.continuousAt.comp hS

end Compat
