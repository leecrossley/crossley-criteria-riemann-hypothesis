import ZeroFreeMertensBridge
import GcdGapFrequency
import ShellFirstMoment

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real

/-- An ordinary zero-free half-plane controls the actual maximum over all
complete shells, on every late block and at all positive real thresholds. -/
theorem full_shell_frequency_of_zero_free {θ δ : ℝ} (half : 1/2 ≤ θ) (one : θ ≤ 1)
    (nz : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) (gap : 8*θ-4<δ) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0<t →
      t*frequency uniformShellScore m t ≤ 2*(m:ℝ)^δ := by
  have dp : 0<δ := by linarith only [half,gap]
  let cut := powerCut (δ/8)
  let mask := fun _ _ _ : ℕ => True
  obtain ⟨N,align⟩ := eventually_atTop.mp (first_shell_event_eventually dp)
  filter_upwards [selected_layer_frequency_of_zeroFree half one nz gap cut mask,
    uniform_high_shell_subpower dp,eventually_ge_atTop (max N 1)] with m low high start t tp
  classical
  have cover : frequency uniformShellScore m t ≤
      eventMass (selectedLayerEvent cut mask) m t + eventMass (highFirstShellEvent δ) m t := by
    unfold frequency eventMass
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro n row
    have mn := (mem_Icc.mp row).1
    have nn : 1≤n := (le_max_right ..).trans (start.trans mn)
    by_cases hit : t < uniformShellScore n
    · rw [if_pos hit]
      obtain ⟨j,jp,bad⟩ := (uniform_event_iff_score nn tp).mpr hit
      by_cases small : (2:ℝ)^j < (n:ℝ)^(1-3*δ/16)
      · have shell : fullFirstShellEvent δ n t := ⟨j,jp,small,bad⟩
        obtain ⟨i,rank,_,cross⟩ := (align n ((le_max_left ..).trans (start.trans mn)) t tp.le).mpr shell
        have oneLayer : (1:ℝ) ≤ (halvingCount n i:ℝ) := by
          unfold halvingCount
          exact_mod_cast Nat.le_add_left 1 _
        have sh : 0 ≤ share n 0 t := by unfold share; positivity
        have layer : layerShare n i t ≤ share n 0 t := div_le_self sh oneLayer
        have yes : selectedLayerEvent cut mask n t :=
          ⟨i,rank,0,by unfold halvingCount; omega,trivial,Or.inl (cross.trans_le (neg_le_neg layer))⟩
        rw [if_pos yes]; split <;> simp
      · have yes : highFirstShellEvent δ n t := ⟨j,jp,le_of_not_gt small,bad⟩
        rw [if_pos yes]; split <;> simp
    · rw [if_neg hit]; split_ifs <;> positivity
  linarith only [mul_le_mul_of_nonneg_left cover tp.le,low t tp,high t tp]

private theorem ordinary_half_plane_of_rh (rh : RiemannHypothesis) :
    ∀ s : ℂ, (1/2:ℝ)<s.re → riemannZeta s ≠ 0 := by
  intro s half zero
  have nontrivial : ¬∃ k : ℕ, s= -2*(k+1) := by
    rintro ⟨k,rfl⟩
    simp at half
    linarith only [half,Nat.cast_nonneg (α:=ℝ) k]
  have pole : s ≠ 1 := by
    rintro rfl
    exact riemannZeta_ne_zero_of_one_le_re (by simp) zero
  exact (ne_of_gt half) (rh s zero nontrivial pole)

/-- Under RH all sufficiently late blocks and all positive real levels work.
The opposite implication requires only cofinal blocks and dyadic levels. -/
theorem full_shell_frequency_of_rh (rh : RiemannHypothesis) {δ : ℝ} (dp : 0<δ) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0<t →
      t*frequency uniformShellScore m t ≤ 2*(m:ℝ)^δ :=
  full_shell_frequency_of_zero_free (θ:=1/2) le_rfl (by norm_num)
    (ordinary_half_plane_of_rh rh) (by linarith only [dp])

theorem rh_iff_same_block_shell_frequency :
    RiemannHypothesis ↔ sameBlockWeak uniformShellScore := by
  refine ⟨?_,rh_of_uniform_shell_score⟩
  intro rh δ dp
  obtain ⟨N,all⟩ := eventually_atTop.mp (full_shell_frequency_of_rh rh dp)
  exact ⟨2,by norm_num,fun A => ⟨max A N,le_max_left ..,
    fun k => all (max A N) (le_max_right ..) ((2:ℝ)^k) (by positivity)⟩⟩

theorem rh_iff_same_block_far_gap :
    RiemannHypothesis ↔ ∀ δ > (0:ℝ), sameBlockUpper (farGapMass δ) δ :=
  rh_iff_same_block_shell_frequency.trans uniform_frequency_iff_far_gap

theorem rh_iff_cofinal_shell_first_moment :
    RiemannHypothesis ↔ ∀ δ > (0:ℝ), cofinalMomentBound uniformShellScore δ :=
  (rh_iff_same_block_shell_frequency.trans uniform_weak_iff_first_moment).trans all_cofinal_moments_iff.symm

end RiemannReduction.ShortTail.LossFrequency
