import FirstShallowShells

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real

/-- The same test is used for every exponent: any complete positive-index
dyadic shell crosses its full negative band share. -/
def uniformFirstShellEvent (n : ℕ) (t : ℝ) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ fullFirstShell n j < -share n 0 t

/-- The complementary large quotients, paid by absolute kernel decay. -/
def highFirstShellEvent (δ : ℝ) (n : ℕ) (t : ℝ) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ (n:ℝ)^(1-3*δ/16) ≤ (2:ℝ)^j ∧ fullFirstShell n j < -share n 0 t

private theorem shell_crossing_rank {n j : ℕ} {t : ℝ} (tp : 0 ≤ t)
    (bad : fullFirstShell n j < -share n 0 t) : j < bandCount n 0 := by
  by_contra! off
  have exceed : n^4 < (2:ℕ)^j := by
    by_contra! small
    have index := Nat.le_log_of_pow_le (by decide : 1<2) small
    have on : j < bandCount n 0 := by simpa [bandCount] using Nat.lt_succ_of_le index
    omega
  have empty : fullFirstShell n j=0 := by simp [fullFirstShell,Nat.div_eq_of_lt exceed]
  have nonneg : 0 ≤ share n 0 t := by unfold share; positivity
  linarith only [empty,bad,nonneg]

private theorem raw_shell_ceiling {n j : ℕ} {t : ℝ} (hn : 1 ≤ n) (jp : 1 ≤ j)
    (tp : 0 < t) (bad : fullFirstShell n j < -share n 0 t) :
    t*(2:ℝ)^(2*j) ≤ (4*kernelConstant)*(1+8*log n)^3*(n:ℝ)^2 := by
  have np := Nat.cast_pos (α:=ℝ).mpr hn
  have bp : 0 < (bandCount n 0:ℝ) := by unfold bandCount; positivity
  have two : 2 ≤ (2:ℕ)^j := by
    calc (2:ℕ) = 2^1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right (by decide) jp
  have cap : bandHi n j=n^4/2^j := min_eq_right (Nat.div_le_div_left two (by decide))
  have size := halved_net_size n j 0 (n^4/2^(j+1))
  simp only [zero_add,halvedNet,intervalNet,cap,pow_zero,Nat.div_one,div_one] at size
  change |fullFirstShell n j| * (2:ℝ)^(2*j) ≤ _ at size
  have value : share n 0 t ≤ |fullFirstShell n j| := by
    linarith only [bad,neg_le_abs (fullFirstShell n j)]
  have scale : share n 0 t*(4*(bandCount n 0:ℝ))=t*(n:ℝ)^2 := by
    unfold share
    field_simp
    ring
  have rank : j ≤ Nat.log 2 (n^4) := by simpa [bandCount] using shell_crossing_rank tp.le bad
  have limit : (2:ℕ)^j ≤ n^4 := (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) rank).trans
    (Nat.pow_log_le_self 2 (by positivity))
  have lq := log_le_log (by positivity : 0<(2:ℝ)^j) (show (2:ℝ)^j ≤ (n:ℝ)^4 by exact_mod_cast limit)
  rw [log_pow (n:ℝ) 4,Nat.cast_ofNat] at lq
  have ln := log_natCast_nonneg n
  let L := 1+8*log n
  have l1 : 1 ≤ L := by dsimp [L]; linarith only [ln]
  have qbound : 1+log ((2:ℝ)^j) ≤ L := by dsimp [L]; linarith only [ln,lq]
  have pair := mul_le_mul qbound (band_count_log hn) bp.le (by linarith only [l1] : 0≤L)
  have cube : L*L ≤ L^3 := by nlinarith only [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr l1)]
  have factor := mul_le_mul_of_nonneg_left (pair.trans cube) (show 0 ≤ 4*kernelConstant by positivity [kernelConstant_nonneg])
  have term := mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right value (by positivity : 0≤(2:ℝ)^(2*j))).trans size)
    (show 0≤4*(bandCount n 0:ℝ) by positivity)
  have left : (share n 0 t*(2:ℝ)^(2*j))*(4*(bandCount n 0:ℝ)) =
      (t*(2:ℝ)^(2*j))*(n:ℝ)^2 := by
    calc _ = (share n 0 t*(4*(bandCount n 0:ℝ)))*(2:ℝ)^(2*j) := by ring
         _ = _ := by rw [scale]; ring
  rw [left] at term
  have scaleCap := mul_le_mul_of_nonneg_right factor (pow_nonneg np.le 4)
  apply le_of_mul_le_mul_right _ (pow_pos np 2)
  dsimp [L] at scaleCap
  linarith only [term,scaleCap]

private theorem high_shell_height {δ : ℝ} {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (tp : 0 < t)
    (hit : highFirstShellEvent δ n t) :
    t ≤ (4*kernelConstant)*(1+8*log n)^3*(n:ℝ)^(3*δ/8) := by
  obtain ⟨j,jp,high,cross⟩ := hit
  have square : (n:ℝ)^(2-3*δ/8) ≤ (2:ℝ)^(2*j) :=
    le_of_not_gt fun shallow => (not_lt_of_ge high) ((first_shell_quotient_iff n j δ).mp shallow)
  have np := Nat.cast_pos (α:=ℝ).mpr hn
  have paid := (mul_le_mul_of_nonneg_left square tp.le).trans (raw_shell_ceiling hn jp tp cross)
  have scaled := mul_le_mul_of_nonneg_right paid (rpow_nonneg np.le (3*δ/8))
  have powers : (n:ℝ)^(2-3*δ/8)*(n:ℝ)^(3*δ/8)=(n:ℝ)^2 := by rw [←rpow_add np,sub_add_cancel,rpow_two]
  rw [mul_assoc t,powers] at scaled
  apply le_of_mul_le_mul_right _ (pow_pos np 2)
  linarith only [scaled]

/-- Complete shells above the old exponent-dependent quotient boundary
satisfy the frequency estimate on every sufficiently late block. -/
theorem uniform_high_shell_subpower {δ : ℝ} (ep : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0 < t → t*eventMass (highFirstShellEvent δ) m t ≤ (m:ℝ)^δ :=
  event_subpower_from_height (α:=3*δ/8) (by positivity)
    (show 0 ≤ 4*kernelConstant by positivity [kernelConstant_nonneg]) (by linarith)
    (fun _ hn _ tp hit => high_shell_height hn tp hit)

private theorem shell_mass_split (δ : ℝ) (m : ℕ) (t : ℝ) :
    eventMass (fullFirstShellEvent δ) m t ≤ eventMass uniformFirstShellEvent m t ∧
    eventMass uniformFirstShellEvent m t ≤ eventMass (fullFirstShellEvent δ) m t +
      eventMass (highFirstShellEvent δ) m t := by
  classical
  constructor
  · unfold eventMass
    apply sum_le_sum
    intro n _
    by_cases hit : fullFirstShellEvent δ n t
    · have all : uniformFirstShellEvent n t := by obtain ⟨j,jp,_,cross⟩ := hit; exact ⟨j,jp,cross⟩
      simp [hit,all]
    · simp only [if_neg hit]
      split <;> positivity
  · unfold eventMass
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro n _
    by_cases hit : uniformFirstShellEvent n t
    · rw [if_pos hit]
      obtain ⟨j,jp,cross⟩ := hit
      by_cases low : (2:ℝ)^j < (n:ℝ)^(1-3*δ/16)
      · have part : fullFirstShellEvent δ n t := ⟨j,jp,low,cross⟩
        rw [if_pos part]
        split <;> simp
      · have part : highFirstShellEvent δ n t := ⟨j,jp,le_of_not_gt low,cross⟩
        rw [if_pos part]
        split <;> simp
    · rw [if_neg hit]
      split_ifs <;> positivity

/-- Removing the exponent-dependent shell cutoff leaves the same
common-block weak bound for every positive δ. -/
theorem full_shell_shared_iff_uniform {δ : ℝ} (ep : 0 < δ) :
    sharedEventBound (fullFirstShellEvent δ) δ ↔ sharedEventBound uniformFirstShellEvent δ := by
  constructor
  · rintro ⟨C,cp,blocks⟩
    obtain ⟨N,high⟩ := eventually_atTop.mp (uniform_high_shell_subpower ep)
    refine ⟨C+1,by linarith,fun A => ?_⟩
    obtain ⟨m,hm,all⟩ := blocks (max A N)
    refine ⟨m,(le_max_left ..).trans hm,fun j => ?_⟩
    have tp : 0 < (2:ℝ)^j := by positivity
    have covered := mul_le_mul_of_nonneg_left (shell_mass_split δ m ((2:ℝ)^j)).2 tp.le
    have paid := high m ((le_max_right ..).trans hm) _ tp
    linarith only [covered,paid,all j]
  · rintro ⟨C,cp,blocks⟩
    refine ⟨C,cp,fun A => ?_⟩
    obtain ⟨m,hm,all⟩ := blocks A
    exact ⟨m,hm,fun j => (mul_le_mul_of_nonneg_left (shell_mass_split δ m ((2:ℝ)^j)).1
      (by positivity)).trans (all j)⟩

theorem rh_of_uniform_first_shells
    (h : ∀ δ > (0:ℝ), sharedEventBound uniformFirstShellEvent δ) : RiemannHypothesis :=
  rh_of_full_first_shells fun δ ep => (full_shell_shared_iff_uniform ep).mpr (h δ ep)

/-- A single classical statistic independent of the block, exponent and
threshold. The quotient bin j=0 contributes zero, so the finite maximum is nonnegative. -/
def uniformShellScore (n : ℕ) : ℝ :=
  (range (bandCount n 0)).sup' (nonempty_range_iff.mpr (by unfold bandCount; omega))
    (fun j => -fullFirstShell n j/share n 0 1)

theorem uniform_shell_score_nonnegative (n : ℕ) : 0 ≤ uniformShellScore n := by
  have zero : 0 ∈ range (bandCount n 0) := mem_range.mpr (by unfold bandCount; omega)
  have h := le_sup' (fun j => -fullFirstShell n j/share n 0 1) zero
  simpa only [full_first_zero_bin,neg_zero,zero_div,uniformShellScore] using h

theorem uniform_event_iff_score {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (tp : 0<t) :
    uniformFirstShellEvent n t ↔ t < uniformShellScore n := by
  have np := Nat.cast_pos (α:=ℝ).mpr hn
  have bp : 0 < (bandCount n 0:ℝ) := by unfold bandCount; positivity
  have one : 0 < share n 0 1 := by unfold share; positivity
  have scale : share n 0 t=t*share n 0 1 := by unfold share; ring
  rw [uniformShellScore,lt_sup'_iff]
  constructor
  · rintro ⟨j,_,cross⟩
    refine ⟨j,mem_range.mpr (shell_crossing_rank tp.le cross),(lt_div_iff₀ one).mpr ?_⟩
    linarith only [cross,scale]
  · rintro ⟨j,_,cross⟩
    have bad : fullFirstShell n j < -share n 0 t := by
      linarith only [(lt_div_iff₀ one).mp cross,scale]
    have jp : 1 ≤ j := by
      by_contra! off
      have z : j=0 := by omega
      rw [z,full_first_zero_bin] at bad
      have nonnegative : 0 ≤ share n 0 t := by unfold share; positivity
      linarith only [bad,nonnegative]
    exact ⟨j,jp,bad⟩

theorem uniform_shell_score_frequency {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (tp : 0<t) :
    eventMass uniformFirstShellEvent m t=frequency uniformShellScore m t := by
  classical
  unfold eventMass frequency
  apply sum_congr rfl
  intro n hn
  rw [uniform_event_iff_score (hm.trans (mem_Icc.mp hn).1) tp]

/-- The fixed scalar and fixed event have identical cofinal weak bounds. -/
theorem uniform_score_same_block_iff :
    sameBlockWeak uniformShellScore ↔ ∀ δ > (0:ℝ), sharedEventBound uniformFirstShellEvent δ := by
  constructor <;> intro h δ ep <;> obtain ⟨C,cp,blocks⟩ := h δ ep <;>
    refine ⟨C,cp,fun A => ?_⟩
  · obtain ⟨m,hm,all⟩ := blocks (max A 1)
    exact ⟨m,(le_max_left ..).trans hm,fun j => by
      rw [uniform_shell_score_frequency ((le_max_right ..).trans hm) (by positivity)]
      exact all j⟩
  · obtain ⟨m,hm,all⟩ := blocks (max A 1)
    exact ⟨m,(le_max_left ..).trans hm,fun j => by
      rw [←uniform_shell_score_frequency ((le_max_right ..).trans hm) (by positivity)]
      exact all j⟩

theorem rh_of_uniform_shell_score (h : sameBlockWeak uniformShellScore) : RiemannHypothesis :=
  rh_of_uniform_first_shells (uniform_score_same_block_iff.mp h)

end RiemannReduction.ShortTail.LossFrequency
