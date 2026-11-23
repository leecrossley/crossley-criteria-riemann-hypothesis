import MobiusSignPairs

/-! Complete square windows. Deleting both matched entries discards a
quartic surplus. Keeping it gives the exact remaining one-sided question. -/

noncomputable section
namespace RiemannReduction.ShortTail.SignPairs
open Finset Filter Real RiemannReduction.DivisorBand.FourthMass

private theorem sum_lower {m : ℕ} (hm : 2 ≤ m) :
    (m:ℝ)^4/4 ≤ ∑ n ∈ Icc m (m^2), (n:ℝ) := by
  let M := m^2
  have hmM : m ≤ M/2 := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    ((Nat.mul_le_mul_left m hm).trans_eq (by simp [M,pow_two]))
  have card : (M:ℝ)/2 ≤ ((Ioc (M/2) M).card:ℝ) := by
    rw [Nat.card_Ioc]
    have c : (M:ℝ) ≤ 2*((M-M/2:ℕ):ℝ) := by exact_mod_cast (show M ≤ 2*(M-M/2) by omega)
    linarith
  have sub : Ioc (M/2) M ⊆ Icc m M := fun n hn =>
    mem_Icc.mpr ⟨hmM.trans (mem_Ioc.mp hn).1.le,(mem_Ioc.mp hn).2⟩
  calc
    (m:ℝ)^4/4 = (M:ℝ)/2*((M:ℝ)/2) := by dsimp [M]; push_cast; ring
    _ ≤ ((Ioc (M/2) M).card:ℝ)*((M:ℝ)/2) := mul_le_mul_of_nonneg_right card (by positivity)
    _ = ∑ _n ∈ Ioc (M/2) M, (M:ℝ)/2 := by simp
    _ ≤ ∑ n ∈ Ioc (M/2) M, (n:ℝ) := by
      apply sum_le_sum
      intro n hn
      have h := (mem_Ioc.mp hn).1
      have c : (M:ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast (show M ≤ 2*n by omega)
      linarith
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun n _ _ => Nat.cast_nonneg n)

private theorem lower_window {m : ℕ} (hm : 100000 ≤ m) (f : ℕ → ℝ) {C : ℝ} (hp : 0 < C)
    (h : ∀ {n : ℕ}, 100000 ≤ n → (n:ℝ)^4/C ≤ f n) :
    (m:ℝ)^4/(4*C) ≤ window f m := by
  calc
    (m:ℝ)^4/(4*C) = ((m:ℝ)^4/4)/C := by ring
    _ ≤ (∑ n ∈ Icc m (m^2), (n:ℝ))/C := div_le_div_of_nonneg_right (sum_lower (by omega)) hp.le
    _ = ∑ n ∈ Icc m (m^2), (n:ℝ)/C := sum_div ..
    _ ≤ _ := by
      apply sum_le_sum
      intro n hn
      have late := hm.trans (mem_Icc.mp hn).1
      have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
      apply (le_div_iff₀ (pow_pos np 3)).mpr
      exact (show (n:ℝ)/C*(n:ℝ)^3=(n:ℝ)^4/C by ring).le.trans (h late)

theorem paired_windows {m : ℕ} (hm : 100000 ≤ m) :
    loss credit m=0 ∧ (m:ℝ)^4/80000000 ≤ window paid m ∧
      (m:ℝ)^4/6400000000 ≤ window credit m := by
  refine ⟨?_,?_,?_⟩
  · unfold loss window
    apply sum_eq_zero
    intro n hn
    have h := (covered_weight (hm.trans (mem_Icc.mp hn).1)).2
    have p : 0 ≤ credit n := (by positivity : 0 ≤ (n:ℝ)^4/1600000000).trans h
    simp [max_eq_right (neg_nonpos.mpr p)]
  · convert lower_window hm paid (C:=20000000) (by norm_num) (fun h => (covered_weight h).1) using 1
    norm_num
  · convert lower_window hm credit (C:=1600000000) (by norm_num) (fun h => (covered_weight h).2) using 1
    norm_num

private theorem small_total (η : ℝ) (hp : 0 < η) :
    ∀ᶠ m : ℕ in atTop, window (fun n => |core n|) m ≤ η*(m:ℝ)^4 := by
  obtain ⟨b,bp,C,Cp,est⟩ := core_cancellation
  have grow := tendsto_sqrt_atTop.comp (Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<2)
    (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))))
  have vanish := tendsto_exp_atBot.comp (grow.const_mul_atTop_of_neg (neg_lt_zero.mpr bp))
  filter_upwards [est,vanish.eventually_lt_const (div_pos hp Cp)] with m cap tiny
  change exp (-b*sqrt (2*log m)) < η/C at tiny
  have h := (lt_div_iff₀ Cp).mp tiny
  have coeff : C*exp (-b*sqrt (2*log m)) ≤ η := by linarith
  exact cap.trans (by
    calc _ = (C*exp (-b*sqrt (2*log m)))*(m:ℝ)^4 := by ring
         _ ≤ η*(m:ℝ)^4 := mul_le_mul_of_nonneg_right coeff (by positivity))

private theorem all_samples_late :
    ∀ᶠ m : ℕ in atTop, ∀ n ∈ Icc m (m^2), core n = credit n+rest n := by
  filter_upwards [eventually_ge_atTop (100000:ℕ)] with m hm
  intro n hn
  have large := hm.trans (mem_Icc.mp hn).1
  exact decompose large

/-- The actual unused indices alone have quartic negative loss on every
sufficiently late block. The surplus from the selected pairs is essential. -/
theorem unused_loss_lower :
    ∀ᶠ m : ℕ in atTop, (m:ℝ)^4/12800000000 ≤ loss rest m := by
  filter_upwards [all_samples_late,small_total (1/12800000000) (by norm_num),
    eventually_ge_atTop (100000:ℕ)] with m split small hm
  have lower : window credit m-window (fun n => |core n|) m ≤ loss rest m := by
    unfold window loss
    rw [←sum_sub_distrib]
    apply sum_le_sum
    intro n hn
    rw [←sub_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (show credit n-|core n| ≤ -(rest n) by linarith only [split n hn,le_abs_self (core n)]).trans (le_max_left _ _)
  linarith only [lower,small,(paired_windows hm).2.2]

/-- The explicit surplus and the loss of the unused indices agree in
relative size on every sufficiently late window, measured sample by sample. -/
theorem relative_payment (η : ℝ) (hp : 0 < η) :
    ∀ᶠ m : ℕ in atTop, window (fun n => |max (-rest n) 0-credit n|) m ≤ η*window credit m := by
  filter_upwards [all_samples_late,small_total (η/6400000000) (by positivity),
    eventually_ge_atTop (100000:ℕ)] with m split small hm
  have each (n : ℕ) (hn : n ∈ Icc m (m^2)) : |max (-rest n) 0-credit n| ≤ |core n| := by
    have c := (covered_weight (hm.trans (mem_Icc.mp hn).1)).2
    have pos : 0 ≤ credit n := (by positivity : 0 ≤ (n:ℝ)^4/1600000000).trans c
    calc _ = |max (-rest n) 0-max (credit n) 0| := by rw [max_eq_left pos]
         _ ≤ |(-rest n)-credit n| := abs_max_sub_max_le_abs _ _ _
         _ = |core n| := by rw [split n hn,show -rest n-credit n= -(credit n+rest n) by ring,abs_neg]
  calc
    _ ≤ window (fun n => |core n|) m := sum_le_sum fun n h =>
      div_le_div_of_nonneg_right (each n h) (by positivity)
    _ ≤ (η/6400000000)*(m:ℝ)^4 := small
    _ = η*((m:ℝ)^4/6400000000) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (paired_windows hm).2.2 hp.le

theorem unused_loss_exceeds (ε : ℝ) (he : ε < 4) :
    ∀ᶠ m : ℕ in atTop, (m:ℝ)^ε < loss rest m := by
  have grow := ((tendsto_rpow_atTop (sub_pos.mpr he)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_gt_atTop 12800000000
  filter_upwards [unused_loss_lower,grow,eventually_ge_atTop (1:ℕ)] with m lower big one
  change 12800000000 < (m:ℝ)^(4-ε) at big
  have mp : 0 < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  have eqn : (m:ℝ)^(4-ε)*(m:ℝ)^ε=(m:ℝ)^4 := by rw [←rpow_add mp,sub_add_cancel]; norm_cast
  have h := mul_lt_mul_of_pos_right big (rpow_pos_of_pos mp ε)
  rw [eqn] at h
  linarith only [lower,h]

def outstanding (m : ℕ) := window (fun n => max (-rest n-credit n) 0) m

/-- The surplus can pay other entries at its own sample. This equality
retains its full value, including any excess over the first negative partner. -/
theorem loss_with_credit : ∀ᶠ m : ℕ in atTop, loss core m = outstanding m := by
  filter_upwards [all_samples_late] with m split
  unfold loss outstanding window
  apply sum_congr rfl
  intro n hn
  have h : -core n = -rest n-credit n := by rw [split n hn]; ring
  simp only [h]

theorem original_iff_outstanding :
    cofinalSubpower (mass (signedRemainder (-1))) ↔ cofinalSubpower outstanding := by
  apply negative_budget_iff_core.trans
  obtain ⟨u,eqn⟩ := eventually_atTop.mp loss_with_credit
  constructor <;> intro h ε ep A <;>
    obtain ⟨m,large,hp⟩ := h ε ep (max u A) <;>
    refine ⟨m,(le_max_right _ _).trans large,?_⟩
  · rwa [←eqn m ((le_max_left _ _).trans large)]
  · rwa [eqn m ((le_max_left _ _).trans large)]

end RiemannReduction.ShortTail.SignPairs
