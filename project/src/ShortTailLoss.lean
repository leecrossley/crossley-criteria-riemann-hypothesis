import ShortTailPrefix
import ThirdSignedPrime
import WholeTailPNT

/-! Removing the prefix preserves the cofinal negative-loss question. The
remaining unsigned terms still have quartic mass. The prime number theorem
gives genuine relative cancellation in the remaining signed sum. -/

noncomputable section
namespace RiemannReduction.ShortTail
open Finset Filter Real RiemannGaussian.AlpogeMined RiemannReduction.ThirdBridge
open RiemannReduction.DivisorBand RiemannReduction.DivisorBand.FourthMass

def half (n : ℕ) : ℝ := fixedBandHalfTail (n^4) (fixedBandMultipleCutoff n)
def core (n : ℕ) : ℝ := ∑ d ∈ late n, term n d
def coreAbs (n : ℕ) : ℝ := ∑ d ∈ late n, |term n d|
def loss (f : ℕ → ℝ) (m : ℕ) : ℝ := window (fun n => max (-(f n)) 0) m

theorem half_split (n : ℕ) : (∑ d ∈ early n, term n d) + core n = half n :=
  sum_filter_add_sum_filter_not (indices n) (· ≤ cutoff n) (term n)

theorem absolute_split (n : ℕ) : earlyAbs n + coreAbs n = fixedBandHalfTailAbsolute n :=
  sum_filter_add_sum_filter_not (indices n) (· ≤ cutoff n) (fun d => |term n d|)

theorem half_core_distance (n : ℕ) : |half n-core n| ≤ earlyAbs n := by
  rw [←half_split,add_sub_cancel_right]
  exact abs_sum_le_sum_abs _ _

private theorem remainder_half : ∃ B : ℝ, 0 ≤ B ∧ ∀ {n : ℕ}, 10^8 ≤ n →
    |remainder n-half n| ≤ B*(n:ℝ)^2 := by
  obtain ⟨C,hC,err⟩ := RiemannReduction.ThirdPrime.remainder_third
  refine ⟨C+12000,by positivity,fun {n} hn => ?_⟩
  have delta := sample_error (show 2 ≤ n by omega)
  rw [abs_sub_comm] at delta
  exact (abs_sub_le _ (thirdSample n) _).trans ((add_le_add (err hn) delta).trans_eq (by ring))

private theorem harmonic_exp {m : ℕ} :
    1+2*log m ≤ exp (10*sqrt (2*log m)) := by
  let u := sqrt (2*log m)
  have h := sq_sqrt (show 0 ≤ 2*log m by linarith [log_natCast_nonneg m])
  change u^2=_ at h
  have hu : 0 ≤ u := sqrt_nonneg _
  have hs := pow_le_pow_left₀ (by linarith : 0 ≤ u+1) (add_one_le_exp u) 2
  have h1 : 1+2*log m ≤ (exp u)^2 := by nlinarith only [hs,h,hu]
  apply h1.trans
  rw [pow_two,←exp_add]
  exact exp_le_exp.mpr (by change u+u ≤ 10*u; linarith)

theorem core_distance_subpower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, window (fun n => |remainder n-core n|) m ≤ (m:ℝ)^ε := by
  obtain ⟨B,B0,near⟩ := remainder_half
  filter_upwards [eventually_ge_atTop (10^8:ℕ),eventual_exp_sqrt (B+kernelConstant) 10 ε hε]
    with m hm small
  have each (n : ℕ) (hn : n ∈ Icc m (m^2)) :
      |remainder n-core n|/(n:ℝ)^3 ≤ B*(n:ℝ)⁻¹+earlyAbs n/(n:ℝ)^3 := by
    have lo := hm.trans (mem_Icc.mp hn).1
    have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
    have h := (abs_sub_le _ (half n) _).trans (add_le_add (near lo) (half_core_distance n))
    exact (div_le_div_of_nonneg_right h (by positivity : 0 ≤ (n:ℝ)^3)).trans_eq (by field_simp)
  calc
    _ ≤ ∑ n ∈ Icc m (m^2), (B*(n:ℝ)⁻¹+earlyAbs n/(n:ℝ)^3) := sum_le_sum each
    _ = B*(∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹)+window earlyAbs m := by rw [sum_add_distrib,←mul_sum]; rfl
    _ ≤ B*exp (10*sqrt (2*log m))+kernelConstant*exp (10*sqrt (2*log m)) :=
      add_le_add (mul_le_mul_of_nonneg_left ((harmonic_window (by omega)).trans harmonic_exp) B0)
        (early_window_bound (by omega))
    _ ≤ _ := by rwa [←add_mul]

theorem negative_loss_distance (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, |loss remainder m-loss core m| ≤ (m:ℝ)^ε := by
  filter_upwards [core_distance_subpower ε hε] with m limit
  unfold loss window
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum ?_).trans limit)
  intro n _
  rw [←sub_div,abs_div,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)^3)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (abs_max_sub_max_le_abs _ _ _).trans_eq (by rw [neg_sub_neg,abs_sub_comm])

def cofinalSubpower (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ m ≥ A, f m ≤ (m:ℝ)^ε

private theorem transfer {f g : ℕ → ℝ}
    (dist : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, |f m-g m| ≤ (m:ℝ)^ε)
    (h : cofinalSubpower f) : cofinalSubpower g := by
  intro ε ep A
  have ep' : 0 < ε/2 := by linarith
  have big := ((tendsto_rpow_atTop ep').comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 2
  obtain ⟨u,good⟩ := eventually_atTop.mp ((dist _ ep').and big)
  obtain ⟨m,large,pass⟩ := h _ ep' (max (max u 1) A)
  have start := (le_max_left _ A).trans large
  obtain ⟨err,r⟩ := good m ((le_max_left _ 1).trans start)
  change 2 ≤ (m:ℝ)^(ε/2) at r
  have mp : 0 < (m:ℝ) := Nat.cast_pos.mpr (by have := (le_max_right _ 1).trans start; omega)
  have add : (m:ℝ)^ε = ((m:ℝ)^(ε/2))*((m:ℝ)^(ε/2)) := by
    conv_lhs => rw [show ε = ε/2+ε/2 by ring]
    exact rpow_add mp _ _
  refine ⟨m,(le_max_right _ _).trans large,?_⟩
  rw [add]
  nlinarith only [(abs_le.mp err).1,pass,mul_le_mul_of_nonneg_right r (rpow_nonneg mp.le (ε/2))]

/-- The one-sided question can be asked of just the retained signed sum, with
the starting block allowed to depend on ε. -/
theorem negative_budget_iff_core :
    cofinalSubpower (mass (signedRemainder (-1))) ↔ cofinalSubpower (loss core) := by
  have same : mass (signedRemainder (-1)) = loss remainder := by
    funext m
    simp [mass,signedRemainder,loss,window]
  rw [same]
  exact ⟨transfer negative_loss_distance,transfer (fun ε hp => by
    simpa only [abs_sub_comm (loss core _) (loss remainder _)] using negative_loss_distance ε hp)⟩

/-- Summing absolute values before the inner Möbius sum necessarily exceeds
a fixed multiple of m^4, even after the enlarged prefix has been removed. -/
theorem core_absolute_lower :
    ∀ᶠ m : ℕ in atTop, (m:ℝ)^4/16000 ≤ window coreAbs m := by
  filter_upwards [eventually_ge_atTop (16000:ℕ),early_window_subpower 1 zero_lt_one] with m hm small
  rw [rpow_one] at small
  have full := fixedBandHalfTailAbsolute_window_lower (show 32 ≤ m by omega)
  have split : window earlyAbs m+window coreAbs m=window fixedBandHalfTailAbsolute m := by
    unfold window
    rw [←sum_add_distrib]
    exact sum_congr rfl fun n _ => by rw [←add_div, absolute_split]
  have h3 : (16000:ℝ) ≤ (m:ℝ)^3 := by
    exact_mod_cast hm.trans (Nat.le_self_pow (by decide : 3 ≠ 0) m)
  change (m:ℝ)^4/8000 ≤ window fixedBandHalfTailAbsolute m at full
  nlinarith only [split,full,small,mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg (α:=ℝ) m)]

private theorem sum_indices {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ Icc m (m^2), (n:ℝ) ≤ (m:ℝ)^4 := by
  have size : ((Icc m (m^2)).card:ℝ) ≤ (m:ℝ)^2 := by
    exact_mod_cast (show (Icc m (m^2)).card ≤ m^2 by rw [Nat.card_Icc]; omega)
  calc
    _ ≤ ∑ _n ∈ Icc m (m^2), (m:ℝ)^2 :=
      sum_le_sum fun n hn => by exact_mod_cast (mem_Icc.mp hn).2
    _ = ((Icc m (m^2)).card:ℝ)*(m:ℝ)^2 := by simp
    _ ≤ (m:ℝ)^2*(m:ℝ)^2 := mul_le_mul_of_nonneg_right size (sq_nonneg _)
    _ = _ := by ring

/-- The prime number theorem saves an exp(-b sqrt(2 log m)) factor on the
remaining range, with the absolute value taken inside the sample window
but after each signed sum over d. -/
theorem core_cancellation :
    ∃ b > (0:ℝ), ∃ C > (0:ℝ), ∀ᶠ m : ℕ in atTop,
      window (fun n => |core n|) m ≤ C*(m:ℝ)^4*exp (-b*sqrt (2*log m)) := by
  obtain ⟨b,bp,M,Mp,up⟩ := whole_tail_pnt
  refine ⟨b,bp,M+1,by linarith,?_⟩
  filter_upwards [eventually_ge_atTop (108:ℕ),core_distance_subpower 1 zero_lt_one,
    eventual_exp_sqrt 1 b 1 zero_lt_one] with m hm error growing
  rw [rpow_one] at error
  rw [one_mul,rpow_one] at growing
  have mp : 0 < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  let E := exp (-b*sqrt (2*log m))
  have Ep : 0 < E := exp_pos _
  have budget : window (fun n => |remainder n|) m ≤ (M*E)*(m:ℝ)^4 := by
    have each (n : ℕ) (hn : n ∈ Icc m (m^2)) : |remainder n|/(n:ℝ)^3 ≤ (M*E)*n := by
      have mn := (mem_Icc.mp hn).1
      have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
      have est := (up (n^2) (Nat.pow_le_pow_left (hm.trans mn) 2)).2.2
      change |remainder n| ≤ M*((n^2:ℕ):ℝ)^2 * exp (-b*sqrt (log ((n^2:ℕ):ℝ))) at est
      rw [Nat.cast_pow,log_pow,Nat.cast_ofNat] at est
      have lg := log_le_log mp (Nat.cast_le (α:=ℝ).mpr mn)
      have root := sqrt_le_sqrt (mul_le_mul_of_nonneg_left lg (by norm_num : (0:ℝ)≤2))
      have fall : exp (-b*sqrt (2*log n)) ≤ E :=
        exp_le_exp.mpr (mul_le_mul_of_nonpos_left root (neg_nonpos.mpr bp.le))
      apply (div_le_iff₀ (pow_pos np 3)).mpr
      exact est.trans ((mul_le_mul_of_nonneg_left fall (by positivity : 0 ≤ M*((n:ℝ)^2)^2)).trans_eq (by ring))
    apply (sum_le_sum each).trans
    rw [←mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_indices (by omega)) (mul_nonneg Mp.le Ep.le)
  have covered : (m:ℝ) ≤ (m:ℝ)^4*E := by
    dsimp [E]
    rw [neg_mul,exp_neg,←div_eq_mul_inv,le_div_iff₀ (exp_pos _)]
    have hpow : (m:ℝ)^2 ≤ (m:ℝ)^4 := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < m) (by decide : 2 ≤ 4)
    exact (mul_le_mul_of_nonneg_left growing mp.le).trans (by simpa [pow_two] using hpow)
  have join : window (fun n => |core n|) m ≤
      window (fun n => |remainder n|) m+window (fun n => |remainder n-core n|) m := by
    unfold window
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro n _
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h := abs_sub_le (core n) (remainder n) 0
    simpa only [sub_zero,abs_sub_comm (core n) (remainder n),add_comm] using h
  apply join.trans
  exact (add_le_add budget (error.trans covered)).trans_eq (by dsimp [E]; ring)

/-- Signed cancellation consumes an arbitrarily large fraction of the
absolute term mass on every sufficiently late full window. -/
theorem core_relative_cancellation (η : ℝ) (hp : 0 < η) :
    ∀ᶠ m : ℕ in atTop, window (fun n => |core n|) m ≤ η * window coreAbs m := by
  obtain ⟨b,bp,C,Cp,est⟩ := core_cancellation
  have grow := tendsto_sqrt_atTop.comp (Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<2)
    (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))))
  have vanish := tendsto_exp_atBot.comp (grow.const_mul_atTop_of_neg (neg_lt_zero.mpr bp))
  filter_upwards [est,core_absolute_lower,vanish.eventually_lt_const (show 0 < η/(16000*C) by positivity)]
    with m cap raw tiny
  change exp (-b*sqrt (2*log m)) < η/(16000*C) at tiny
  have h := (lt_div_iff₀ (show 0 < 16000*C by positivity)).mp tiny
  have coeff : C*exp (-b*sqrt (2*log m)) ≤ η/16000 := by linarith
  calc
    _ ≤ C*(m:ℝ)^4*exp (-b*sqrt (2*log m)) := cap
    _ = (C*exp (-b*sqrt (2*log m)))*(m:ℝ)^4 := by ring
    _ ≤ (η/16000)*(m:ℝ)^4 := mul_le_mul_of_nonneg_right coeff (by positivity)
    _ = η*((m:ℝ)^4/16000) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left raw hp.le

def positiveTerms (n : ℕ) : ℝ := ∑ d ∈ late n, max (term n d) 0
def negativeTerms (n : ℕ) : ℝ := ∑ d ∈ late n, max (-(term n d)) 0

private theorem signs (n : ℕ) :
    positiveTerms n+negativeTerms n=coreAbs n ∧ positiveTerms n-negativeTerms n=core n := by
  unfold positiveTerms negativeTerms coreAbs core
  rw [←sum_add_distrib,←sum_sub_distrib]
  constructor <;> apply sum_congr rfl <;> intro d _
  all_goals
    rcases le_total 0 (term n d) with pos|neg
    · simp [max_eq_left pos,max_eq_right (neg_nonpos.mpr pos),abs_of_nonneg pos]
    · simp [max_eq_right neg,max_eq_left (neg_nonneg.mpr neg),abs_of_nonpos neg]

/-- The loss pairs opposite signs only within the same fourth-power sample. -/
theorem loss_eq_unmatched (m : ℕ) :
    loss core m = window (fun n => negativeTerms n-min (positiveTerms n) (negativeTerms n)) m := by
  unfold loss window
  apply sum_congr rfl
  intro n _
  have sig := (signs n).2
  change max (-(core n)) 0/(n:ℝ)^3 = (negativeTerms n-min (positiveTerms n) (negativeTerms n))/(n:ℝ)^3
  rcases le_total (positiveTerms n) (negativeTerms n) with h|h
  · rw [min_eq_left h,max_eq_left (by linarith)]
    congr 1
    linarith
  · rw [min_eq_right h,max_eq_right (by linarith),sub_self]

/-- Even the negative terms by themselves, and the positive terms by
themselves, have quartic weight on every sufficiently late window. -/
theorem both_term_masses_lower :
    ∀ᶠ m : ℕ in atTop, (m:ℝ)^4/64000 ≤ window positiveTerms m ∧
      (m:ℝ)^4/64000 ≤ window negativeTerms m := by
  filter_upwards [core_absolute_lower,core_relative_cancellation (1/2) (by norm_num)] with m raw cancel
  have lift (f : ℕ → ℝ) (h : ∀ n, coreAbs n ≤ 2*f n+|core n|) :
      window coreAbs m ≤ 2*window f m+window (fun n => |core n|) m := by
    unfold window
    rw [mul_sum,←sum_add_distrib]
    apply sum_le_sum
    intro n _
    rw [←mul_div_assoc,←add_div]
    exact div_le_div_of_nonneg_right (h n) (by positivity)
  have pos := lift positiveTerms (fun n => by
    obtain ⟨a,b⟩ := signs n
    linarith only [a,b,neg_abs_le (core n)])
  have neg := lift negativeTerms (fun n => by
    obtain ⟨a,b⟩ := signs n
    linarith only [a,b,le_abs_self (core n)])
  constructor <;> linarith only [raw,cancel,pos,neg]

/-- Even passing to a sparse cofinal sequence cannot make the PNT
majorant itself small enough for a fixed exponent below four. -/
theorem pnt_majorant_exceeds (b C ε : ℝ) (hC : 0 < C) (hε : ε < 4) :
    ∀ᶠ m : ℕ in atTop, (m:ℝ)^ε < C*(m:ℝ)^4*exp (-b*sqrt (2*log m)) := by
  filter_upwards [eventual_exp_sqrt (2/C) b (4-ε) (sub_pos.mpr hε),
    eventually_ge_atTop (1:ℕ)] with m scale hm
  have mp : 0 < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  let u := sqrt (2*log m)
  change 2/C*exp (b*u) ≤ (m:ℝ)^(4-ε) at scale
  have fourth : (m:ℝ)^(4-ε)*(m:ℝ)^ε=(m:ℝ)^4 := by
    rw [←rpow_add mp,sub_add_cancel]
    norm_cast
  have lifted := mul_le_mul_of_nonneg_right scale (rpow_pos_of_pos mp ε).le
  rw [fourth] at lifted
  have strict : (m:ℝ)^ε*exp (b*u) < C*(m:ℝ)^4 := by
    have a := mul_le_mul_of_nonneg_left lifted hC.le
    have canon : C*(2/C*exp (b*u)*(m:ℝ)^ε) = 2*((m:ℝ)^ε*exp (b*u)) := by field_simp
    rw [canon] at a
    linarith only [a,mul_pos (rpow_pos_of_pos mp ε) (exp_pos (b*u))]
  change (m:ℝ)^ε < C*(m:ℝ)^4 * exp (-b*u)
  rw [neg_mul,exp_neg,←div_eq_mul_inv]
  exact (lt_div_iff₀ (exp_pos _)).mpr strict

end RiemannReduction.ShortTail
