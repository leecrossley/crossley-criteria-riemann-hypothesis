import CheckAlpogeFixedPrimeBandFirstQuotient

/-! An unconditional subpower estimate for a growing initial segment of
Sanftenberg's actual half-length linear Möbius sum, on complete square windows. -/

noncomputable section
namespace RiemannReduction.ShortTail
open Finset Filter Real RiemannGaussian.AlpogeMined
open scoped ArithmeticFunction.Moebius

def cutoff (n : ℕ) : ℕ := ⌊(n:ℝ)^3 * exp (sqrt (log n))⌋₊

def indices (n : ℕ) := Ioc (fixedBandMultipleCutoff n) (n^4/2)
def early (n : ℕ) := (indices n).filter (· ≤ cutoff n)
def late (n : ℕ) := (indices n).filter (fun d => ¬ d ≤ cutoff n)

def term (n d : ℕ) : ℝ :=
  (μ d:ℝ) * (fixedBandCenteredKernel (((n^4:ℕ):ℝ)/d) -
    fixedBandFirstCorrection (((n^4:ℕ):ℝ)/d))

def earlyAbs (n : ℕ) : ℝ := ∑ d ∈ early n, |term n d|
def window (f : ℕ → ℝ) (m : ℕ) : ℝ := ∑ n ∈ Icc m (m^2), f n/(n:ℝ)^3

def kernelConstant : ℝ := 1572 + 60 * |fixedBandLogConstant|

theorem kernelConstant_nonneg : 0 ≤ kernelConstant := by unfold kernelConstant; positivity

private theorem term_bound {n d : ℕ} (hn : 2 ≤ n) (hd : d ∈ indices n) :
    |term n d| ≤ kernelConstant * (1+log ((n^4:ℕ):ℝ))/((n^4:ℕ):ℝ)*d := by
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hd
  have dp : 0 < (d:ℝ) := Nat.cast_pos.mpr (by omega)
  have d1 : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have np : 0 < ((n^4:ℕ):ℝ) := Nat.cast_pos.mpr (pow_pos (by omega) _)
  let y := ((n^4:ℕ):ℝ)/d
  have yp : 0 < y := div_pos np dp
  have y2 : 2 ≤ y := (le_div_iff₀ dp).mpr (by exact_mod_cast (show 2*d ≤ n^4 by omega))
  have ly : 0 ≤ log y := log_nonneg (by linarith)
  have lN := log_le_log yp (div_le_self np.le d1)
  have base : 0 ≤ 72+60*|fixedBandLogConstant| := by positivity
  have hμ : |(μ d:ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  change |(μ d:ℝ)*(fixedBandCenteredKernel y-fixedBandFirstCorrection y)| ≤ _
  rw [abs_mul]
  calc
    _ ≤ |fixedBandCenteredKernel y-fixedBandFirstCorrection y| :=
      mul_le_of_le_one_left (abs_nonneg _) hμ
    _ ≤ |fixedBandCenteredKernel y|+|fixedBandFirstCorrection y| := abs_sub _ _
    _ ≤ (72+60*|fixedBandLogConstant|)*(1+log y)/y+1500/y :=
      add_le_add (fixedBandCenteredKernel_bound y2) (fixedBandFirstCorrection_decay yp)
    _ ≤ kernelConstant*(1+log ((n^4:ℕ):ℝ))/y := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ yp.le
      have inc := mul_le_mul_of_nonneg_left (add_le_add_left lN 1) base
      unfold kernelConstant
      nlinarith only [inc,ly,lN]
    _ = _ := by dsimp [y]; field_simp

theorem early_abs_bound {n : ℕ} (hn : 2 ≤ n) :
    earlyAbs n ≤ (n:ℝ)^2 * (kernelConstant*(1+4*log n)*exp (2*sqrt (log n))) := by
  let a := kernelConstant*(1+log ((n^4:ℕ):ℝ))/((n^4:ℕ):ℝ)
  have a0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (mul_nonneg kernelConstant_nonneg (by linarith [log_natCast_nonneg (n^4)])) (by positivity)
  have subs : early n ⊆ Ioc 0 (cutoff n) := by
    intro d hd
    obtain ⟨hd,small⟩ := mem_filter.mp hd
    exact mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hd).1,small⟩
  have size : ((early n).card:ℝ) ≤ cutoff n := by
    exact_mod_cast (show (early n).card ≤ cutoff n by simpa using card_le_card subs)
  have bound := Nat.floor_le (show 0 ≤ (n:ℝ)^3*exp (sqrt (log n)) by positivity)
  change (cutoff n:ℝ) ≤ _ at bound
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  calc
    _ ≤ ∑ _d ∈ early n, a*(cutoff n:ℝ) := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hmem,small⟩ := mem_filter.mp hd
      exact (term_bound hn hmem).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast small) a0)
    _ = ((early n).card:ℝ)*(a*cutoff n) := by simp
    _ ≤ (cutoff n:ℝ)*(a*cutoff n) := mul_le_mul_of_nonneg_right size (by positivity)
    _ = a*(cutoff n:ℝ)^2 := by ring
    _ ≤ a*((n:ℝ)^3*exp (sqrt (log n)))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) bound _) a0
    _ = _ := by
      dsimp [a]
      rw [Nat.cast_pow,log_pow,Nat.cast_ofNat,show 2*sqrt (log n)=sqrt (log n)+sqrt (log n) by ring,exp_add]
      field_simp

theorem harmonic_window {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹ ≤ 1+2*log m := by
  have extend := sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc hm (le_refl (m^2)))
    (f := fun n : ℕ => (n:ℝ)⁻¹) (fun _ _ _ => by positivity)
  have total := harmonic_le_one_add_log (m^2)
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
    Nat.cast_pow,log_pow,Nat.cast_ofNat] at total
  exact extend.trans total

theorem early_window_bound {m : ℕ} (hm : 2 ≤ m) :
    window earlyAbs m ≤ kernelConstant * exp (10*sqrt (2*log m)) := by
  let u := sqrt (2*log m)
  have u0 : 0 ≤ u := sqrt_nonneg _
  have usq : u^2 = 2*log m := sq_sqrt (by linarith [log_natCast_nonneg m])
  let B := kernelConstant*(1+8*log m)*exp (2*u)
  have B0 : 0 ≤ B := by dsimp [B]; positivity [kernelConstant_nonneg, log_natCast_nonneg m]
  have each (n : ℕ) (hn : n ∈ Icc m (m^2)) : earlyAbs n/(n:ℝ)^3 ≤ B*(n:ℝ)⁻¹ := by
    obtain ⟨lo,hi⟩ := mem_Icc.mp hn
    have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
    have c : (n:ℝ) ≤ (m:ℝ)^2 := by exact_mod_cast hi
    have lg := log_le_log np c
    rw [log_pow,Nat.cast_ofNat] at lg
    have rt := sqrt_le_sqrt lg
    have inc : kernelConstant*(1+4*log n)*exp (2*sqrt (log n)) ≤ B := by
      dsimp [B,u]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) kernelConstant_nonneg)
        (exp_le_exp.mpr (by linarith)) (exp_pos _).le
        (mul_nonneg kernelConstant_nonneg (by linarith [log_natCast_nonneg m]))
    apply (div_le_iff₀ (pow_pos np 3)).mpr
    exact (early_abs_bound (hm.trans lo)).trans ((mul_le_mul_of_nonneg_left inc (sq_nonneg _)).trans_eq
      (by field_simp))
  have rough : window earlyAbs m ≤ B*(1+2*log m) := by
    apply (sum_le_sum each).trans
    rw [←mul_sum]
    exact mul_le_mul_of_nonneg_left (harmonic_window (by omega)) B0
  have square : 1+8*log m ≤ exp (4*u) := by
    have inc := add_one_le_exp (2*u)
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 2*u+1) inc 2
    rw [show (exp (2*u))^2=exp (4*u) by rw [show 4*u=2*u+2*u by ring,exp_add,pow_two]] at h
    nlinarith only [h,usq,u0]
  have product := mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left square kernelConstant_nonneg)
    (exp_pos (2*u)).le) ((show 1+2*log m ≤ 1+8*log m by linarith [log_natCast_nonneg m]).trans square)
    (show 0 ≤ 1+2*log m by linarith [log_natCast_nonneg m])
    (mul_nonneg (mul_nonneg kernelConstant_nonneg (exp_pos _).le) (exp_pos _).le)
  apply rough.trans (product.trans_eq ?_)
  change kernelConstant*exp (4*u)*exp (2*u)*exp (4*u) = kernelConstant*exp (10*u)
  rw [mul_assoc kernelConstant,← exp_add,mul_assoc kernelConstant,← exp_add]
  congr 2
  ring

/-- Every fixed multiple of exp(O(sqrt(log m))) is eventually below m^ε. -/
theorem eventual_exp_sqrt (C a ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, C * exp (a*sqrt (2*log m)) ≤ (m:ℝ)^ε := by
  have grow := tendsto_sqrt_atTop.comp (Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<2)
    (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))))
  filter_upwards [grow.eventually_ge_atTop (max C (2*(a+1)/ε)),eventually_ge_atTop (1:ℕ)] with m big one
  let u := sqrt (2*log m)
  change max C (2*(a+1)/ε) ≤ u at big
  have u0 : 0 ≤ u := sqrt_nonneg _
  have usq : u^2=2*log m := sq_sqrt (by linarith [log_natCast_nonneg m])
  have c : C ≤ exp u := ((le_max_left _ _).trans big).trans (by linarith only [add_one_le_exp u])
  have t := (div_le_iff₀ hε).mp ((le_max_right _ _).trans big)
  have h := mul_le_mul_of_nonneg_right t u0
  have p : 0 < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  rw [rpow_def_of_pos p]
  apply (mul_le_mul_of_nonneg_right c (exp_pos _).le).trans
  rw [← exp_add]
  apply exp_le_exp.mpr
  nlinarith only [h,congrArg (fun x : ℝ => ε*x) usq]

/-- The sum of the individual absolute values in the removed prefix already
meets the requested budget on every sufficiently late complete square window. -/
theorem early_window_subpower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, window earlyAbs m ≤ (m:ℝ)^ε := by
  filter_upwards [eventually_ge_atTop (2:ℕ),eventual_exp_sqrt kernelConstant 10 ε hε]
    with m hm cap
  exact (early_window_bound hm).trans cap

end RiemannReduction.ShortTail
