import OddAbelBands
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Real RiemannGaussian.AlpogeMined
open scoped ArithmeticFunction.Moebius

private def shapeConstant : ℝ := 2*(1-eulerMascheroniConstant)+4*log 2+1
private def secondShape (z : ℝ) := (z-1)*shapeConstant + (3-4*z)*log z

private theorem shape_mono {u v : ℝ} (hu : 1 ≤ u) (uv : u ≤ v) (hv : v ≤ 3/2) :
    secondShape u ≤ secondShape v := by
  have up := zero_lt_one.trans_le hu
  have vp := up.trans_le uv
  have logCap := log_le_sub_one_of_pos vp
  have slope : 2 ≤ shapeConstant-4*log v := by
    unfold shapeConstant
    linarith only [logCap,hv,eulerMascheroniConstant_lt_two_thirds,log_two_gt_d9]
  have nonneg : 0 ≤ u*(shapeConstant-4*log v)-(4*u-3) := by
    nlinarith only [mul_le_mul_of_nonneg_left slope up.le,uv,hv]
  have logStep := log_le_sub_one_of_pos (div_pos vp up)
  rw [log_div vp.ne' up.ne'] at logStep
  have bound := mul_le_mul_of_nonneg_right logStep up.le
  simp only [sub_mul,div_mul_cancel₀ _ up.ne',one_mul] at bound
  have contribution := mul_le_mul_of_nonneg_left bound (by linarith : 0 ≤ 4*u-3)
  have scaled : 0 ≤ u*(secondShape v-secondShape u) := by
    unfold secondShape
    nlinarith only [contribution,mul_nonneg (sub_nonneg.mpr uv) nonneg]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left up).mp scaled)

private theorem shape_bounds {z : ℝ} (lo : 1 ≤ z) (hi : z ≤ 3/2) :
    0 ≤ secondShape z ∧ secondShape z ≤ 6/5 := by
  have bot := shape_mono (u:=1) le_rfl lo hi
  have top := shape_mono lo hi le_rfl
  constructor
  · simpa only [secondShape,sub_self,zero_mul,log_one,mul_zero,add_zero] using bot
  · apply top.trans
    unfold secondShape shapeConstant
    rw [log_div (by norm_num : (3:ℝ)≠0) (by norm_num : (2:ℝ)≠0)]
    linarith only [one_half_lt_eulerMascheroniConstant,log_two_lt_d9,log_three_gt_d9]

private def scaleAt (n d : ℕ) : ℝ := (((n^4:ℕ):ℝ)/d)/2

private theorem row_on_second {n d : ℕ} (dp : 0<d) (lo : n^4/3 < d) (hi : d ≤ n^4/2) :
    rowWeight n d=secondShape (scaleAt n d) ∧
    1 ≤ scaleAt n d ∧ scaleAt n d ≤ 3/2 := by
  have dr : 0<(d:ℝ) := Nat.cast_pos.mpr dp
  have dn : 2*(d:ℝ) ≤ ((n^4:ℕ):ℝ) := by exact_mod_cast (show 2*d ≤ n^4 by omega)
  have nd : ((n^4:ℕ):ℝ) ≤ 3*(d:ℝ) := by exact_mod_cast (show n^4 ≤ 3*d by omega)
  have h1 := (le_div_iff₀ dr).mpr dn
  have h2 := (div_le_iff₀ dr).mpr nd
  have one : 1 ≤ scaleAt n d := by unfold scaleAt; linarith only [h1]
  have three : 2*scaleAt n d ≤ 3 := by unfold scaleAt; linarith only [h2]
  refine ⟨?_,one,by linarith only [three]⟩
  have eq := fixedBandHalfKernel_second one three
  have e : 2*scaleAt n d = ((n^4:ℕ):ℝ)/d := by unfold scaleAt; ring
  rw [e] at eq
  exact eq

/-- Across quotient 2, the actual corrected kernel is nonnegative and
decreases as the divisor grows. This includes the truncated first divisor. -/
theorem second_row_antitone {n d e : ℕ} (dp : 0<d) (lo : n^4/3 < d) (de : d ≤ e)
    (hi : e ≤ n^4/2) :
    0 ≤ rowWeight n e ∧ rowWeight n e ≤ rowWeight n d ∧ rowWeight n d ≤ 6/5 := by
  obtain ⟨wd,ld,hd⟩ := row_on_second dp lo (de.trans hi)
  obtain ⟨we,le,he⟩ := row_on_second (dp.trans_le de) (lo.trans_le de) hi
  have anti : scaleAt n e ≤ scaleAt n d := by
    unfold scaleAt
    exact div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Nat.cast_pos.mpr dp) (Nat.cast_le.mpr de)) (by norm_num)
  rw [wd,we]
  exact ⟨(shape_bounds le he).1,shape_mono le anti hd,(shape_bounds ld hd).2⟩

private def secondLower (n : ℕ) :=
  max (max (fixedBandMultipleCutoff n) (cutoff n)) (n^4/3)

private theorem second_rows_interval (n : ℕ) :
    quotientRows n 2 = Ioc (secondLower n) (n^4/2) := by
  ext d
  by_cases dp : 0<d
  · have two : 2 ≤ n^4/d ↔ 2*d ≤ n^4 := Nat.le_div_iff_mul_le dp
    have three : 3 ≤ n^4/d ↔ 3*d ≤ n^4 := Nat.le_div_iff_mul_le dp
    simp only [quotientRows,late,indices,secondLower,mem_filter,mem_Ioc,max_lt_iff]
    omega
  · have z : d=0 := by omega
    simp [z,quotientRows,late,indices]

private theorem second_variation {n a b : ℕ} {p : ℕ → ℕ} (ab : a < b) (mono : Monotone p)
    (inside : ∀ k ∈ Ioc a b, n^4/3 < p k ∧ p k ≤ n^4/2) :
    endpointVariation a b (fun k => rowWeight n (p k)) ≤ 12/5 := by
  let w (k : ℕ) := rowWeight n (p k)
  have ant (i j : ℕ) (hi : i ∈ Ioc a b) (hj : j ∈ Ioc a b) (ij : i ≤ j) :
      0 ≤ w j ∧ w j ≤ w i ∧ w i ≤ 6/5 :=
    second_row_antitone (Nat.lt_of_le_of_lt (Nat.zero_le _) (inside i hi).1)
      (inside i hi).1 (mono ij) (inside j hj).2
  have front : a+1 ∈ Ioc a b := mem_Ioc.mpr ⟨by omega,by omega⟩
  have last : b ∈ Ioc a b := mem_Ioc.mpr ⟨ab,le_rfl⟩
  have endpoints := ant (a+1) b front last (by omega)
  have frontPos := (ant (a+1) (a+1) front front le_rfl).1
  have indices_eq : Ioc a (b-1)=Ico (a+1) b := by ext k; simp only [mem_Ioc,mem_Ico]; omega
  have telescope : (∑ k ∈ Ico (a+1) b, |w (k+1)-w k|)=w (a+1)-w b := by
    calc
      _ = -(∑ k ∈ Ico (a+1) b, (w (k+1)-w k)) := by
        rw [←sum_neg_distrib]
        apply sum_congr rfl
        intro k hk
        have h := mem_Ico.mp hk
        have each := ant k (k+1) (mem_Ioc.mpr ⟨by omega,by omega⟩)
          (mem_Ioc.mpr ⟨by omega,by omega⟩) (by omega)
        exact abs_of_nonpos (sub_nonpos.mpr each.2.1)
      _ = _ := by rw [sum_Ico_sub w (by omega)]; ring
  change |w b|+|w (a+1)|+(∑ k ∈ Ioc a (b-1), |w (k+1)-w k|) ≤ _
  rw [indices_eq,telescope,abs_of_nonneg endpoints.1,abs_of_nonneg frontPos]
  linarith only [endpoints.2.2]

private theorem weighted_second {n X a b : ℕ} {C : ℝ} (cp : 0 ≤ C) (cap : b ≤ X)
    (bound : ∀ k ≤ X, |fixedBandPrefix k| ≤ C*sqrt k)
    {p : ℕ → ℕ} (mono : Monotone p) (inside : ∀ k ∈ Ioc a b, n^4/3 < p k ∧ p k ≤ n^4/2) :
    |oddWeighted a b (fun k => rowWeight n (p k))| ≤ 48/5*C*sqrt b := by
  by_cases ab : a<b
  · have budget : ∀ k ≤ b, |oddPrefix k| ≤ 4*C*sqrt b := by
      intro k hk
      exact (odd_prefix_sqrt cp bound k (hk.trans cap)).trans
        (mul_le_mul_of_nonneg_left (sqrt_le_sqrt (by exact_mod_cast hk)) (by positivity))
    have upper := (odd_abel_bound (fun k => rowWeight n (p k)) (by positivity) budget).trans
      (mul_le_mul_of_nonneg_left (second_variation ab mono inside) (by positivity))
    linarith only [upper]
  · rw [oddWeighted,Ioc_eq_empty_of_le (le_of_not_gt ab),sum_empty,abs_zero]
    positivity

/-- An ordinary Mertens envelope through U controls both signed witnesses on
the whole (possibly truncated) quotient-2 interval. The cofactor bound uses
the smaller endpoint floor(U/2), and both constants are independent of n. -/
theorem second_quotient_of_mertens {n X : ℕ} {C : ℝ} (cp : 0 ≤ C) (cap : n^4/2 ≤ X)
    (bound : ∀ k ≤ X, |fixedBandPrefix k| ≤ C*sqrt k) :
    |oddSum n (quotientRows n 2)| ≤ 48/5*C*sqrt ((n^4/2:ℕ):ℝ) ∧
    |cofactorSum n (quotientRows n 2)| ≤ 48/5*C*sqrt ((n^4/4:ℕ):ℝ) := by
  let a := secondLower n
  let b := n^4/2
  have low : n^4/3 ≤ a := le_max_right .. 
  have one := weighted_second (n:=n) (a:=a) cp cap bound (p:=id) monotone_id
    (fun k hk => ⟨low.trans_lt (mem_Ioc.mp hk).1,(mem_Ioc.mp hk).2⟩)
  have half := weighted_second (n:=n) (a:=a/2) (b:=b/2) cp ((Nat.div_le_self ..).trans cap) bound
    (p:=fun k => 2*k) (fun _ _ hk => Nat.mul_le_mul_left 2 hk) (fun k hk => by
      obtain ⟨l,h⟩ := mem_Ioc.mp hk
      change n^4/3 < 2*k ∧ 2*k ≤ b
      omega)
  have eq : b/2 = n^4/4 := by dsimp [b]; omega
  rw [eq] at half
  rw [second_rows_interval]
  constructor
  · simpa [oddSum,oddWeighted,oddMu,sum_filter,ite_mul,a,b] using one
  · simpa [cofactorSum,cofactor_interval,oddWeighted,oddMu,sum_filter,ite_mul,a,b,
      show n^4/2/2=n^4/4 by omega] using half

private def smallCoefficient (n : ℕ) : ℤ :=
  if n=0 then 0 else if n.primeFactorsList.Nodup then (-1)^n.primeFactorsList.length else 0

private theorem smallCoefficient_eq (n : ℕ) : μ n = smallCoefficient n := by
  by_cases z : n=0
  · simp [z,smallCoefficient]
  · by_cases sf : Squarefree n
    · simp [smallCoefficient,z,(Nat.squarefree_iff_nodup_primeFactorsList z).mp sf,
        ArithmeticFunction.moebius_apply_of_squarefree sf,ArithmeticFunction.cardFactors_apply]
    · have h : ¬ n.primeFactorsList.Nodup :=
        fun e => sf ((Nat.squarefree_iff_nodup_primeFactorsList z).mpr e)
      simp [smallCoefficient,z,h,ArithmeticFunction.moebius_eq_zero_of_not_squarefree sf]

private theorem small_mertens {k : ℕ} (hk : k<33) : |fixedBandPrefix k| ≤ sqrt k := by
  have finite : ∀ i : Fin 33, (∑ d ∈ range (i.val+1), smallCoefficient d)^2 ≤ (i.val:ℤ) := by
    decide +kernel
  have e := finite ⟨k,hk⟩
  change (∑ d ∈ range (k+1), smallCoefficient d)^2 ≤ (k:ℤ) at e
  simp_rw [←smallCoefficient_eq] at e
  apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
  rw [sq_abs,sq_sqrt (Nat.cast_nonneg k)]
  unfold fixedBandPrefix
  exact_mod_cast e

/-- The published finite range plus the 33 early prefixes checked in the kernel. -/
theorem finite_mertens_sqrt
    (hurst : ∀ k : ℕ, 33 ≤ k → k ≤ 10^16 → |fixedBandPrefix k| ≤ 571/1000*sqrt k)
    (k : ℕ) (hk : k ≤ 10^16) : |fixedBandPrefix k| ≤ 1*sqrt k := by
  by_cases small : k<33
  · simpa only [one_mul] using small_mertens small
  · exact (hurst k (by omega) hk).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (sqrt_nonneg _))

/-- The 33..10^16 ordinary Mertens bound is an explicit literature input.
The early prefix squares are enumerated in the Lean kernel. -/
theorem second_quotient_finite_envelope
    (hurst : ∀ k : ℕ, 33 ≤ k → k ≤ 10^16 → |fixedBandPrefix k| ≤ 571/1000*sqrt k)
    {n : ℕ} (cap : n ≤ 11892) :
    |oddSum n (quotientRows n 2)| ≤ 7*(n:ℝ)^2 ∧
    |cofactorSum n (quotientRows n 2)| ≤ 7*(n:ℝ)^2 := by
  have hi : n^4/2 ≤ 10^16 :=
    (Nat.div_le_div_right (Nat.pow_le_pow_left cap 4)).trans (by decide)
  have ⟨odd,half⟩ := second_quotient_of_mertens (by norm_num : (0:ℝ) ≤ 1) hi (finite_mertens_sqrt hurst)
  have divCap : 2*((n^4/2:ℕ):ℝ) ≤ (n:ℝ)^4 := by exact_mod_cast (show 2*(n^4/2) ≤ n^4 by omega)
  have bound : sqrt ((n^4/2:ℕ):ℝ) ≤ 5/7*(n:ℝ)^2 := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    rw [sq_sqrt (Nat.cast_nonneg _),mul_pow]
    nlinarith only [divCap,sq_nonneg ((n:ℝ)^2)]
  have smaller : sqrt ((n^4/4:ℕ):ℝ) ≤ sqrt ((n^4/2:ℕ):ℝ) :=
    sqrt_le_sqrt (by exact_mod_cast (show n^4/4 ≤ n^4/2 by omega))
  constructor <;> nlinarith only [odd,half,bound,smaller,sq_nonneg (n:ℝ)]

/-- On the finite Mertens domain the two q=2 frequencies vanish at these
thresholds. Both signed inequalities hold at every index of each full block. -/
theorem second_quotient_finite_blocks
    (hurst : ∀ k : ℕ, 33 ≤ k → k ≤ 10^16 → |fixedBandPrefix k| ≤ 571/1000*sqrt k)
    {m : ℕ} (cap : m ≤ 109) {t : ℝ} (threshold : 28*(bandCount (m^2) 0:ℝ) ≤ t) :
    ∀ n ∈ Icc m (m^2),
      -share n 0 t ≤ oddSum n (quotientRows n 2) ∧
      cofactorSum n (quotientRows n 2) ≤ share n 0 t := by
  intro n hn
  have nb := (mem_Icc.mp hn).2
  have bmon : bandCount n 0 ≤ bandCount (m^2) 0 := by
    simpa [bandCount] using Nat.log_mono_right (b:=2) (Nat.pow_le_pow_left nb 4)
  have bp : 0 < (bandCount n 0:ℝ) := by unfold bandCount; positivity
  have h := second_quotient_finite_envelope hurst
    (nb.trans ((Nat.pow_le_pow_left cap 2).trans (by decide)))
  have tin : 28*(bandCount n 0:ℝ) ≤ t :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast bmon) (by norm_num)).trans threshold
  have amount : 7*(n:ℝ)^2 ≤ share n 0 t := by
    unfold share
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right tin (sq_nonneg (n:ℝ))]
  exact ⟨(neg_le_neg amount).trans (abs_le.mp h.1).1,(abs_le.mp h.2).2.trans amount⟩

end RiemannReduction.ShortTail.LossFrequency
