import DivisorAttribution

/-! Fold the even rows in an original quotient range onto their odd halves.
The signs reverse by multiplicativity, and multiples of four contribute zero. -/

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset ArithmeticFunction RiemannGaussian.AlpogeMined
open scoped ArithmeticFunction.Moebius

def oddHalves (S : Finset ℕ) : Finset ℕ :=
  ((S.filter (fun d => ¬ d%2=1)).image (fun d => d/2)).filter (fun r => r%2=1)

private theorem double_sign (r : ℕ) :
    (μ (2*r):ℝ) = if r%2=1 then -(μ r:ℝ) else 0 := by
  by_cases h : r%2=1
  · have odd : Odd r := Nat.odd_iff.mpr h
    rw [if_pos h,isMultiplicative_moebius.map_mul_of_coprime odd.coprime_two_left,
      moebius_apply_prime Nat.prime_two]
    push_cast
    ring
  · have nonsq : ¬ Squarefree (2*r) := fun sq =>
      (Nat.squarefree_iff_prime_squarefree.mp sq 2 Nat.prime_two) ⟨r/2,by omega⟩
    rw [if_neg h,moebius_eq_zero_of_not_squarefree nonsq,Int.cast_zero]

theorem fold_signed_rows (S : Finset ℕ) (w : ℕ → ℝ) :
    ∑ d ∈ S, (μ d:ℝ)*w d =
      (∑ d ∈ S.filter (fun d => d%2=1), (μ d:ℝ)*w d) -
      ∑ r ∈ oddHalves S, (μ r:ℝ)*w (2*r) := by
  let evenRows := S.filter (fun d => ¬ d%2=1)
  have even_at (d : ℕ) (hd : d ∈ evenRows) : 2*(d/2)=d := by
    have h := (mem_filter.mp hd).2
    omega
  have inj : Set.InjOn (fun d : ℕ => d/2) (↑evenRows) := by
    intro a ha b hb equal
    exact (even_at a ha).symm.trans ((congrArg (2 * ·) equal).trans (even_at b hb))
  have packed : (∑ r ∈ oddHalves S, (μ r:ℝ)*w (2*r)) =
      -(∑ d ∈ evenRows, (μ d:ℝ)*w d) := by
    unfold oddHalves
    rw [sum_filter, sum_image inj,←sum_neg_distrib]
    apply sum_congr rfl
    intro d hd
    have rep := even_at d hd
    have sign : (μ d:ℝ) = if (d/2)%2=1 then -(μ (d/2):ℝ) else 0 := by
      calc (μ d:ℝ) = (μ (2*(d/2)):ℝ) := by rw [rep]
           _ = _ := double_sign (d/2)
    by_cases odd : (d/2)%2=1 <;> simp [sign, odd, rep]
  rw [packed, sub_neg_eq_add]
  exact (sum_filter_add_sum_filter_not S (fun d => d%2=1) (fun d => (μ d:ℝ)*w d)).symm

def quotientRows (n q : ℕ) := (late n).filter (fun d => n^4/d=q)

def rowWeight (n d : ℕ) : ℝ := fixedBandCenteredKernel (((n^4:ℕ):ℝ)/d) -
  fixedBandFirstCorrection (((n^4:ℕ):ℝ)/d)

theorem quotient_sign_fold (n q : ℕ) :
    ∑ d ∈ quotientRows n q, term n d =
      (∑ d ∈ (quotientRows n q).filter (fun d => d%2=1), (μ d:ℝ)*rowWeight n d) -
      ∑ r ∈ oddHalves (quotientRows n q), (μ r:ℝ)*rowWeight n (2*r) :=
  fold_signed_rows (quotientRows n q) (rowWeight n)

/-- Only two quotient ranges can supply these odd cofactors. A cofactor may
lie below the retained cutoff even when its double is in the retained range. -/
theorem halved_quotient {n q r : ℕ} (hr : r ∈ oddHalves (quotientRows n q)) :
    n^4/r = 2*q ∨ n^4/r = 2*q+1 := by
  obtain ⟨d,hd,e⟩ := mem_image.mp (mem_filter.mp hr).1
  obtain ⟨hb,even⟩ := mem_filter.mp hd
  have bin := (mem_filter.mp hb).2
  have rep : 2*r=d := by omega
  have div : n^4/r/2=q := by rwa [Nat.div_div_eq_div_mul,Nat.mul_comm r 2,rep]
  omega

def quotientBandRows (n b j : ℕ) := (highPart n b).filter (fun d => quotientLevel n d=j)

def oddSum (n : ℕ) (S : Finset ℕ) :=
  ∑ d ∈ S.filter (fun d => d%2=1), (μ d:ℝ)*rowWeight n d

def cofactorSum (n : ℕ) (S : Finset ℕ) :=
  ∑ r ∈ oddHalves S, (μ r:ℝ)*rowWeight n (2*r)

theorem halved_dyadic_band {n b j r : ℕ} (hr : r ∈ oddHalves (quotientBandRows n b j)) :
    quotientLevel n r=j+1 := by
  obtain ⟨d,hd,e⟩ := mem_image.mp (mem_filter.mp hr).1
  obtain ⟨hb,even⟩ := mem_filter.mp hd
  obtain ⟨hh,level⟩ := mem_filter.mp hb
  have span := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hh).1).1
  have rep : 2*r=d := by omega
  have dq : 2 ≤ n^4/d := (Nat.le_div_iff_mul_le (by omega : 0<d)).mpr (by omega)
  have div : n^4/r/2=n^4/d := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm r 2,rep]
  change Nat.log 2 (n^4/r)=j+1
  rw [Nat.log_of_one_lt_of_le (by decide : 1<2) (by omega : 2 ≤ n^4/r),div]
  exact congrArg (· + 1) level

def share (n b : ℕ) (t : ℝ) := t*(n:ℝ)^2/(2*(bandCount n b:ℝ))/2

/-- A large loss requires either a negative odd contribution in some dyadic
quotient band or a positive signed sum on odd cofactors one band higher. -/
theorem odd_band_driving_hit {n b : ℕ} {t : ℝ} (hn : 2 ≤ n)
    (tp : 0 < t) (hit : t < score n) (small : envelope n*(b:ℝ)^2 ≤ t*(n:ℝ)^2/2) :
    ∃ j < bandCount n b,
      oddSum n (quotientBandRows n b j) < -share n b t ∨
      share n b t < cofactorSum n (quotientBandRows n b j) := by
  obtain ⟨j,hj,neg⟩ := band_driving_hit hn tp hit small
  refine ⟨j,hj,?_⟩
  have split : bandSum n b j = oddSum n (quotientBandRows n b j) -
      cofactorSum n (quotientBandRows n b j) := fold_signed_rows _ (rowWeight n)
  rw [split,neg_div] at neg
  unfold share
  by_contra! h
  linarith only [h.1,h.2,neg]

def oddAlarm (n : ℕ) (t : ℝ) : Prop := ∃ j < bandCount n 0,
  oddSum n (quotientBandRows n 0 j) < -share n 0 t ∨
  share n 0 t < cofactorSum n (quotientBandRows n 0 j)

open Classical in
/-- Controlling the harmonic frequency of these explicitly signed odd sums
would give the desired estimate on exactly the same blocks and thresholds. -/
theorem frequency_odd_witness {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (tp : 0 < t) :
    frequency score m t ≤ ∑ n ∈ Icc m (m^2), if oddAlarm n t then (n:ℝ)⁻¹ else 0 := by
  apply sum_le_sum
  intro n hn
  by_cases hit : t < score n
  · have witness : oddAlarm n t := odd_band_driving_hit (hm.trans (mem_Icc.mp hn).1) tp hit
        (by simp only [Nat.cast_zero,zero_pow (by decide : 2≠0),mul_zero]; positivity)
    simp only [if_pos hit,if_pos witness,le_refl]
  · simp only [if_neg hit]
    split <;> positivity

end RiemannReduction.ShortTail.LossFrequency
