import OddMertensFold

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Real RiemannGaussian.AlpogeMined
open scoped ArithmeticFunction.Moebius

def bandLo (n j : ℕ) := max (max (fixedBandMultipleCutoff n) (cutoff n)) (n^4/2^(j+1))
def bandHi (n j : ℕ) := min (n^4/2) (n^4/2^j)

private theorem quotient_swap {N d q : ℕ} (dp : 0<d) (qp : 0<q) :
    q ≤ N/d ↔ d ≤ N/q := by
  rw [Nat.le_div_iff_mul_le dp,Nat.le_div_iff_mul_le qp,Nat.mul_comm]

theorem quotient_rows_interval (n j : ℕ) :
    quotientBandRows n 0 j = Ioc (bandLo n j) (bandHi n j) := by
  apply Finset.ext
  intro d
  by_cases dp : 0<d
  · have qpos (k : ℕ) : 0 < (2:ℕ)^k := by positivity
    have exchange (k : ℕ) := quotient_swap (N:=n^4) dp (qpos k)
    rw [quotientBandRows,mem_filter,highPart,mem_filter,late,mem_filter,indices,mem_Ioc,
      mem_Ioc,bandLo,bandHi,max_lt_iff,max_lt_iff,le_min_iff]
    unfold quotientLevel
    constructor
    · rintro ⟨⟨⟨⟨lo,up⟩,cut⟩,nz⟩,level⟩
      have q2 := (quotient_swap (by omega : 0<d) (by decide : 0<2)).mpr up
      obtain ⟨a,b⟩ := (Nat.log_eq_iff (b:=2) (n:=n^4/d) (Or.inr ⟨by decide,by omega⟩)).mp level
      exact ⟨⟨⟨lo,by omega⟩,lt_of_not_ge (fun x => (not_le_of_gt b) ((exchange _).mpr x))⟩,up,(exchange _).mp a⟩
    · rintro ⟨⟨⟨lo,cut⟩,hi⟩,up,lb⟩
      exact ⟨⟨⟨⟨lo,up⟩,by omega⟩,by omega⟩,Nat.log_eq_of_pow_le_of_lt_pow ((exchange _).mpr lb)
        (lt_of_not_ge (fun x => (not_le_of_gt hi) ((exchange _).mp x)))⟩
  · have z : d=0 := by omega
    simp [z,quotientBandRows,highPart,bandLo]

theorem cofactor_interval (a b : ℕ) :
    oddHalves (Ioc a b)=(Ioc (a/2) (b/2)).filter (fun r => r%2=1) := by
  ext r
  simp only [mem_odd_halves,mem_Ioc,mem_filter]
  omega

def oddWeighted (a b : ℕ) (w : ℕ → ℝ) := ∑ k ∈ Ioc a b, oddMu k*w k

theorem odd_rows_abel_input (n j : ℕ) :
    oddSum n (quotientBandRows n 0 j)=oddWeighted (bandLo n j) (bandHi n j) (rowWeight n) ∧
    cofactorSum n (quotientBandRows n 0 j)=oddWeighted (bandLo n j/2) (bandHi n j/2)
      (fun r => rowWeight n (2*r)) := by
  rw [quotient_rows_interval]
  constructor <;> simp [oddSum,cofactorSum,cofactor_interval,oddWeighted,oddMu,sum_filter,ite_mul]

def endpointVariation (a b : ℕ) (w : ℕ → ℝ) : ℝ :=
  |w b|+|w (a+1)|+∑ k ∈ Ioc a (b-1), |w (k+1)-w k|

theorem endpointVariation_nonneg (a b : ℕ) (w : ℕ → ℝ) : 0≤endpointVariation a b w := by
  unfold endpointVariation
  positivity

/-- Abel's bound on the original contiguous interval, with the odd Mertens
prefix. Empty intervals and a cofactor below the retained cutoff are allowed. -/
theorem odd_abel_bound {a b : ℕ} (w : ℕ → ℝ) {H : ℝ} (hp : 0≤H)
    (control : ∀ k ≤ b, |oddPrefix k| ≤ H) :
    |oddWeighted a b w| ≤ H*endpointVariation a b w := by
  by_cases ab : a<b
  · have id := sum_Ioc_by_parts w oddMu ab
    simp only [smul_eq_mul] at id
    have signed : oddWeighted a b w = w b*oddPrefix b-w (a+1)*oddPrefix a -
        ∑ k ∈ Ioc a (b-1), (w (k+1)-w k)*oddPrefix k := by
      unfold oddPrefix
      rw [←id]
      exact sum_congr rfl fun _ _ => mul_comm ..
    have edges (x k : ℕ) (cap : k≤b) : |w x*oddPrefix k| ≤ |w x| * H := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (control k cap) (abs_nonneg _)
    have middle := (abs_sum_le_sum_abs (fun k => (w (k+1)-w k)*oddPrefix k) (Ioc a (b-1))).trans
      (sum_le_sum (g:=fun k => |w (k+1)-w k| * H) (fun k hk => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (control k ((mem_Ioc.mp hk).2.trans (Nat.sub_le ..))) (abs_nonneg _)))
    rw [←sum_mul] at middle
    rw [signed]
    apply (abs_sub ..).trans
    have left := (abs_sub (w b*oddPrefix b) (w (a+1)*oddPrefix a)).trans
      (add_le_add (edges b b le_rfl) (edges (a+1) a ab.le))
    unfold endpointVariation
    nlinarith only [left,middle]
  · rw [oddWeighted,Ioc_eq_empty_of_le (le_of_not_gt ab),sum_empty,abs_zero]
    exact mul_nonneg hp (endpointVariation_nonneg ..)

/-- With a finite square-root envelope for ordinary M, each witness uses
only its two endpoint weights and the variation between them. -/
theorem odd_band_of_mertens {n j X : ℕ} {C : ℝ} (cp : 0≤C) (cap : bandHi n j ≤ X)
    (bound : ∀ k ≤ X, |fixedBandPrefix k| ≤ C*sqrt k) :
    |oddSum n (quotientBandRows n 0 j)| ≤
      4*C*sqrt (bandHi n j)*endpointVariation (bandLo n j) (bandHi n j) (rowWeight n) ∧
    |cofactorSum n (quotientBandRows n 0 j)| ≤
      4*C*sqrt ((bandHi n j/2:ℕ):ℝ)*endpointVariation (bandLo n j/2) (bandHi n j/2)
        (fun r => rowWeight n (2*r)) := by
  have uniform (a b : ℕ) (w : ℕ → ℝ) (hi : b≤X) :
      |oddWeighted a b w| ≤ 4*C*sqrt b*endpointVariation a b w := by
    apply odd_abel_bound w (by positivity)
    intro k hk
    exact (odd_prefix_sqrt cp bound k (hk.trans hi)).trans
      (mul_le_mul_of_nonneg_left (sqrt_le_sqrt (by exact_mod_cast hk)) (by positivity))
  obtain ⟨odd,half⟩ := odd_rows_abel_input n j
  rw [odd,half]
  exact ⟨uniform _ _ _ cap,uniform _ _ _ ((Nat.div_le_self ..).trans cap)⟩

end RiemannReduction.ShortTail.LossFrequency
