import QuotientSignFold

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Real ArithmeticFunction RiemannGaussian.AlpogeMined
open scoped ArithmeticFunction.Moebius

theorem mem_odd_halves {S : Finset ℕ} {r : ℕ} :
    r ∈ oddHalves S ↔ r%2=1 ∧ 2*r ∈ S := by
  constructor
  · intro h
    obtain ⟨d,hd,e⟩ := mem_image.mp (mem_filter.mp h).1
    have ev := (mem_filter.mp hd).2
    have rep : 2*r=d := by omega
    exact ⟨(mem_filter.mp h).2,rep ▸ (mem_filter.mp hd).1⟩
  · rintro ⟨hr,hd⟩
    exact mem_filter.mpr ⟨mem_image.mpr ⟨2*r,mem_filter.mpr ⟨hd,by omega⟩,by omega⟩,hr⟩

def oddMu (r : ℕ) : ℝ := if r%2=1 then (μ r:ℝ) else 0
def oddPrefix (x : ℕ) : ℝ := ∑ r ∈ range (x+1), oddMu r

def fullMoment (x k : ℕ) : ℝ := ∑ r ∈ range (x+1), (μ r:ℝ)*(r:ℝ)^k
def oddMoment (x k : ℕ) : ℝ :=
  ∑ r ∈ (range (x+1)).filter (fun d => d%2=1), (μ r:ℝ)*(r:ℝ)^k

/-- The even terms are minus the odd terms at half the argument. The exact
moment recurrence also applies when a bound or its half is odd. -/
theorem odd_moment_recurrence (x k : ℕ) :
    oddMoment x k = fullMoment x k + (2:ℝ)^k*oddMoment (x/2) k := by
  have halves : oddHalves (range (x+1)) =
      (range (x/2+1)).filter (fun r => r%2=1) := by
    ext r
    simp only [mem_odd_halves,mem_filter,mem_range]
    omega
  have eq := fold_signed_rows (range (x+1)) (fun r => (r:ℝ)^k)
  rw [halves] at eq
  change fullMoment x k = oddMoment x k - _ at eq
  have e : (∑ r ∈ (range (x/2+1)).filter (fun r => r%2=1), (μ r:ℝ)*((2*r:ℕ):ℝ)^k) =
      (2:ℝ)^k*oddMoment (x/2) k := by
    unfold oddMoment
    rw [mul_sum]
    apply sum_congr rfl
    intro r _
    push_cast
    rw [mul_pow]
    ring
  rw [eq,e]
  ring

theorem odd_prefix_recurrence (x : ℕ) :
    oddPrefix x = fixedBandPrefix x + oddPrefix (x/2) := by
  simpa [oddPrefix,oddMu,oddMoment,fullMoment,fixedBandPrefix,sum_filter] using odd_moment_recurrence x 0

/-- Transfers any finite ordinary square-root bound directly to the odd
prefixes through the same endpoint. The constant four also covers x=0. -/
theorem odd_prefix_sqrt {X : ℕ} {C : ℝ} (hc : 0 ≤ C)
    (bound : ∀ y ≤ X, |fixedBandPrefix y| ≤ C*sqrt y) :
    ∀ x ≤ X, |oddPrefix x| ≤ 4*C*sqrt x := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro hx
    by_cases xp : x=0
    · subst x
      simp [oddPrefix,oddMu]
    have prev := ih (x/2) (by omega) ((Nat.div_le_self ..).trans hx)
    have half : 2*((x/2:ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast (show 2*(x/2) ≤ x by omega)
    have root : sqrt ((x/2:ℕ):ℝ) ≤ 3/4*sqrt x := by
      apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
      rw [mul_pow, sq_sqrt (Nat.cast_nonneg _),sq_sqrt (Nat.cast_nonneg _)]
      nlinarith only [half,Nat.cast_nonneg (α:=ℝ) x]
    rw [odd_prefix_recurrence]
    apply (abs_add_le ..).trans
    have scale := mul_le_mul_of_nonneg_left root (show 0≤4*C by positivity)
    linarith only [prev,scale,bound x hx]

end RiemannReduction.ShortTail.LossFrequency
