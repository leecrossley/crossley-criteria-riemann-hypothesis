import ThirdQuotient
import CheckAlpogeFixedPrimeBandFirstQuotient

/-! Specialize the second-band removal to Sanftenberg's public linear Möbius tail. -/
noncomputable section
namespace RiemannReduction.ThirdBridge
open Real Finset RiemannGaussian.AlpogeMined RiemannReduction.ThirdQuotient
open scoped ArithmeticFunction.Moebius

/-- The difference of the two public lattice functions. -/
def lattice (y : ℝ) := fixedBandLattice y - 2*fixedBandLattice (y/2)

/- Reuse proofs of four private helpers from their exact pinned module. Lean infers
their types from their original checked declarations and checks each alias. -/
open Lean Elab Command in
run_cmd do
  for short in [`latticeDifference_first,`latticeDifference_zero,`latticeDifference_decay,`lattice_continuousOn] do
    let source := ((`_private ++ `CheckAlpogeFixedPrimeBandFirstQuotient).num 0) ++ `RiemannGaussian.AlpogeMined ++ short
    let info ← getConstInfo source
    let levels := info.levelParams
    liftTermElabM <| addDecl <| .thmDecl {
      name := `RiemannReduction.ThirdBridge ++ short, levelParams := levels,
      type := info.type, value := mkConst source (levels.map Level.param) }

private theorem continuous_lattice : ContinuousRanges lattice := by
  intro Y
  have g := lattice_continuousOn Y
  have arg : ContinuousOn (fun y : ℝ => y/2) (Set.Icc 0 Y) := continuousOn_id.div_const 2
  have maps : Set.MapsTo (fun y : ℝ => y/2) (Set.Icc 0 Y) (Set.Icc 0 Y) :=
    fun y hy => ⟨by dsimp; linarith [hy.1],by dsimp; linarith [hy.1,hy.2]⟩
  exact g.sub (continuousOn_const.mul (g.comp arg maps))

def surviving (y : ℝ) := fixedBandCenteredKernel y - fixedBandFirstCorrection y
def thirdTail (N K : ℕ) := cutThird lattice surviving N K

private theorem half_eq (N K : ℕ) : fixedBandHalfTail N K = tail surviving N K := by
  apply sum_subset (Ioc_subset_Ioc_right (Nat.div_le_self ..))
  intro d hd hd'
  obtain ⟨hdk,hdn⟩ := mem_Ioc.mp hd
  have dh : N/2 < d := lt_of_not_ge (fun h => hd' (mem_Ioc.mpr ⟨hdk,h⟩))
  have hd₀ : 0 < (d:ℝ) := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt hdk)
  have hlo := (one_le_div hd₀).mpr (Nat.cast_le (α := ℝ).mpr hdn)
  have hhi := (div_le_iff₀ hd₀).mpr (show (N:ℝ) ≤ 2*d by exact_mod_cast (show N ≤ 2*d by omega))
  rw [fixedBandFirstCorrection_first hlo hhi,sub_self,mul_zero]

theorem half_third_error {N K : ℕ} (hN : 32 ≤ N) (hK : K ≤ N) :
    |fixedBandHalfTail N K - thirdTail N K| ≤ 12000*(K:ℝ)^2/N := by
  rw [half_eq]
  apply third_tail_error (fun h₁ h₂ => latticeDifference_first h₁ h₂) continuous_lattice
    (fun h₁ h₂ => latticeDifference_zero h₁ h₂) (fun h => latticeDifference_decay h) _ _ hN hK
  · intro y h₁ h₂
    simp [surviving,fixedBandFirstCorrection_first h₁ h₂]
  · intro z h₁ h₂
    exact fixedBandHalfKernel_second h₁ h₂

/-- The older sample handles n < 3, outside the N ≥ 32 correction domain. -/
def thirdSample (n : ℕ) : ℝ := if 3 ≤ n then thirdTail (n^4) (fixedBandMultipleCutoff n)
  else fixedBandHalfTail (n^4) (fixedBandMultipleCutoff n)

theorem sample_error {n : ℕ} (hn : 2 ≤ n) :
    |fixedBandHalfTail (n^4) (fixedBandMultipleCutoff n)-thirdSample n| ≤ 12000*(n:ℝ)^2 := by
  by_cases h : 3 ≤ n
  · rw [thirdSample,if_pos h]
    have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
    have hK : fixedBandMultipleCutoff n ≤ n^3 := Nat.div_le_self ..
    have h₄ := (by decide : 32 ≤ 3^4).trans (Nat.pow_le_pow_left h 4)
    have h₃ : n^3 ≤ n^4 := Nat.pow_le_pow_right (by omega) (by decide)
    apply (half_third_error h₄ (hK.trans h₃)).trans
    rw [Nat.cast_pow]
    apply (div_le_iff₀ (pow_pos hnR 4)).mpr
    calc
      12000*(fixedBandMultipleCutoff n:ℝ)^2 ≤ 12000*((n:ℝ)^3)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hK) 2) (by norm_num)
      _ = _ := by ring
  · simp only [thirdSample,if_neg h,sub_self,abs_zero]
    positivity

def thirdMass (s : ℝ) (m b : ℕ) := ∑ n ∈ Icc m b, max (s*thirdSample n) 0/(n:ℝ)^3
def halfMass (s : ℝ) (m b : ℕ) := ∑ n ∈ Icc m b,
  max (s*fixedBandHalfTail (n^4) (fixedBandMultipleCutoff n)) 0/(n:ℝ)^3

/-- On any whole interval both sign losses transfer with logarithmic total error. -/
theorem half_third_mass {s : ℝ} (hs : |s| ≤ 1) {m b : ℕ} (hm : 2 ≤ m) :
    |halfMass s m b - thirdMass s m b| ≤ 12000*(1+log b) := by
  apply fixedBand_mass_sqrt_error (by norm_num) _ hm
  intro n hn
  rw [←mul_sub,abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) hs).trans (sample_error hn)

theorem half_iff_third_log :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, fixedBandHalfTailMass m (m^2) ≤ C*(1+2*log m)) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, thirdMass 1 m (m^2) ≤ C*(1+2*log m)) := by
  constructor <;> rintro ⟨C,hC,h⟩ <;> refine ⟨C+12000,by positivity,fun A => ?_⟩ <;>
    obtain ⟨m,hm,hw⟩ := h (max 2 A)
  all_goals
    have he := abs_le.mp (half_third_mass (s:=1) (by norm_num) (b:=m^2) ((le_max_left 2 A).trans hm))
    have hmass : halfMass 1 m (m^2) = fixedBandHalfTailMass m (m^2) := by
      simp [halfMass,fixedBandHalfTailMass]
    rw [hmass,Nat.cast_pow,log_pow,Nat.cast_ofNat] at he
    exact ⟨m,(le_max_right 2 A).trans hm,by linarith only [hw,he.1,he.2]⟩

theorem rh_of_third_mass_log
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, thirdMass 1 m (m^2) ≤ C*(1+2*log m)) :
    RiemannHypothesis := rh_of_fixedBandHalfTailMass_log_squareWindows (half_iff_third_log.mpr h)

end RiemannReduction.ThirdBridge
open Lean Elab Command in
run_cmd do
  for n in [``RiemannReduction.ThirdBridge.half_third_error, ``RiemannReduction.ThirdBridge.half_third_mass,
      ``RiemannReduction.ThirdBridge.half_iff_third_log, ``RiemannReduction.ThirdBridge.rh_of_third_mass_log] do
    let axioms ← Lean.collectAxioms n
    for a in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Unexpected axiom {a} in {n}"
    logInfo m!"{n} uses {axioms}"


