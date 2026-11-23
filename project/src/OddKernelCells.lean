import OddKernelVariation

/-! Quotient-cell formula for Sanftenberg's corrected weight. The primitive
below is the one used in his first-quotient calculation. -/

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Real MeasureTheory RiemannGaussian.AlpogeMined

private def integrandRamp (z t : ℝ) := (1+1/t)*max (z/t-1) 0
def integratedRamp (z : ℝ) := ∫ t in (1:ℝ)..2, integrandRamp z t
private def antiderivativeRamp (z t : ℝ) := (z-1)*log t-z/t-t

private theorem ramp_integrable (z : ℝ) {a b : ℝ} (ha : 1≤a) (ab : a≤b) :
    IntervalIntegrable (integrandRamp z) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le ab]
  have nz (t : ℝ) (ht : t∈Set.Icc a b) : t≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (ha.trans ht.1))
  unfold integrandRamp
  fun_prop (disch := assumption)

private theorem ramp_active (z : ℝ) {b : ℝ} (hb : 1≤b) (bz : b≤z) :
    (∫ t in (1:ℝ)..b, integrandRamp z t) = antiderivativeRamp z b-antiderivativeRamp z 1 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (ramp_integrable z le_rfl hb)
  intro t ht
  rw [Set.uIcc_of_le hb] at ht
  have tp := zero_lt_one.trans_le ht.1
  have h := (one_le_div tp).mpr (ht.2.trans bz)
  rw [integrandRamp,max_eq_left (by linarith)]
  unfold antiderivativeRamp
  convert (((Real.hasDerivAt_log tp.ne').const_mul (z-1)).sub
    ((hasDerivAt_const t z).div (hasDerivAt_id' t) tp.ne')).sub (hasDerivAt_id' t) using 1
  · rfl
  · field_simp [tp.ne']
    ring

private theorem ramp_inactive (z : ℝ) {a b : ℝ} (ha : 1≤a) (za : z≤a) (ab : a≤b) :
    (∫ t in a..b, integrandRamp z t) = 0 := by
  rw [←intervalIntegral.integral_zero (a:=a) (b:=b) (E:=ℝ)]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le ab] at ht
  have tp := zero_lt_one.trans_le (ha.trans ht.1)
  have h := (div_le_one tp).mpr (za.trans ht.1)
  simp [integrandRamp,max_eq_right (by linarith : z/t-1 ≤ 0)]

theorem integrated_ramp_low {z : ℝ} (h : z≤1) : integratedRamp z=0 :=
  ramp_inactive z le_rfl h (by norm_num)

theorem integrated_ramp_middle {z : ℝ} (lo : 1≤z) (hi : z≤2) :
    integratedRamp z=(z-1)*log z := by
  rw [integratedRamp,←intervalIntegral.integral_add_adjacent_intervals (ramp_integrable z le_rfl lo)
    (ramp_integrable z lo hi),ramp_active z lo le_rfl,ramp_inactive z lo le_rfl hi]
  simp [antiderivativeRamp,(zero_lt_one.trans_le lo).ne']
  ring

theorem integrated_ramp_high {z : ℝ} (hi : 2≤z) :
    integratedRamp z=(z-1)*log 2+z/2-1 := by
  rw [integratedRamp,ramp_active z (by norm_num) hi]
  simp only [antiderivativeRamp,log_one,mul_zero,div_one]
  ring

private def OnCell (q : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ A B C D : ℝ, Set.EqOn f (cellForm A B C D) (Set.Icc (q:ℝ) (q+1))

private theorem cell_add {q : ℕ} {f g : ℝ → ℝ} (hf : OnCell q f) (hg : OnCell q g) :
    OnCell q (fun y => f y+g y) := by
  obtain ⟨A,B,C,D,ef⟩ := hf
  obtain ⟨a,b,c,d,eg⟩ := hg
  refine ⟨A+a,B+b,C+c,D+d,fun y hy => ?_⟩
  dsimp only
  rw [ef hy,eg hy]
  unfold cellForm
  ring

private theorem cell_smul {q : ℕ} {f : ℝ → ℝ} (a : ℝ) (hf : OnCell q f) :
    OnCell q (fun y => a*f y) := by
  obtain ⟨A,B,C,D,ef⟩ := hf
  refine ⟨a*A,a*B,a*C,a*D,fun y hy => ?_⟩
  dsimp only
  rw [ef hy]
  unfold cellForm
  ring

private theorem cell_sub {q : ℕ} {f g : ℝ → ℝ} (hf : OnCell q f) (hg : OnCell q g) :
    OnCell q (fun y => f y-g y) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using cell_add hf (cell_smul (-1) hg)

private theorem cell_sum {q : ℕ} {s : Finset ℕ} {f : ℕ → ℝ → ℝ}
    (h : ∀ k∈s, OnCell q (f k)) : OnCell q (fun y => ∑ k∈s, f k y) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0,0,0,0,by intro y _; simp [cellForm]⟩
  | @insert a s na ih =>
    simpa only [sum_insert na] using cell_add (h a (mem_insert_self ..))
      (ih (fun k hk => h k (mem_insert_of_mem hk)))

private def spike (v : ℕ) (y : ℝ) := max (y/v-1) 0
private theorem weighted_spike_cell (q : ℕ) {v : ℕ} (vp : 0<v) (l c : ℝ) :
    OnCell q (fun y => (l*log y+c)*spike v y) := by
  have vr : 0<(v:ℝ) := by exact_mod_cast vp
  by_cases before : q<v
  · refine ⟨0,0,0,0,fun y hy => ?_⟩
    have endpt : (q:ℝ)+1 ≤ v := by exact_mod_cast before
    have off := (div_le_one vr).mpr (hy.2.trans endpt)
    simp [spike,cellForm,max_eq_right (by linarith : y/v-1 ≤ 0)]
  · refine ⟨l/v,c/v,-l,-c,fun y hy => ?_⟩
    have start : (v:ℝ)≤q := by exact_mod_cast (le_of_not_gt before)
    have on := (one_le_div vr).mpr (start.trans hy.1)
    dsimp only
    rw [spike,max_eq_left (by linarith)]
    unfold cellForm
    ring

private theorem integrated_spike_cell (q : ℕ) {v : ℕ} (vp : 0<v) :
    OnCell q (fun y => integratedRamp (y/v)) := by
  have vr : 0<(v:ℝ) := by exact_mod_cast vp
  by_cases before : q<v
  · refine ⟨0,0,0,0,fun y hy => ?_⟩
    have stop : (q:ℝ)+1≤v := by exact_mod_cast before
    simp [integrated_ramp_low ((div_le_one vr).mpr (hy.2.trans stop)),cellForm]
  · have start : (v:ℝ)≤q := by exact_mod_cast le_of_not_gt before
    by_cases after : 2*v≤q
    · refine ⟨0,(log 2+1/2)/v,0,-log 2-1,fun y hy => ?_⟩
      have h : 2*(v:ℝ)≤q := by exact_mod_cast after
      dsimp only
      rw [integrated_ramp_high ((le_div_iff₀ vr).mpr (h.trans hy.1))]
      unfold cellForm
      ring
    · refine ⟨1/v,-log v/v,-1,log v,fun y hy => ?_⟩
      have stop : (q:ℝ)+1≤2*v := by exact_mod_cast (show q+1≤2*v by omega)
      have yp := vr.trans_le (start.trans hy.1)
      dsimp only
      rw [integrated_ramp_middle ((one_le_div vr).mpr (start.trans hy.1))
        ((div_le_iff₀ vr).mpr (hy.2.trans stop)),log_div yp.ne' vr.ne']
      unfold cellForm
      ring

private def scaledU (a : ℕ) (y : ℝ) := fixedBandUnitRamp (y/a)

private theorem scaledU_expand {q a : ℕ} (ha : 0<a) {y : ℝ} (yp : 0≤y) (cap : y≤(q:ℝ)+1) :
    scaledU a y=∑ k ∈ Ioc 0 (q+1), spike (a*k) y := by
  have ap : (1:ℝ)≤a := by exact_mod_cast ha
  have cap' : y/a≤((q+1:ℕ):ℝ) := by push_cast; exact (div_le_self yp ap).trans cap
  have eq := fixedBandUnitRamp_sum (div_nonneg yp (Nat.cast_nonneg a)) cap'
  rw [Nat.floor_natCast] at eq
  rw [scaledU,←eq]
  apply sum_congr rfl
  intro k _
  simp [spike,Nat.cast_mul,div_div]

private theorem weighted_U_cell (q : ℕ) {a : ℕ} (ha : 0<a) (l c : ℝ) :
    OnCell q (fun y => (l*log y+c)*scaledU a y) := by
  obtain ⟨A,B,C,D,id⟩ := cell_sum (q:=q) (s:=Ioc 0 (q+1))
    (f:=fun k y => (l*log y+c)*spike (a*k) y)
    (fun k hk => weighted_spike_cell q (Nat.mul_pos ha (mem_Ioc.mp hk).1) l c)
  refine ⟨A,B,C,D,fun y hy => ?_⟩
  dsimp only
  rw [scaledU_expand ha ((Nat.cast_nonneg q).trans hy.1) hy.2,mul_sum]
  exact id hy

private def weightedU (a : ℕ) (y t : ℝ) := (1+1/t)*scaledU a (y/t)
private def integratedU (a : ℕ) (y : ℝ) := ∫ t in (1:ℝ)..2, weightedU a y t

private theorem weightedU_expand {q a : ℕ} (ha : 0<a) {y : ℝ} (yp : 0≤y) (cap : y≤(q:ℝ)+1)
    {t : ℝ} (ht : 1≤t) : weightedU a y t =
      ∑ k ∈ Ioc 0 (q+1), integrandRamp (y/(a*k:ℕ)) t := by
  have tp : 0<t := zero_lt_one.trans_le ht
  rw [weightedU,scaledU_expand ha (div_nonneg yp tp.le) ((div_le_self yp ht).trans cap),mul_sum]
  apply sum_congr rfl
  intro k _
  dsimp only [spike,integrandRamp]
  rw [div_right_comm y t]

private theorem integrated_U_cell (q : ℕ) {a : ℕ} (ha : 0<a) : OnCell q (integratedU a) := by
  obtain ⟨A,B,C,D,id⟩ := cell_sum (q:=q) (s:=Ioc 0 (q+1))
    (f:=fun k y => integratedRamp (y/(a*k:ℕ)))
    (fun k hk => integrated_spike_cell q (Nat.mul_pos ha (mem_Ioc.mp hk).1))
  refine ⟨A,B,C,D,fun y hy => ?_⟩
  rw [←id hy]
  unfold integratedU integratedRamp
  dsimp only
  rw [←intervalIntegral.integral_finsetSum (f:= fun k => integrandRamp (y/(a*k:ℕ)))
    (a:=1) (b:=2) (fun _ _ => ramp_integrable _ le_rfl (by norm_num))]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (1:ℝ)≤2)] at ht
  exact weightedU_expand ha ((Nat.cast_nonneg q).trans hy.1) hy.2 ht.1

private theorem weightedU_integrable {q a : ℕ} (ha : 0<a) {y : ℝ}
    (yp : 0≤y) (cap : y≤(q:ℝ)+1) : IntervalIntegrable (weightedU a y) volume 1 2 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (1:ℝ)≤2)]
  have nz (t : ℝ) (ht : t∈Set.Icc (1:ℝ) 2) : t≠0 := (zero_lt_one.trans_le ht.1).ne'
  have cont (k : ℕ) : ContinuousOn (integrandRamp (y/(a*k:ℕ))) (Set.Icc 1 2) := by
    unfold integrandRamp
    fun_prop (disch := assumption)
  apply (continuousOn_finsetSum (Ioc 0 (q+1)) (fun k _ => cont k)).congr
  intro t ht
  exact weightedU_expand ha yp cap ht.1

private def fourRamps (f : ℕ → ℝ → ℝ) (y : ℝ) := f 1 y-5*f 2 y+8*f 4 y-4*f 8 y
private def threeRamps (f : ℕ → ℝ → ℝ) (y : ℝ) := f 1 y-3*f 2 y+2*f 4 y

private theorem three_cells (q : ℕ) {f : ℕ → ℝ → ℝ} (forms : ∀ a>0, OnCell q (f a)) :
    OnCell q (threeRamps f) :=
  cell_add (cell_sub (forms 1 (by decide)) (cell_smul 3 (forms 2 (by decide))))
    (cell_smul 2 (forms 4 (by decide)))

private theorem four_cells (q : ℕ) {f : ℕ → ℝ → ℝ} (forms : ∀ a>0, OnCell q (f a)) :
    OnCell q (fourRamps f) :=
  cell_sub (cell_add (cell_sub (forms 1 (by decide)) (cell_smul 5 (forms 2 (by decide))))
    (cell_smul 8 (forms 4 (by decide)))) (cell_smul 4 (forms 8 (by decide)))

private theorem lattice_as_three {y : ℝ} (yp : 0≤y) : fixedBandLattice y=threeRamps scaledU y := by
  simpa [threeRamps,scaledU] using fixedBandLattice_ramps yp

private theorem difference_as_four {y : ℝ} (yp : 0≤y) :
    fixedBandLattice y-2*fixedBandLattice (y/2)=fourRamps scaledU y := by
  rw [fixedBandLattice_ramps yp,fixedBandLattice_ramps (div_nonneg yp (by norm_num : (0:ℝ)≤2))]
  simp only [fourRamps,scaledU,Nat.cast_one,div_one,Nat.cast_ofNat]
  rw [show y/2/2=y/4 by ring,show y/2/4=y/8 by ring]
  ring

private theorem integral_as_four {q : ℕ} {y : ℝ} (yp : 0≤y) (cap : y≤(q:ℝ)+1) :
    (∫ t in (1:ℝ)..2, (1+1/t)*(fixedBandLattice (y/t)-2*fixedBandLattice (y/t/2))) =
    fourRamps integratedU y := by
  have int (a : ℕ) (ha : 0<a) := weightedU_integrable ha yp cap
  have step : (∫ t in (1:ℝ)..2, (1+1/t)*(fixedBandLattice (y/t)-2*fixedBandLattice (y/t/2))) =
      ∫ t in (1:ℝ)..2, weightedU 1 y t-5*weightedU 2 y t+8*weightedU 4 y t-4*weightedU 8 y t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ)≤2)] at ht
    dsimp only
    rw [difference_as_four (div_nonneg yp (zero_lt_one.trans_le ht.1).le)]
    unfold fourRamps weightedU
    ring
  rw [step,intervalIntegral.integral_sub (((int 1 (by decide)).sub ((int 2 (by decide)).const_mul 5)).add
    ((int 4 (by decide)).const_mul 8)) ((int 8 (by decide)).const_mul 4),
    intervalIntegral.integral_add ((int 1 (by decide)).sub ((int 2 (by decide)).const_mul 5))
      ((int 4 (by decide)).const_mul 8),
    intervalIntegral.integral_sub (int 1 (by decide)) ((int 2 (by decide)).const_mul 5)]
  simp only [fourRamps,integratedU,intervalIntegral.integral_const_mul]

/-- The actual corrected kernel is a member of the four-dimensional family
on every closed integer quotient cell. The proof expands all original ramps. -/
theorem signed_kernel_quotient_cells : HasQuotientCellForm signedQuotientKernel := by
  intro q _hq
  have plain (a : ℕ) (ha : 0<a) : OnCell q (scaledU a) := by
    simpa only [zero_mul,zero_add,one_mul] using weighted_U_cell q ha 0 1
  let weighted := fun (a : ℕ) (y : ℝ) => (log y+fixedBandLogConstant)*scaledU a y
  have wt (a : ℕ) (ha : 0<a) : OnCell q (weighted a) := by
    simpa only [weighted,one_mul] using weighted_U_cell q ha 1 fixedBandLogConstant
  obtain ⟨A,B,C,D,form⟩ := cell_add (cell_sub (cell_sub
    (cell_smul (log 2) (cell_sub (plain 1 (by decide)) (plain 2 (by decide))))
    (three_cells q wt)) (cell_smul (1-eulerMascheroniConstant) (four_cells q plain)))
    (four_cells q fun _ h => integrated_U_cell q h)
  refine ⟨A,B,C,D,fun y hy => ?_⟩
  rw [←form hy]
  have yp := (Nat.cast_nonneg q).trans hy.1
  change fixedBandCenteredKernel y-((1-eulerMascheroniConstant)*(fixedBandLattice y-2*fixedBandLattice (y/2))
    -(∫ t in (1:ℝ)..2, (1+1/t)*(fixedBandLattice (y/t)-2*fixedBandLattice (y/t/2)))) = _
  rw [fixedBandCenteredKernel,difference_as_four yp,integral_as_four yp hy.2,lattice_as_three yp]
  simp only [weighted,threeRamps,scaledU,Nat.cast_one,Nat.cast_ofNat,div_one]
  ring

/-- Total variation of the original corrected kernel across a dyadic
interval is logarithmic in its lower endpoint. -/
theorem signed_kernel_variation_bound (Q : ℕ) (hQ : 2≤Q) :
    eVariationOn signedQuotientKernel (Set.Icc (Q:ℝ) (2*Q)) ≤
      ENNReal.ofReal (8*kernelConstant*(1+log (2*Q))) :=
  signed_kernel_dyadic_variation signed_kernel_quotient_cells Q hQ

/-- A square-root bound for the ordinary Mertens prefix up to the upper
divisor endpoint controls both signed sums on this dyadic bin. -/
theorem both_signed_dyadic_of_mertens {n j X : ℕ} {C : ℝ} (cp : 0≤C)
    (cap : bandHi n j ≤ X) (mertens : ∀ k ≤ X, |fixedBandPrefix k| ≤ C*sqrt k) :
    |oddSum n (quotientBandRows n 0 j)| ≤ 80*kernelConstant*C*(n:ℝ)^2 ∧
    |cofactorSum n (quotientBandRows n 0 j)| ≤ 80*kernelConstant*C*(n:ℝ)^2 :=
  both_signed_dyadic_uniform cp cap mertens signed_kernel_quotient_cells

end RiemannReduction.ShortTail.LossFrequency
