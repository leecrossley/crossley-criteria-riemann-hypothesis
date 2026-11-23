import OddAbelBands
import Mathlib.Topology.EMetricSpace.BoundedVariation

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Set Real Finset
open scoped ENNReal

private def oneSign (g : ℝ → ℝ) (a b : ℝ) :=
  (∀ x ∈ Ioo a b, 0≤g x) ∨ (∀ x ∈ Ioo a b, g x≤0)

private def oneDirection (f : ℝ → ℝ) (a b : ℝ) :=
  MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b)

private theorem split_inc {g : ℝ → ℝ} {a b : ℝ} (ab : a≤b)
    (ct : ContinuousOn g (Icc a b)) (inc : MonotoneOn g (Icc a b)) :
    ∃ c ∈ Icc a b, oneSign g a c ∧ oneSign g c b := by
  have ea : a ∈ Icc a b := ⟨le_rfl,ab⟩
  have eb : b ∈ Icc a b := ⟨ab,le_rfl⟩
  by_cases p : 0 ≤ g a
  · exact ⟨a,ea,Or.inl (by simp),Or.inl (fun x hx =>
      p.trans (inc ea (Ioo_subset_Icc_self hx) hx.1.le))⟩
  by_cases q : g b ≤ 0
  · exact ⟨b,eb,Or.inr (fun x hx =>
      (inc (Ioo_subset_Icc_self hx) eb hx.2.le).trans q),Or.inr (by simp)⟩
  obtain ⟨c,hc,zero⟩ := intermediate_value_Icc ab ct (show (0:ℝ) ∈ Icc (g a) (g b) from
      ⟨le_of_not_ge p,le_of_not_ge q⟩)
  refine ⟨c,hc,Or.inr ?_,Or.inl ?_⟩
  · intro x hx
    exact (inc ⟨hx.1.le,hx.2.le.trans hc.2⟩ hc hx.2.le).trans_eq zero
  · intro x hx
    exact zero.symm.le.trans (inc hc ⟨hc.1.trans hx.1.le,hx.2.le⟩ hx.1.le)

private theorem split_sign {g : ℝ → ℝ} {a b : ℝ} (ab : a≤b)
    (ct : ContinuousOn g (Icc a b)) (dir : oneDirection g a b) :
    ∃ c ∈ Icc a b, oneSign g a c ∧ oneSign g c b := by
  rcases dir with inc|dec
  · exact split_inc ab ct inc
  have hneg : MonotoneOn (fun x => -g x) (Icc a b) := fun _ hx _ hy xy => neg_le_neg (dec hx hy xy)
  obtain ⟨c,hc,p,q⟩ := split_inc ab ct.neg hneg
  have back {u v : ℝ} (x : oneSign (fun z => -g z) u v) : oneSign g u v := by
    rcases x with x|x
    · exact Or.inr fun z hz => neg_nonneg.mp (x z hz)
    · exact Or.inl fun z hz => neg_nonpos.mp (x z hz)
  exact ⟨c,hc,back p,back q⟩

private theorem dir_of_deriv {f g : ℝ → ℝ} {a b : ℝ}
    (ct : ContinuousOn f (Icc a b))
    (der : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) (sgn : oneSign g a b) :
    oneDirection f a b := by
  have dif : DifferentiableOn ℝ f (interior (Icc a b)) := by
    rw [interior_Icc]
    exact fun x hx => (der x hx).differentiableAt.differentiableWithinAt
  rcases sgn with p|p
  · left
    apply monotoneOn_of_deriv_nonneg (convex_Icc ..) ct dif
    rw [interior_Icc]
    exact fun x hx => (der x hx).deriv ▸ p x hx
  · right
    apply antitoneOn_of_deriv_nonpos (convex_Icc ..) ct dif
    rw [interior_Icc]
    exact fun x hx => (der x hx).deriv ▸ p x hx

private theorem var_join (f : ℝ → ℝ) {a c b : ℝ} (ac : a≤c) (cb : c≤b) :
    eVariationOn f (Icc a b) = eVariationOn f (Icc a c)+eVariationOn f (Icc c b) := by
  simpa using (eVariationOn.Icc_add_Icc f ac cb (Set.mem_univ c)).symm

private theorem var_inc {f : ℝ → ℝ} {a b S : ℝ} (ab : a≤b)
    (bound : ∀ x ∈ Icc a b, |f x|≤S) (inc : MonotoneOn f (Icc a b)) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (2*S) := by
  have a0 : a ∈ Icc a b := ⟨le_rfl,ab⟩
  have b0 : b ∈ Icc a b := ⟨ab,le_rfl⟩
  have eqn := inc.eVariationOn_eq a0 b0
  rw [inter_self] at eqn
  apply eqn.le.trans (ENNReal.ofReal_le_ofReal ?_)
  linarith only [(abs_le.mp (bound a a0)).1,(abs_le.mp (bound b b0)).2]

private theorem var_direction {f : ℝ → ℝ} {a b S : ℝ} (ab : a≤b)
    (bound : ∀ x ∈ Icc a b, |f x|≤S) (dir : oneDirection f a b) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (2*S) := by
  rcases dir with inc|dec
  · exact var_inc ab bound inc
  have inc : MonotoneOn (fun x => -f x) (Icc a b) := fun _ hx _ hy xy => neg_le_neg (dec hx hy xy)
  have est := var_inc ab (S:=S) (f:=fun x => -f x) (fun x hx => by simpa using bound x hx) inc
  simpa only [eVariationOn,edist_neg_neg] using est

private theorem var_if_deriv_monotone {f g : ℝ → ℝ} {a b S : ℝ} (ab : a≤b) (sp : 0≤S)
    (fct : ContinuousOn f (Icc a b)) (gct : ContinuousOn g (Icc a b))
    (der : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x)
    (dir : oneDirection g a b) (bound : ∀ x ∈ Icc a b, |f x|≤S) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (4*S) := by
  obtain ⟨c,hc,p,q⟩ := split_sign ab gct dir
  have boxL : Icc a c ⊆ Icc a b := Icc_subset_Icc_right hc.2
  have boxR : Icc c b ⊆ Icc a b := Icc_subset_Icc_left hc.1
  have L := var_direction hc.1 (fun x hx => bound x (boxL hx)) (dir_of_deriv (fct.mono boxL)
    (fun x hx => der x ⟨hx.1,hx.2.trans_le hc.2⟩) p)
  have R := var_direction hc.2 (fun x hx => bound x (boxR hx)) (dir_of_deriv (fct.mono boxR)
    (fun x hx => der x ⟨hc.1.trans_lt hx.1,hx.2⟩) q)
  rw [var_join f hc.1 hc.2,show 4*S=2*S+2*S by ring,ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add L R

/-- The analytic form of a corrected quotient cell has uniformly bounded
variation relative to its amplitude, independently of its four coefficients. -/
def cellForm (A B C D y : ℝ) := A*y*log y+B*y+C*log y+D

theorem cellForm_variation {a b S : ℝ} (ap : 0<a) (ab : a≤b) (sp : 0≤S)
    (A B C D : ℝ) (bound : ∀ x ∈ Icc a b, |cellForm A B C D x|≤S) :
    eVariationOn (cellForm A B C D) (Icc a b) ≤ ENNReal.ofReal (8*S) := by
  let f := cellForm A B C D
  let g := fun x : ℝ => A*(log x+1)+B+C/x
  let h := fun x : ℝ => A*x-C
  have fd (x : ℝ) (hp : 0<x) : HasDerivAt f (g x) x := by
    have d := ((((hasDerivAt_const x A).mul (hasDerivAt_id x)).mul (hasDerivAt_log hp.ne')).add
      ((hasDerivAt_const x B).mul (hasDerivAt_id x))).add
      ((hasDerivAt_const x C).mul (hasDerivAt_log hp.ne'))
    convert d.add_const D using 1
    all_goals first | rfl | (dsimp [f,g,cellForm]; field_simp; ring)
  have gd (x : ℝ) (hp : 0<x) : HasDerivAt g (h x/x^2) x := by
    have d := (((hasDerivAt_log hp.ne').add_const 1).const_mul A).add_const B
    convert d.add ((hasDerivAt_const x C).div (hasDerivAt_id x) hp.ne') using 1
    all_goals first | rfl | (dsimp [g,h]; field_simp; ring)
  have dir : oneDirection h a b := by
    rcases le_total 0 A with sign|sign
    · exact Or.inl fun _ _ _ _ xy => sub_le_sub_right (mul_le_mul_of_nonneg_left xy sign) _
    · exact Or.inr fun _ _ _ _ xy => sub_le_sub_right (mul_le_mul_of_nonpos_left xy sign) _
  have ct : ContinuousOn h (Icc a b) := by dsimp [h]; fun_prop
  obtain ⟨c,hc,p,q⟩ := split_sign ab ct dir
  have piece {u v : ℝ} (up : 0<u) (uv : u≤v) (inside : Icc u v ⊆ Icc a b)
      (sign : oneSign h u v) : eVariationOn f (Icc u v) ≤ ENNReal.ofReal (4*S) := by
    have h0 (x : ℝ) (hx : x ∈ Icc u v) : 0<x := up.trans_le hx.1
    have fct : ContinuousOn f (Icc u v) := fun x hx => (fd x (h0 x hx)).continuousAt.continuousWithinAt
    have gct : ContinuousOn g (Icc u v) := fun x hx => (gd x (h0 x hx)).continuousAt.continuousWithinAt
    apply var_if_deriv_monotone uv sp fct gct (fun x hx => fd x (up.trans hx.1)) _ (fun x hx => bound x (inside hx))
    apply dir_of_deriv gct (fun x hx => gd x (up.trans hx.1))
    rcases sign with pos|neg
    · exact Or.inl fun x hx => div_nonneg (pos x hx) (sq_nonneg _)
    · exact Or.inr fun x hx => div_nonpos_of_nonpos_of_nonneg (neg x hx) (sq_nonneg _)
  have L := piece ap hc.1 (Icc_subset_Icc_right hc.2) p
  have R := piece (ap.trans_le hc.1) hc.2 (Icc_subset_Icc_left hc.1) q
  change eVariationOn f _ ≤ _
  rw [var_join f hc.1 hc.2,show 8*S=4*S+4*S by ring,ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add L R

/-- A local analytic identity on each full closed cell. Coefficients can
depend on q. Agreement at integers is included to handle jump costs. -/
def HasQuotientCellForm (H : ℝ → ℝ) : Prop :=
  ∀ q : ℕ, 2≤q → ∃ A B C D : ℝ, EqOn H (cellForm A B C D) (Set.Icc (q:ℝ) (q+1))

theorem dyadic_variation_of_cells {H : ℝ → ℝ} {K : ℝ} (kp : 0≤K)
    (cells : HasQuotientCellForm H) (decay : ∀ y:ℝ, 2≤y → |H y|≤K*(1+log y)/y)
    (Q : ℕ) (hQ : 2≤Q) :
    eVariationOn H (Set.Icc (Q:ℝ) (2*Q)) ≤ ENNReal.ofReal (8*K*(1+log (2*Q))) := by
  let S := K*(1+log (2*Q))/Q
  have qr : 0<(Q:ℝ) := by exact_mod_cast (show 0<Q by omega)
  have qlower : (2:ℝ) ≤ Q := by exact_mod_cast hQ
  have lg : 0≤log (2*(Q:ℝ)) := log_nonneg (by linarith)
  have sp : 0≤S := by dsimp [S]; positivity
  have localBound (i : ℕ) (hi : i<Q) :
      eVariationOn H (Set.Icc ((Q+i:ℕ):ℝ) ((Q+i+1:ℕ):ℝ)) ≤ ENNReal.ofReal (8*S) := by
    let q := Q+i
    have hq : 2≤q := by dsimp [q]; omega
    obtain ⟨A,B,C,D,form⟩ := cells q hq
    change eVariationOn H (Set.Icc (q:ℝ) ((q+1:ℕ):ℝ)) ≤ _
    push_cast
    rw [eVariationOn.eq_of_eqOn form]
    apply cellForm_variation (by exact_mod_cast (show 0<q by omega)) (by linarith) sp
    intro x hx
    have qlow : (Q:ℝ)≤q := by exact_mod_cast (show Q≤q by dsimp [q]; omega)
    have qhigh : (q:ℝ)+1≤2*(Q:ℝ) := by exact_mod_cast (show q+1≤2*Q by dsimp [q]; omega)
    have pos := qr.trans_le (qlow.trans hx.1)
    rw [←form hx]
    apply (decay x ((show (2:ℝ)≤q by exact_mod_cast hq).trans hx.1)).trans
    apply div_le_div₀ _ _ qr (qlow.trans hx.1)
    · exact mul_nonneg kp (by linarith)
    · exact mul_le_mul_of_nonneg_left (by linarith [log_le_log pos (hx.2.trans qhigh)]) kp
  let grid : ℕ → ℝ := fun i => ((Q+i:ℕ):ℝ)
  have mono : Monotone grid := fun _ _ h => by dsimp [grid]; exact_mod_cast Nat.add_le_add_left h Q
  have sum := eVariationOn.sum' H mono (n:=Q)
  have grid0 : grid 0=(Q:ℝ) := by simp [grid]
  have gridQ : grid Q=2*(Q:ℝ) := by dsimp [grid]; push_cast; ring
  rw [grid0,gridQ] at sum
  rw [←sum]
  calc
    _ ≤ ∑ _i ∈ range Q, ENNReal.ofReal (8*S) := by
      apply sum_le_sum
      intro i hi
      simpa only [grid,←Nat.add_assoc] using localBound i (mem_range.mp hi)
    _ = ENNReal.ofReal ((Q:ℝ)*(8*S)) := by simp [ENNReal.ofReal_mul (Nat.cast_nonneg (α:=ℝ) Q)]
    _ = _ := by congr 1; dsimp [S]; field_simp

open RiemannGaussian.AlpogeMined in
def signedQuotientKernel (y : ℝ) := fixedBandCenteredKernel y - fixedBandFirstCorrection y

open RiemannGaussian.AlpogeMined in
theorem signedQuotientKernel_decay {y : ℝ} (hy : 2≤y) :
    |signedQuotientKernel y| ≤ kernelConstant*(1+log y)/y := by
  have yp : 0<y := by linarith
  have base := (abs_sub _ _).trans
    (add_le_add (fixedBandCenteredKernel_bound hy) (fixedBandFirstCorrection_decay yp))
  apply base.trans
  rw [←add_div]
  apply div_le_div_of_nonneg_right _ yp.le
  unfold kernelConstant
  nlinarith only [log_nonneg (by linarith : 1≤y)]

theorem signed_kernel_dyadic_variation (cells : HasQuotientCellForm signedQuotientKernel)
    (Q : ℕ) (hQ : 2≤Q) :
    eVariationOn signedQuotientKernel (Set.Icc (Q:ℝ) (2*Q)) ≤
      ENNReal.ofReal (8*kernelConstant*(1+log (2*Q))) :=
  dyadic_variation_of_cells kernelConstant_nonneg cells (fun _ hy => signedQuotientKernel_decay hy) Q hQ

/-- A decreasing sequence of quotient samples costs at most its two endpoint
amplitudes and one copy of the continuous variation on the enclosing band. -/
theorem endpointVariation_of_antitone {a b : ℕ} (ab : a<b) {H : ℝ → ℝ} {φ : ℕ → ℝ}
    {T : Set ℝ} {S V : ℝ} (vp : 0≤V) (anti : AntitoneOn φ (Set.Icc (a+1) b))
    (inside : MapsTo φ (Set.Icc (a+1) b) T) (amp : ∀ x ∈ T, |H x| ≤ S)
    (variation : eVariationOn H T ≤ ENNReal.ofReal V) :
    endpointVariation a b (fun k => H (φ k)) ≤ 2*S+V := by
  have left := amp _ (inside (show a+1 ∈ Set.Icc (a+1) b from ⟨le_rfl,ab⟩))
  have right := amp _ (inside (show b ∈ Set.Icc (a+1) b from ⟨ab,le_rfl⟩))
  have sample := eVariationOn.sum_le_of_monotoneOn_Icc (f:=H ∘ φ)
    (s:=Set.Icc (a+1) b) (m:=a+1) (n:=b) (u:=id) (monotone_id.monotoneOn _) (fun _ h => h)
  have full := sample.trans ((eVariationOn.comp_le_of_antitoneOn H φ anti inside).trans variation)
  have ranges : Finset.Ioc a (b-1) = Finset.Ico (a+1) b := by
    ext k
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  have cost : (∑ k ∈ Finset.Ico (a+1) b, |H (φ (k+1))-H (φ k)|) ≤ V := by
    apply (ENNReal.ofReal_le_ofReal_iff vp).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
    simpa only [id_eq,Function.comp_apply,edist_dist,Real.dist_eq] using full
  rw [endpointVariation,ranges]
  linarith only [left,right,cost]

open RiemannGaussian.AlpogeMined in
/-- On the first active unit cell the explicit quotient formula supplies
the coefficients directly, without a cell-form assumption. -/
theorem signed_kernel_variation_two_three :
    eVariationOn signedQuotientKernel (Set.Icc 2 3) ≤
      ENNReal.ofReal (4*kernelConstant*(1+log 3)) := by
  let L := 2*(1-eulerMascheroniConstant)+4*log 2+1
  have formula : EqOn signedQuotientKernel
      (cellForm (-2) (L/2+2*log 2) 3 (-L-3*log 2)) (Set.Icc 2 3) := by
    intro y hy
    have yp : 0<y := by linarith [hy.1]
    have f := fixedBandHalfKernel_second (z:=y/2) (by linarith [hy.1]) (by linarith [hy.2])
    rw [show 2*(y/2)=y by ring,log_div yp.ne' (by norm_num)] at f
    rw [signedQuotientKernel,f]
    dsimp [L,cellForm]
    ring
  let S := kernelConstant*(1+log 3)/2
  have l3 : 0≤log 3 := log_nonneg (by norm_num)
  have sp : 0≤S := by dsimp [S]; positivity [kernelConstant_nonneg]
  rw [eVariationOn.eq_of_eqOn formula]
  apply (cellForm_variation (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≤3) sp _ _ _ _ ?_).trans_eq
  · dsimp [S]
    congr 1
    ring
  · intro y hy
    rw [←formula hy]
    apply (signedQuotientKernel_decay hy.1).trans
    apply div_le_div₀ _ _ (by norm_num) hy.1
    · exact mul_nonneg kernelConstant_nonneg (by linarith)
    · exact mul_le_mul_of_nonneg_left (by linarith [log_le_log (by linarith [hy.1]) hy.2]) kernelConstant_nonneg

open RiemannGaussian.AlpogeMined

private theorem samples_in_band {n j d : ℕ}
    (hd : d ∈ Set.Icc (bandLo n j+1) (bandHi n j)) :
    ((n^4:ℕ):ℝ)/d ∈ Set.Icc ((2^j:ℕ):ℝ) (2*((2^j:ℕ):ℝ)) := by
  let Q := (2:ℕ)^j
  have qp : 0<Q := by dsimp [Q]; positivity
  have dp : 0<d := by have := hd.1; omega
  have upper : d ≤ n^4/Q := hd.2.trans (min_le_right ..)
  have lower : n^4/(Q*2) < d := by
    have h := le_max_right (max (fixedBandMultipleCutoff n) (cutoff n)) (n^4/2^(j+1))
    rw [pow_succ] at h
    exact h.trans_lt hd.1
  have hi := (Nat.le_div_iff_mul_le qp).mp upper
  have lo := (Nat.div_lt_iff_lt_mul (by positivity : 0<Q*2)).mp lower
  have dr : (0:ℝ)<d := Nat.cast_pos.mpr dp
  constructor
  · apply (le_div_iff₀ dr).mpr
    exact_mod_cast (show Q*d≤n^4 by simpa [Nat.mul_comm] using hi)
  · apply (div_le_iff₀ dr).mpr
    have less : n^4 ≤ 2*Q*d := by nlinarith only [lo.le]
    exact_mod_cast less

theorem variation_on_original_samples {n j a b : ℕ} (ab : a<b) {p : ℕ → ℕ}
    (pm : Monotone p) (source : MapsTo p (Set.Icc (a+1) b) (Set.Icc (bandLo n j+1) (bandHi n j)))
    (cells : HasQuotientCellForm signedQuotientKernel) :
    endpointVariation a b (fun k => rowWeight n (p k))
      ≤ 10*kernelConstant*(1+log (2*((2^j:ℕ):ℝ))) := by
  let Q := (2:ℕ)^j
  have jpos : 0<j := by
    by_contra! jz
    have zero : j=0 := by omega
    have h := source (show a+1 ∈ Set.Icc (a+1) b from ⟨le_rfl,ab⟩)
    rcases h with ⟨left,right⟩
    have ll : n^4/2 ≤ bandLo n 0 := le_max_right ..
    have hh : bandHi n 0 ≤ n^4/2 := min_le_left ..
    rw [zero] at left right
    omega
  have qr : 2≤Q := by
    have := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 1≤j by omega)
    simpa [Q] using this
  let φ (k : ℕ) := ((n^4:ℕ):ℝ)/(p k)
  have anti : AntitoneOn φ (Set.Icc (a+1) b) := by
    intro x hx y _ xy
    have sx := (source hx).1
    have px : 0<p x := by omega
    exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast px) (by exact_mod_cast pm xy)
  have inside : MapsTo φ (Set.Icc (a+1) b) (Set.Icc (Q:ℝ) (2*(Q:ℝ))) :=
    fun _ hk => samples_in_band (source hk)
  let W := kernelConstant*(1+log (2*(Q:ℝ)))
  have qr' : (2:ℝ)≤Q := by exact_mod_cast qr
  have lg : 0≤log (2*(Q:ℝ)) := log_nonneg (by linarith)
  have wz : 0≤W := by dsimp [W]; positivity [kernelConstant_nonneg]
  have amp (x : ℝ) (hx : x∈Set.Icc (Q:ℝ) (2*Q)) : |signedQuotientKernel x|≤W := by
    apply (signedQuotientKernel_decay (qr'.trans hx.1)).trans
    calc
      _ ≤ W/1 := by
        apply div_le_div₀ wz _ (by norm_num) (by linarith [hx.1])
        exact mul_le_mul_of_nonneg_left (by linarith [log_le_log (by linarith [hx.1]) hx.2]) kernelConstant_nonneg
      _ = _ := div_one W
  change endpointVariation a b (fun k => signedQuotientKernel (φ k)) ≤ _
  apply (endpointVariation_of_antitone ab (by positivity [kernelConstant_nonneg] : 0≤8*kernelConstant*(1+log (2*(Q:ℝ))))
    anti inside amp (signed_kernel_dyadic_variation cells Q qr)).trans_eq
  dsimp [W,Q]
  ring

/-- For any finite square-root envelope on ordinary Mertens prefixes, both
signed components are bounded on every original dyadic bin, including empty
bins. The only kernel premise is the explicit shape on closed unit cells. -/
theorem both_signed_dyadic_bounds {n j X : ℕ} {C : ℝ} (cp : 0≤C) (cap : bandHi n j ≤ X)
    (mertens : ∀ k ≤ X, |fixedBandPrefix k| ≤ C*sqrt k)
    (cells : HasQuotientCellForm signedQuotientKernel) :
    |oddSum n (quotientBandRows n 0 j)| ≤
      4*C*sqrt (bandHi n j)*(10*kernelConstant*(1+log (2*((2^j:ℕ):ℝ)))) ∧
    |cofactorSum n (quotientBandRows n 0 j)| ≤
      4*C*sqrt ((bandHi n j/2:ℕ):ℝ)*(10*kernelConstant*(1+log (2*((2^j:ℕ):ℝ)))) := by
  rw [(odd_rows_abel_input n j).1,(odd_rows_abel_input n j).2]
  have side (a b : ℕ) (p : ℕ → ℕ) (bX : b≤X) (pm : Monotone p)
      (source : MapsTo p (Set.Icc (a+1) b) (Set.Icc (bandLo n j+1) (bandHi n j))) :
      |oddWeighted a b (fun k => rowWeight n (p k))| ≤
        4*C*sqrt b*(10*kernelConstant*(1+log (2*((2^j:ℕ):ℝ)))) := by
    by_cases ab : a<b
    · have bound (k : ℕ) (hk : k≤b) : |oddPrefix k| ≤ 4*C*sqrt b :=
        (odd_prefix_sqrt cp mertens k (hk.trans bX)).trans
          (mul_le_mul_of_nonneg_left (sqrt_le_sqrt (by exact_mod_cast hk)) (by positivity))
      exact (odd_abel_bound _ (by positivity) bound).trans
        (mul_le_mul_of_nonneg_left (variation_on_original_samples ab pm source cells) (by positivity))
    · have q : (1:ℝ) ≤ ((2^j:ℕ):ℝ) := by exact_mod_cast (show 1≤(2:ℕ)^j from Nat.one_le_pow _ _ (by decide))
      have lg : 0≤log (2*((2^j:ℕ):ℝ)) := log_nonneg (by linarith)
      rw [oddWeighted,Finset.Ioc_eq_empty_of_le (by omega),sum_empty,abs_zero]
      positivity [kernelConstant_nonneg]
  constructor
  · exact side _ _ id cap monotone_id (fun _ hk => hk)
  · apply side _ _ (fun k => 2*k) ((Nat.div_le_self ..).trans cap) (fun _ _ h => Nat.mul_le_mul_left 2 h)
    intro k hk
    rcases hk with ⟨lo,hi⟩
    change bandLo n j+1 ≤ 2*k ∧ 2*k ≤ bandHi n j
    exact ⟨by omega,by omega⟩


/-- The inverse square root of the dyadic quotient from its divisor range
absorbs the logarithmic variation uniformly in the original dyadic level. -/
theorem both_signed_dyadic_uniform {n j X : ℕ} {C : ℝ} (cp : 0≤C) (cap : bandHi n j ≤ X)
    (mertens : ∀ k ≤ X, |fixedBandPrefix k| ≤ C*sqrt k)
    (cells : HasQuotientCellForm signedQuotientKernel) :
    |oddSum n (quotientBandRows n 0 j)| ≤ 80*kernelConstant*C*(n:ℝ)^2 ∧
    |cofactorSum n (quotientBandRows n 0 j)| ≤ 80*kernelConstant*C*(n:ℝ)^2 := by
  let Q := (2:ℕ)^j
  have qp : 0<Q := by dsimp [Q]; positivity
  have qR : (0:ℝ)<Q := by exact_mod_cast qp
  have logBound : 1+log (2*(Q:ℝ)) ≤ 2*sqrt Q := by
    rw [log_mul (by norm_num) qR.ne']
    have sqrtlog := log_le_sub_one_of_pos (sqrt_pos.mpr qR)
    rw [log_sqrt qR.le] at sqrtlog
    linarith only [sqrtlog,log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have size (b : ℕ) (hb : b≤bandHi n j) : sqrt b * sqrt Q ≤ (n:ℝ)^2 := by
    have product := (Nat.le_div_iff_mul_le qp).mp (hb.trans (min_le_right ..) : b≤n^4/Q)
    rw [←sqrt_mul (Nat.cast_nonneg (α:=ℝ) b),←sqrt_sq (sq_nonneg (n:ℝ))]
    apply sqrt_le_sqrt
    exact_mod_cast (show b*Q ≤ (n^2)^2 from product.trans_eq (by ring))
  have absorb (b : ℕ) (hb : b≤bandHi n j) :
      4*C*sqrt b*(10*kernelConstant*(1+log (2*(Q:ℝ)))) ≤ 80*kernelConstant*C*(n:ℝ)^2 := by
    have first := mul_le_mul_of_nonneg_left logBound
      (show 0≤4*C*sqrt b*(10*kernelConstant) by positivity [kernelConstant_nonneg])
    have second := mul_le_mul_of_nonneg_left (size b hb)
      (show 0≤80*kernelConstant*C by positivity [kernelConstant_nonneg])
    linarith only [first,second]
  obtain ⟨left,right⟩ := both_signed_dyadic_bounds cp cap mertens cells
  exact ⟨left.trans (absorb _ le_rfl),right.trans (absorb _ (Nat.div_le_self ..))⟩

end RiemannReduction.ShortTail.LossFrequency
