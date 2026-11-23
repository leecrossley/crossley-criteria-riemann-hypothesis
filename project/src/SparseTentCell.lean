import PrimeCentreCells

open Finset Set
noncomputable section
namespace PrimeCentreMean.Sparse

private def primesTo (B : ℕ) := (range (B+1)).filter Nat.Prime

private theorem common_sum {x : ℝ} {B : ℕ} (leB : x ≤ B) :
    ThetaTransfer.primeSum (x/4) =
      ∑ p ∈ primesTo B, Real.log p * ThetaTransfer.tent (x/4/p) := by
  unfold ThetaTransfer.primeSum primesTo
  rw [show 4*(x/4)=x by ring]
  apply sum_subset_zero_on_sdiff
  · apply filter_subset_filter
    apply range_mono
    have h := Nat.floor_mono leB
    simpa using Nat.succ_le_succ h
  · intro p hp
    obtain ⟨mem,outside⟩ := mem_sdiff.mp hp
    have prim := (mem_filter.mp mem).2
    have low : ⌊x⌋₊ < p := by
      by_contra! h
      exact outside (mem_filter.mpr ⟨mem_range.mpr (by omega),prim⟩)
    have px := (Nat.floor_lt' prim.ne_zero).mp low
    have pp : 0 < (p:ℝ) := by exact_mod_cast prim.pos
    have z : x/4/p < 1/4 := (div_lt_iff₀ pp).mpr (by linarith)
    rw [ThetaTransfer.tent_pieces, if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), mul_zero]
  · intro _ _; rfl

private def hinge (k u : ℝ) := max (k*u-1) 0

/-- Only the negative middle hinge can lift a tent above its chord. -/
private theorem tent_chord {u v c d : ℝ} (uv : u ≤ v) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (sum : c+d=1) : ThetaTransfer.tent (c*u+d*v) ≤
    c*ThetaTransfer.tent u+d*ThetaTransfer.tent v+
      (if 2*u<1 ∧ 1<2*v then 3*(2*v-2*u) else 0) := by
  have affine (k : ℝ) : k*(c*u+d*v)-1 = c*(k*u-1)+d*(k*v-1) := by
    linarith only [sum]
  have upper (k : ℝ) : hinge k (c*u+d*v) ≤ c*hinge k u+d*hinge k v := by
    unfold hinge
    rw [affine]
    apply max_le
    · gcongr <;> exact le_max_left _ _
    · positivity
  have middle : c*hinge 2 u+d*hinge 2 v - hinge 2 (c*u+d*v) ≤
      if 2*u<1 ∧ 1<2*v then 2*v-2*u else 0 := by
    unfold hinge
    rw [affine]
    by_cases hit : 2*u<1 ∧ 1<2*v
    · rw [if_pos hit, max_eq_right (by linarith [hit.1]),max_eq_left (by linarith [hit.2]),mul_zero,zero_add]
      have ha := le_max_right (c*(2*u-1)+d*(2*v-1)) 0
      have h := mul_le_mul_of_nonneg_right (show d≤1 by linarith) (sub_nonneg.mpr hit.2.le)
      linarith only [ha,h,hit.1]
    · rw [if_neg hit]
      by_cases a : 1≤2*u
      · have b : 1≤2*v := by linarith
        rw [max_eq_left (sub_nonneg.mpr a),max_eq_left (sub_nonneg.mpr b),
          max_eq_left (add_nonneg (mul_nonneg hc (sub_nonneg.mpr a)) (mul_nonneg hd (sub_nonneg.mpr b)))]
        linarith
      · have b : 2*v≤1 := le_of_not_gt (fun h => hit ⟨lt_of_not_ge a,h⟩)
        rw [max_eq_right (sub_nonpos.mpr (lt_of_not_ge a).le),max_eq_right (sub_nonpos.mpr b),
          max_eq_right (add_nonpos (mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr (lt_of_not_ge a).le))
            (mul_nonpos_of_nonneg_of_nonpos hd (sub_nonpos.mpr b)))]
        simp
  have h4 := upper 4
  have h1 := upper 1
  simp only [hinge,one_mul] at h4 h1 middle
  unfold ThetaTransfer.tent
  split_ifs at middle ⊢ <;> linarith only [middle,h4,h1]

private def centresInside (A B : ℕ) := (primesTo B).filter (fun p => A<2*p ∧ 2*p<B)

private theorem count_centres (A B : ℕ) : (centresInside A B).card ≤ B-A := by
  have bound : (centresInside A B).image (fun p => 2*p) ⊆ Finset.Ioc A B := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    obtain ⟨_,l,r⟩ := mem_filter.mp hp
    exact Finset.mem_Ioc.mpr ⟨l,r.le⟩
  have inj : Function.Injective (fun p : ℕ => 2*p) := by
    intro p q h
    change 2*p=2*q at h
    omega
  simpa only [Finset.card_image_of_injective _ inj, Nat.card_Ioc] using Finset.card_le_card bound

private theorem atom {A B p : ℕ} (ap : 0<A) (ab : A≤B) (prim : p.Prime) (pb : p≤B)
    {c d : ℝ} (hc : 0≤c) (hd : 0≤d) (one : c+d=1) :
    Real.log p*ThetaTransfer.tent ((c*A+d*B)/4/p) ≤
      c*(Real.log p*ThetaTransfer.tent ((A:ℝ)/4/p))+
      d*(Real.log p*ThetaTransfer.tent ((B:ℝ)/4/p))+
      (if A<2*p ∧ 2*p<B then 3*Real.log B*((B:ℝ)-A)/A else 0) := by
  have a0 : 0<(A:ℝ) := by exact_mod_cast ap
  have pp : 0<(p:ℝ) := by exact_mod_cast prim.pos
  have order : (A:ℝ)≤B := by exact_mod_cast ab
  have pos := Real.log_nonneg (show 1≤(p:ℝ) by exact_mod_cast prim.one_le)
  have phi (z : ℝ) : 2*(z/4/p)=z/(2*p) := by ring
  have corner : 2*((A:ℝ)/4/p)<1 ∧ 1<2*((B:ℝ)/4/p) ↔ A<2*p ∧ 2*p<B := by
    rw [phi,phi,div_lt_one (by positivity), one_lt_div (by positivity)]
    norm_cast
  have h := mul_le_mul_of_nonneg_left (tent_chord (u := (A:ℝ)/4/p) (v := (B:ℝ)/4/p)
    (by gcongr) hc hd one) pos
  rw [show (c*(A:ℝ)+d*B)/4/p = c*((A:ℝ)/4/p)+d*((B:ℝ)/4/p) by ring]
  by_cases hit : A<2*p ∧ 2*p<B
  · rw [if_pos (corner.mpr hit)] at h
    rw [if_pos hit]
    have two : (A:ℝ)≤2*p := by exact_mod_cast hit.1.le
    have rat : ((B:ℝ)-A)/(2*p) ≤ ((B:ℝ)-A)/A :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr order) a0 two
    have logle := Real.log_le_log pp (show (p:ℝ)≤B by exact_mod_cast pb)
    have cost := mul_le_mul logle rat (div_nonneg (sub_nonneg.mpr order) (by positivity)) (pos.trans logle)
    have dEq : 2*((B:ℝ)/4/p)-2*((A:ℝ)/4/p)=((B:ℝ)-A)/(2*p) := by ring
    rw [dEq] at h
    rw [show 3*Real.log B*((B:ℝ)-A)/A=3*(Real.log B*(((B:ℝ)-A)/A)) by ring]
    calc
      _ ≤ _ := h
      _ = c*(Real.log p*ThetaTransfer.tent ((A:ℝ)/4/p))+
          d*(Real.log p*ThetaTransfer.tent ((B:ℝ)/4/p))+
          3*(Real.log p*(((B:ℝ)-A)/(2*p))) := by ring
      _ ≤ _ := by gcongr
  · rw [if_neg (fun h => hit (corner.mp h))] at h
    rw [if_neg hit]
    linarith only [h]

/-- Uniform interpolation for the actual ordinary-prime tent. The only unobserved
negative slope changes are at the distinct integers 2p strictly inside the cell. -/
theorem cell {A B : ℕ} (ap : 0<A) (ab : A<B) {x : ℝ} (hx : x∈Set.Icc (A:ℝ) B) :
    excess x ≤ max (excess A) (excess B) + 3*Real.log B*((B:ℝ)-A)^2/A := by
  have a0 : 0<(A:ℝ) := by exact_mod_cast ap
  have b1 : 1≤(B:ℝ) := by exact_mod_cast (show 1≤B by omega)
  have lpos := Real.log_nonneg b1
  have ab' : (A:ℝ)<B := by exact_mod_cast ab
  have hpos := sub_pos.mpr ab'
  let c := ((B:ℝ)-x)/(B-A)
  let d := (x-(A:ℝ))/(B-A)
  have hc : 0≤c := div_nonneg (sub_nonneg.mpr hx.2) hpos.le
  have hd : 0≤d := div_nonneg (sub_nonneg.mpr hx.1) hpos.le
  have total : c+d=1 := by dsimp [c,d]; field_simp; ring
  have mix : c*A+d*B=x := by dsimp [c,d]; field_simp; ring
  let cost := 3*Real.log B*((B:ℝ)-A)/A
  have cost0 : 0≤cost := by dsimp [cost]; positivity
  have summed := sum_le_sum (s := primesTo B) (fun p hp =>
    atom ap ab.le (mem_filter.mp hp).2 (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hp).1))
      hc hd total)
  rw [mix] at summed
  simp only [sum_add_distrib, ← mul_sum, ← common_sum hx.2, ← common_sum ab'.le,
    ← common_sum (le_rfl : (B:ℝ)≤B)] at summed
  have count : (∑ p ∈ primesTo B, if A<2*p ∧ 2*p<B then cost else 0) =
      ((centresInside A B).card : ℝ)*cost := by
    rw [← sum_filter]
    simp [centresInside, nsmul_eq_mul]
  have cap : ((centresInside A B).card : ℝ) ≤ (B:ℝ)-A := by
    rw [← Nat.cast_sub ab.le]
    exact_mod_cast count_centres A B
  have charge := mul_le_mul_of_nonneg_right cap cost0
  have eq : ((B:ℝ)-A)*cost=3*Real.log B*((B:ℝ)-A)^2/A := by dsimp [cost]; ring
  rw [eq] at charge
  change _ ≤ _ + _ + (∑ p ∈ primesTo B, if A<2*p ∧ 2*p<B then cost else 0) at summed
  rw [count] at summed
  have ends (a : ℝ) : ThetaTransfer.primeSum (a/4)-a/2*Real.log 2 ≤ excess a := le_max_right _ _
  have left := (ends A).trans (le_max_left (excess A) (excess B))
  have right := (ends B).trans (le_max_right (excess A) (excess B))
  have cent : c*((A:ℝ)/2*Real.log 2)+d*((B:ℝ)/2*Real.log 2)=x/2*Real.log 2 := by rw [← mix]; ring
  have same (v : ℝ) : c*v+d*v=v := by rw [← add_mul,total,one_mul]
  change max 0 (ThetaTransfer.primeSum (x/4)-x/2*Real.log 2) ≤ max (excess A) (excess B) + _
  apply max_le
  · have e0 : 0 ≤ max (excess A) (excess B) := (le_max_left 0 _).trans (le_max_left _ _)
    exact add_nonneg e0 (by positivity)
  · linarith only [summed,charge,mul_le_mul_of_nonneg_left left hc,mul_le_mul_of_nonneg_left right hd,
      cent,same (max (excess A) (excess B))]

end PrimeCentreMean.Sparse
