import Mathlib
import ZetaShared.Perron

/-! Zeros of an entire function in a disc: factorisation `f = ∏ (z - u)^{m u} · g` with `g`
zero-free, and Jensen's bound for the number of zeros. -/

open Complex Set Filter Topology Metric

noncomputable section
namespace ZetaStrip

lemma enat_map_untop₀ (n : ℕ∞) : ((n.map (Nat.cast : ℕ → ℤ)).untop₀ : ℤ) = (n.toNat : ℤ) := by
  induction n using ENat.recTopCoe <;> simp

lemma divisor_eq_orderNat {f : ℂ → ℂ} {U : Set ℂ} (hA : AnalyticOnNhd ℂ f U) {z : ℂ}
    (hz : z ∈ U) : MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hA hz, enat_map_untop₀]; rfl

lemma analyticOrderAt_ne_top_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ}
    (hc : f c ≠ 0) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  intro h
  rw [AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (fun w => hf.analyticAt w)] at h
  exact hc (by rw [h]; rfl)

lemma eq_zero_of_orderNat_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {u : ℂ}
    (h : analyticOrderNatAt f u ≠ 0) : f u = 0 := by
  by_contra hne
  apply h
  unfold analyticOrderNatAt
  rw [(hf.analyticAt u).analyticOrderAt_eq_zero.mpr hne]; rfl

/-- Factorisation of an entire function on a disc. -/
theorem exists_factorization {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} (hc : f c ≠ 0)
    (R : ℝ) :
    ∃ (S : Finset ℂ) (g : ℂ → ℂ),
      (∀ u ∈ S, analyticOrderNatAt f u ≠ 0) ∧
      AnalyticOnNhd ℂ g (closedBall c R) ∧
      (∀ z ∈ closedBall c R, g z ≠ 0) ∧
      (∀ z ∈ ball c R, f z = (∏ u ∈ S, (z - u) ^ analyticOrderNatAt f u) * g z) := by
  classical
  set U : Set ℂ := closedBall c R with hU
  have hA : AnalyticOnNhd ℂ f U := fun z _ => hf.analyticAt z
  set D := MeromorphicOn.divisor f U with hD
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  have h₂ : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    rw [(hA u u.2).meromorphicOrderAt_eq]
    intro h
    exact analyticOrderAt_ne_top_of_entire hf hc u (ENat.map_eq_top_iff.mp h)
  obtain ⟨g, hg, hgne, heq⟩ := hA.meromorphicOn.extract_zeros_poles h₂ hfin
  have hDS : ∀ u ∈ hfin.toFinset, D u = (analyticOrderNatAt f u : ℤ) := by
    intro u hu
    have huU : u ∈ U := D.supportWithinDomain (hfin.mem_toFinset.mp hu)
    exact divisor_eq_orderNat hA huU
  have hφ : ∀ z : ℂ, (∏ᶠ u, (· - u) ^ D u) z =
      ∏ u ∈ hfin.toFinset, (z - u) ^ analyticOrderNatAt f u := by
    intro z
    rw [Function.FactorizedRational.finprod_eq_fun hfin]
    show ∏ᶠ u, (z - u) ^ D u = _
    rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset)]
    · refine Finset.prod_congr rfl fun u hu => ?_
      rw [hDS u hu, zpow_natCast]
    · intro u hu
      simp only [Function.mem_mulSupport, ne_eq] at hu
      simp only [Set.Finite.coe_toFinset, Function.mem_support, ne_eq]
      intro h0
      exact hu (by rw [h0, zpow_zero])
  refine ⟨hfin.toFinset, g, ?_, hg, fun z hz => hgne ⟨z, hz⟩, ?_⟩
  · intro u hu
    have h1 : D u ≠ 0 := hfin.mem_toFinset.mp hu
    rw [hDS u hu] at h1
    exact_mod_cast h1
  · intro z hz
    have hzU : z ∈ U := ball_subset_closedBall hz
    have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp heq) z hzU
    have hball : ball c R ∈ 𝓝[≠] z := nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)
    have hev : f =ᶠ[𝓝[≠] z] fun w => (∏ u ∈ hfin.toFinset, (w - u) ^ analyticOrderNatAt f u) * g w := by
      filter_upwards [h1, hball] with w hw hwb
      rcases hw with hw | hw
      · have : f w = ((∏ᶠ u, (· - u) ^ D u) • g) w := hw
        rw [this, Pi.smul_apply', hφ, smul_eq_mul]
      · exact absurd (ball_subset_closedBall hwb) hw
    have hcf : ContinuousAt f z := hf.continuous.continuousAt
    have hcg : ContinuousAt
        (fun w => (∏ u ∈ hfin.toFinset, (w - u) ^ analyticOrderNatAt f u) * g w) z := by
      refine ContinuousAt.mul ?_ (hg z hzU).continuousAt
      exact (continuous_finsetProd _ fun u _ => (continuous_id.sub continuous_const).pow _).continuousAt
    exact ((hcf.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcg).mp hev).self_of_nhds

/-- Jensen's bound for the number of zeros, with multiplicity, in a smaller disc. -/
theorem sum_orderNat_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} (hc : f c ≠ 0)
    {R₁ R M : ℝ} (hR₁ : 0 < R₁) (hR : R₁ < R) (hM : 1 ≤ M)
    (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (S : Finset ℂ) (hS : ∀ u ∈ S, u ∈ closedBall c R₁) :
    ((∑ u ∈ S, analyticOrderNatAt f u : ℕ) : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log (R / R₁) := by
  classical
  have e1 : |R₁| = R₁ := abs_of_pos hR₁
  have e2 : |R| = R := abs_of_pos (hR₁.trans hR)
  have hA : AnalyticOnNhd ℂ f (closedBall c |R|) := fun z _ => hf.analyticAt z
  have hA₁ : AnalyticOnNhd ℂ f (closedBall c |R₁|) := fun z _ => hf.analyticAt z
  have jensen := AnalyticOnNhd.sum_divisor_le (c := c) (r := R₁) (R := R) (M := M) (f := f)
    (by rw [e1]; exact hR₁) (by rw [e1, e2]; exact hR) hM hA hc (by rw [e2]; exact hb)
  set D := MeromorphicOn.divisor f (closedBall c |R₁|) with hD
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hDnn : ∀ u, 0 ≤ D u := fun u => (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hA₁) u
  have hsum : ∑ᶠ u, D u = ∑ u ∈ S ∪ hfin.toFinset, D u :=
    finsum_eq_sum_of_support_subset _ (by
      intro u hu
      simp only [Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
      exact Or.inr hu)
  have hle : (∑ u ∈ S, (analyticOrderNatAt f u : ℤ)) ≤ ∑ᶠ u, D u := by
    rw [hsum]
    calc (∑ u ∈ S, (analyticOrderNatAt f u : ℤ)) = ∑ u ∈ S, D u :=
          Finset.sum_congr rfl fun u hu => by
            rw [hD, divisor_eq_orderNat hA₁ (by rw [e1]; exact hS u hu)]
      _ ≤ ∑ u ∈ S ∪ hfin.toFinset, D u :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun u _ _ => hDnn u
  have hcast : ((∑ u ∈ S, analyticOrderNatAt f u : ℕ) : ℝ) ≤ ((∑ᶠ u, D u : ℤ) : ℝ) := by
    have : ((∑ u ∈ S, analyticOrderNatAt f u : ℕ) : ℝ) =
        ((∑ u ∈ S, (analyticOrderNatAt f u : ℤ) : ℤ) : ℝ) := by push_cast; rfl
    rw [this]
    exact_mod_cast hle
  exact hcast.trans jensen

end ZetaStrip
