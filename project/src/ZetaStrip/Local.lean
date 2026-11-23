import Mathlib
import ZetaShared.Perron
import ZetaStrip.Factor

/-! Local partial fractions for the logarithmic derivative of an entire function (Landau's
lemma): on a disc, `f'/f` is the sum over the nearby zeros of `m/(s - ρ)` up to an error
controlled by the growth of `f`. -/

open Complex Set Filter Topology Metric

noncomputable section
namespace ZetaStrip

/-- A zero-free holomorphic function on a disc, bounded by `exp A` times its value at the centre,
has logarithmic derivative `O(A)` on a smaller disc. -/
theorem norm_logDeriv_le_of_bound {h : ℂ → ℂ} {c : ℂ} {ρ r A : ℝ} (hr : 0 < r) (hrρ : r < ρ)
    (hA : 0 < A) (hd : DifferentiableOn ℂ h (ball c ρ)) (hne : ∀ z ∈ ball c ρ, h z ≠ 0)
    (hb : ∀ z ∈ ball c ρ, ‖h z‖ ≤ Real.exp A * ‖h c‖) {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖deriv h z / h z‖ ≤ 8 * A * ρ / (ρ - r) ^ 2 := by
  have hρ : 0 < ρ := hr.trans hrρ
  have hρr : 0 < ρ - r := sub_pos.mpr hrρ
  have hcb : c ∈ ball c ρ := mem_ball_self hρ
  set q : ℂ → ℂ := fun z => deriv h z / h z with hq
  have hqd : DifferentiableOn ℂ q (ball c ρ) := (hd.deriv isOpen_ball).div hd hne
  obtain ⟨L, hL0, hL⟩ := (hqd.isExactOn_ball).with_val_at c 0
  have hLd : DifferentiableOn ℂ L (ball c ρ) := fun w hw =>
    (hL w hw).differentiableAt.differentiableWithinAt
  -- `h = h c * exp L` on the disc
  have hΦd : ∀ w ∈ ball c ρ, HasDerivAt (fun w => h w * Complex.exp (-L w)) 0 w := by
    intro w hw
    have h1 : HasDerivAt h (deriv h w) w :=
      (hd.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
    have h2 : HasDerivAt (fun w => Complex.exp (-L w)) (Complex.exp (-L w) * (-(q w))) w :=
      (hL w hw).neg.cexp
    refine (h1.mul h2).congr_deriv ?_
    have := hne w hw
    simp only [hq]
    field_simp
    ring
  have hΦ : ∀ w ∈ ball c ρ, h w * Complex.exp (-L w) = h c := by
    intro w hw
    have := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c ρ).isPreconnected
      (f := fun w => h w * Complex.exp (-L w))
      (fun w hw => (hΦd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hΦd w hw).deriv) hw hcb
    simpa [hL0] using this
  have hre : ∀ w ∈ ball c ρ, (L w).re ≤ A := by
    intro w hw
    have h1 : h w = h c * Complex.exp (L w) := by
      rw [← hΦ w hw, mul_assoc, ← Complex.exp_add]; simp
    have h2 := hb w hw
    rw [h1, norm_mul, Complex.norm_exp, mul_comm] at h2
    have hc0 : 0 < ‖h c‖ := norm_pos_iff.mpr (hne c hcb)
    exact Real.exp_le_exp.mp (le_of_mul_le_mul_right h2 hc0)
  -- Borel–Carathéodory
  have hBC : ∀ w ∈ closedBall c ((r + ρ) / 2), ‖L w‖ ≤ 4 * A * ρ / (ρ - r) := by
    intro w hw
    set F : ℂ → ℂ := fun v => L (c + v) with hF
    have hmem : ∀ v ∈ ball (0 : ℂ) ρ, c + v ∈ ball c ρ := by
      intro v hv
      rw [mem_ball, dist_eq_norm] at hv ⊢
      simpa using hv
    have hFd : DifferentiableOn ℂ F (ball 0 ρ) := by
      intro v hv
      have h1 : DifferentiableAt ℂ L (c + v) :=
        hLd.differentiableAt (isOpen_ball.mem_nhds (hmem v hv))
      have h2 : DifferentiableAt ℂ (fun v : ℂ => c + v) v := by fun_prop
      exact (h1.comp v h2).differentiableWithinAt
    have hmaps : MapsTo F (ball 0 ρ) {z | z.re ≤ A} := fun v hv => hre _ (hmem v hv)
    have hd' : dist w c ≤ (r + ρ) / 2 := hw
    have hw' : w - c ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball, dist_eq_norm, sub_zero, ← dist_eq_norm]; linarith
    have hBC0 := Complex.borelCaratheodory_zero hA hFd hmaps hρ hw' (by simp [hF, hL0])
    have e : F (w - c) = L w := by simp [hF]
    rw [e, ← dist_eq_norm] at hBC0
    refine hBC0.trans ?_
    have hdn : 0 ≤ dist w c := dist_nonneg
    have h1 : 0 < ρ - dist w c := by linarith
    rw [div_le_div_iff₀ h1 hρr]
    have h3 : dist w c * (ρ - r) ≤ ρ * (2 * (ρ - dist w c)) := by nlinarith
    calc 2 * A * dist w c * (ρ - r) = 2 * A * (dist w c * (ρ - r)) := by ring
      _ ≤ 2 * A * (ρ * (2 * (ρ - dist w c))) := by gcongr
      _ = 4 * A * ρ * (ρ - dist w c) := by ring
  -- Cauchy estimate
  have hzb : z ∈ ball c ρ := closedBall_subset_ball hrρ hz
  have hLz : deriv L z = q z := (hL z hzb).deriv
  have hdz : dist z c ≤ r := hz
  have hsub : closedBall z ((ρ - r) / 2) ⊆ ball c ρ := by
    intro w hw
    have h1 : dist w z ≤ (ρ - r) / 2 := hw
    have h2 := dist_triangle w z c
    rw [mem_ball]; linarith
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := (ρ - r) / 2)
    (C := 4 * A * ρ / (ρ - r)) (f := L) (by linarith) (hLd.diffContOnCl_ball hsub)
    (fun w hw => hBC w (by
      have h1 : dist w z = (ρ - r) / 2 := hw
      have h2 := dist_triangle w z c
      rw [mem_closedBall]; linarith))
  rw [hLz] at hC
  refine hC.trans (le_of_eq ?_)
  field_simp
  ring

/-- **Landau's lemma.** Local partial fractions for the logarithmic derivative of an entire
function with controlled growth on a disc. -/
theorem exists_logDeriv_approx {r R₁ R : ℝ} (hr : 0 < r) (hrR₁ : r < R₁) (hR₁R : R₁ < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℂ → ℂ) (c : ℂ) (A : ℝ), Differentiable ℂ f → f c ≠ 0 → 0 < A →
      1 ≤ Real.exp A * ‖f c‖ →
      (∀ z ∈ sphere c R, ‖f z‖ ≤ Real.exp A * ‖f c‖) →
      ∃ S : Finset ℂ,
        (∀ u ∈ S, u ∈ closedBall c R₁ ∧ f u = 0 ∧ 1 ≤ analyticOrderNatAt f u) ∧
        (∀ z ∈ closedBall c R₁, f z = 0 → z ∈ S) ∧
        ((∑ u ∈ S, analyticOrderNatAt f u : ℕ) : ℝ) ≤ A / Real.log (R / R₁) ∧
        ∀ z ∈ closedBall c r, f z ≠ 0 →
          ‖deriv f z / f z - ∑ u ∈ S, (analyticOrderNatAt f u : ℂ) / (z - u)‖ ≤ K * A := by
  classical
  have hR₁ : 0 < R₁ := hr.trans hrR₁
  have hR : 0 < R := hR₁.trans hR₁R
  have hRR₁ : 0 < R - R₁ := sub_pos.mpr hR₁R
  have hR₁r : 0 < R₁ - r := sub_pos.mpr hrR₁
  have hlog : 0 < Real.log (R / R₁) := Real.log_pos ((one_lt_div hR₁).mpr hR₁R)
  set q : ℝ := R₁ / (R - R₁) with hq
  have hq0 : 0 < q := div_pos hR₁ hRR₁
  set B : ℝ := 1 + |Real.log q| / Real.log (R / R₁) with hB
  have hB0 : 0 < B := by positivity
  refine ⟨8 * B * R₁ / (R₁ - r) ^ 2, by positivity, ?_⟩
  intro f c A hf hc hA hM1 hb
  obtain ⟨S₀, g, hS₀, hg, hgne, hfac⟩ := exists_factorization hf hc (R + 1)
  set m : ℂ → ℕ := fun u => analyticOrderNatAt f u with hm
  set S := S₀.filter (fun u => u ∈ closedBall c R₁) with hS
  set S₂ := S₀.filter (fun u => ¬ u ∈ closedBall c R₁) with hS₂
  set P₁ : ℂ → ℂ := fun z => ∏ u ∈ S, (z - u) ^ m u with hP₁
  set P₂ : ℂ → ℂ := fun z => ∏ u ∈ S₂, (z - u) ^ m u with hP₂
  set G : ℂ → ℂ := fun z => P₂ z * g z with hG
  have hsub : closedBall c R ⊆ ball c (R + 1) := closedBall_subset_ball (by linarith)
  have hfG : ∀ z ∈ ball c (R + 1), f z = P₁ z * G z := by
    intro z hz
    rw [hfac z hz, ← Finset.prod_filter_mul_prod_filter_not S₀ (fun u => u ∈ closedBall c R₁)]
    simp only [hG, hP₁, hP₂, hS, hS₂, hm]
    ring
  have hSmem : ∀ u ∈ S, u ∈ closedBall c R₁ := fun u hu => (Finset.mem_filter.mp hu).2
  have hSm : ∀ u ∈ S, 1 ≤ m u := fun u hu =>
    Nat.one_le_iff_ne_zero.mpr (hS₀ u (Finset.mem_filter.mp hu).1)
  have hP₁d : Differentiable ℂ P₁ := by
    simp only [hP₁]; fun_prop
  have hP₂d : Differentiable ℂ P₂ := by
    simp only [hP₂]; fun_prop
  have hGd : DifferentiableOn ℂ G (ball c (R + 1)) :=
    hP₂d.differentiableOn.mul (hg.differentiableOn.mono ball_subset_closedBall)
  have hP₂ne : ∀ z ∈ closedBall c R₁, P₂ z ≠ 0 := by
    intro z hz
    simp only [hP₂]
    refine Finset.prod_ne_zero_iff.mpr fun u hu => pow_ne_zero _ (sub_ne_zero.mpr ?_)
    rintro rfl
    exact (Finset.mem_filter.mp hu).2 hz
  have hGne : ∀ z ∈ closedBall c R₁, G z ≠ 0 := fun z hz =>
    mul_ne_zero (hP₂ne z hz) (hgne z (closedBall_subset_closedBall (by linarith) hz))
  set n : ℕ := ∑ u ∈ S, m u with hn
  have hcount : (n : ℝ) ≤ A / Real.log (R / R₁) := by
    have h := sum_orderNat_le hf hc hR₁ hR₁R hM1 hb S hSmem
    rwa [mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hc), Real.log_exp] at h
  have hP₁norm : ∀ z, ‖P₁ z‖ = ∏ u ∈ S, ‖z - u‖ ^ m u := fun z => by
    simp only [hP₁, norm_prod, norm_pow]
  have hP₁low : ∀ z ∈ sphere c R, (R - R₁) ^ n ≤ ‖P₁ z‖ := by
    intro z hz
    rw [hP₁norm, hn, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun u _ => by positivity) fun u hu => ?_
    refine pow_le_pow_left₀ hRR₁.le ?_ _
    have h1 : dist z c = R := hz
    have h2 : dist u c ≤ R₁ := hSmem u hu
    have h3 := dist_triangle z u c
    rw [← dist_eq_norm]; linarith
  have hP₁c : ‖P₁ c‖ ≤ R₁ ^ n := by
    rw [hP₁norm, hn, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun u _ => by positivity) fun u hu => ?_
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    have h2 : dist u c ≤ R₁ := hSmem u hu
    rw [← dist_eq_norm, dist_comm]; exact h2
  set A' : ℝ := A + n * |Real.log q| with hA'
  have hA'0 : 0 < A' := by positivity
  have hcB : c ∈ ball c (R + 1) := mem_ball_self (by linarith)
  have hqn : q ^ n ≤ Real.exp (n * |Real.log q|) := by
    have e : q ^ n = Real.exp (n * Real.log q) := by
      rw [mul_comm, Real.exp_mul, Real.exp_log hq0, Real.rpow_natCast]
    rw [e]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg n))
  have hGsph : ∀ z ∈ sphere c R, ‖G z‖ ≤ Real.exp A' * ‖G c‖ := by
    intro z hz
    have hzB : z ∈ ball c (R + 1) := hsub (sphere_subset_closedBall hz)
    have hlow := hP₁low z hz
    have hpos : 0 < (R - R₁) ^ n := pow_pos hRR₁ n
    have h1 : ‖f z‖ = ‖P₁ z‖ * ‖G z‖ := by rw [hfG z hzB, norm_mul]
    have h2 : ‖f c‖ = ‖P₁ c‖ * ‖G c‖ := by rw [hfG c hcB, norm_mul]
    have h3 := hb z hz
    have h4 : (R - R₁) ^ n * ‖G z‖ ≤ Real.exp A * (R₁ ^ n * ‖G c‖) := by
      calc (R - R₁) ^ n * ‖G z‖ ≤ ‖P₁ z‖ * ‖G z‖ := by gcongr
        _ = ‖f z‖ := h1.symm
        _ ≤ Real.exp A * ‖f c‖ := h3
        _ = Real.exp A * (‖P₁ c‖ * ‖G c‖) := by rw [h2]
        _ ≤ Real.exp A * (R₁ ^ n * ‖G c‖) := by gcongr
    have h5 : R₁ ^ n = q ^ n * (R - R₁) ^ n := by
      rw [hq, div_pow, div_mul_cancel₀ _ hpos.ne']
    have h6 : ‖G z‖ ≤ Real.exp A * q ^ n * ‖G c‖ := by
      rw [h5] at h4
      have h7 : (R - R₁) ^ n * ‖G z‖ ≤ (R - R₁) ^ n * (Real.exp A * q ^ n * ‖G c‖) :=
        h4.trans (le_of_eq (by ring))
      exact le_of_mul_le_mul_left h7 hpos
    calc ‖G z‖ ≤ Real.exp A * q ^ n * ‖G c‖ := h6
      _ ≤ Real.exp A * Real.exp (n * |Real.log q|) * ‖G c‖ := by gcongr
      _ = Real.exp A' * ‖G c‖ := by rw [hA', Real.exp_add]
  have hGball : ∀ z ∈ closedBall c R, ‖G z‖ ≤ Real.exp A' * ‖G c‖ := by
    intro z hz
    have hdc : DiffContOnCl ℂ G (ball c R) := hGd.diffContOnCl_ball hsub
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_ ?_
    · rw [frontier_ball c hR.ne']; exact hGsph
    · rw [closure_ball c hR.ne']; exact hz
  have hBC : ∀ z ∈ closedBall c r, ‖deriv G z / G z‖ ≤ 8 * A' * R₁ / (R₁ - r) ^ 2 := fun z hz =>
    norm_logDeriv_le_of_bound hr hrR₁ hA'0 (hGd.mono (ball_subset_ball (by linarith)))
      (fun w hw => hGne w (ball_subset_closedBall hw))
      (fun w hw => hGball w (closedBall_subset_closedBall hR₁R.le (ball_subset_closedBall hw))) hz
  have hA'B : A' ≤ B * A := by
    have h1 : (n : ℝ) * |Real.log q| ≤ A / Real.log (R / R₁) * |Real.log q| := by gcongr
    calc A' = A + n * |Real.log q| := hA'
      _ ≤ A + A / Real.log (R / R₁) * |Real.log q| := by linarith
      _ = B * A := by rw [hB]; ring
  refine ⟨S, fun u hu => ⟨hSmem u hu,
    eq_zero_of_orderNat_ne_zero hf (hS₀ u (Finset.mem_filter.mp hu).1), hSm u hu⟩, ?_, hcount, ?_⟩
  · intro z hz hfz
    have hzB : z ∈ ball c (R + 1) := hsub (closedBall_subset_closedBall hR₁R.le hz)
    have h1 := hfG z hzB
    rw [hfz] at h1
    have hP0 : P₁ z = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h (hGne z hz)
    obtain ⟨u, hu, hu0⟩ := Finset.prod_eq_zero_iff.mp hP0
    have hzu : z = u :=
      sub_eq_zero.mp ((pow_eq_zero_iff (Nat.one_le_iff_ne_zero.mp (hSm u hu))).mp hu0)
    rw [hzu]; exact hu
  · intro z hz hfz
    have hzR₁ : z ∈ closedBall c R₁ := closedBall_subset_closedBall hrR₁.le hz
    have hzB : z ∈ ball c (R + 1) := hsub (closedBall_subset_closedBall hR₁R.le hzR₁)
    have hfz' : f z = P₁ z * G z := hfG z hzB
    have hP₁z : P₁ z ≠ 0 := fun h => hfz (by rw [hfz', h, zero_mul])
    have hGz : G z ≠ 0 := hGne z hzR₁
    have hGdz : DifferentiableAt ℂ G z := hGd.differentiableAt (isOpen_ball.mem_nhds hzB)
    have hev : f =ᶠ[𝓝 z] fun w => P₁ w * G w := by
      filter_upwards [isOpen_ball.mem_nhds hzB] with w hw using hfG w hw
    have hfac_ne : ∀ u ∈ S, z - u ≠ 0 := by
      intro u hu h
      apply hP₁z
      simp only [hP₁]
      exact Finset.prod_eq_zero hu (by rw [h, zero_pow (Nat.one_le_iff_ne_zero.mp (hSm u hu))])
    have hlogP : logDeriv P₁ z = ∑ u ∈ S, (m u : ℂ) / (z - u) := by
      have h := logDeriv_prod (s := S) (f := fun u w => (w - u) ^ m u) (x := z)
        (fun u hu => pow_ne_zero _ (hfac_ne u hu)) (fun u hu => by fun_prop)
      rw [show P₁ = fun w => ∏ u ∈ S, (w - u) ^ m u from rfl, h]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply]
      have e : deriv (fun w : ℂ => w - u) z = 1 := by simp
      rw [e]; ring
    have hmain : deriv f z / f z = (∑ u ∈ S, (m u : ℂ) / (z - u)) + deriv G z / G z := by
      have e : deriv f z / f z = logDeriv (fun w => P₁ w * G w) z := by
        rw [logDeriv_apply, hev.deriv_eq, hfz']
      rw [e, logDeriv_mul z hP₁z hGz hP₁d.differentiableAt hGdz, hlogP, logDeriv_apply]
    rw [hmain, add_sub_cancel_left]
    calc ‖deriv G z / G z‖ ≤ 8 * A' * R₁ / (R₁ - r) ^ 2 := hBC z hz
      _ ≤ 8 * (B * A) * R₁ / (R₁ - r) ^ 2 := by gcongr
      _ = 8 * B * R₁ / (R₁ - r) ^ 2 * A := by ring

end ZetaStrip
