import IndependentLandau.Defs
import IndependentLandau.Elementary
import IndependentLandau.Series
import IndependentLandau.Kernel
import IndependentLandau.WindowCoefficients
import IndependentLandau.Poles

/-! Window form of Landau's theorem: assembly. -/

open Complex MeasureTheory Set Filter Topology Metric

noncomputable section

namespace IndependentLandau

/-- Moments at a centre `p` near a single pole `ρ₁`: `Bc g k p` equals the polar
contribution `c / (p - ρ₁) ^ (k + 1)` up to an error of rate `e' ^ (-k)`, where `e'`
is any radius below the distance from `p` to the other poles. -/
theorem pole_coeff {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {p : ℂ} (hp : 2 < p.re) {ρ₁ : ℂ} (hρ₁ : ρ₁ ∈ Z) {c : ℂ} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h ρ₁) (heq : ∀ᶠ s in 𝓝[≠] ρ₁, Φ s = c / (s - ρ₁) + h s)
    {e : ℝ} (hep : e ≤ p.re) (hgap : ∀ ρ ∈ Z, ρ ≠ ρ₁ → e ≤ dist p ρ)
    {e' : ℝ} (he' : 0 < e') (he'e : e' < e) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, ‖Bc g k p - c / (p - ρ₁) ^ (k + 1)‖ ≤ M / e' ^ k := by
  have hpρ : p ≠ ρ₁ := by
    intro hcon
    have := hP.re_le_two hρ₁
    rw [← hcon] at this
    linarith
  set H : ℂ → ℂ := Function.update (fun s => Φ s - c / (s - ρ₁)) ρ₁ (h ρ₁) with hH
  have hHne : ∀ s, s ≠ ρ₁ → H s = Φ s - c / (s - ρ₁) := fun s hs =>
    Function.update_of_ne hs _ _
  have hHself : H ρ₁ = h ρ₁ := Function.update_self _ _ _
  have hHd : ∀ s ∈ ball p e, DifferentiableAt ℂ H s := by
    intro s hs
    by_cases hsρ : s = ρ₁
    · rw [hsρ]
      have h1 : ∀ᶠ s in 𝓝 ρ₁, s ∈ ({ρ₁}ᶜ : Set ℂ) → Φ s = c / (s - ρ₁) + h s :=
        eventually_nhdsWithin_iff.1 heq
      have h2 : H =ᶠ[𝓝 ρ₁] h := by
        filter_upwards [h1] with s hs'
        by_cases hsρ' : s = ρ₁
        · rw [hsρ', hHself]
        · rw [hHne s hsρ', hs' hsρ']; ring
      exact hh.differentiableAt.congr_of_eventuallyEq h2
    · have hsZ : s ∉ Z := by
        intro hsZ
        have h1 := hgap s hsZ hsρ
        have h2 : dist s p < e := hs
        rw [dist_comm] at h2
        linarith
      have hs0 : 0 < s.re := by
        have h1 : dist s p < e := hs
        have h2 := Complex.abs_re_le_norm (s - p)
        rw [Complex.dist_eq] at h1
        rw [Complex.sub_re] at h2
        have h3 := (abs_le.1 (h2.trans h1.le)).1
        have h4 := (abs_lt.1 (h2.trans_lt h1)).1
        linarith
      have hΦ := hP.differentiableAt hs0 hsZ
      have h2 : H =ᶠ[𝓝 s] fun s => Φ s - c / (s - ρ₁) := by
        filter_upwards [isOpen_ne.mem_nhds hsρ] with s' hs'
        exact hHne s' hs'
      have h3 : DifferentiableAt ℂ (fun s => Φ s - c / (s - ρ₁)) s :=
        hΦ.sub ((differentiableAt_const c).div (differentiableAt_id.sub_const ρ₁)
          (sub_ne_zero.2 hsρ))
      exact h3.congr_of_eventuallyEq h2
  have hHt : DifferentiableOn ℂ (fun w => H (p - w)) (ball 0 e) := by
    intro w hw
    have hw' : ‖w‖ < e := mem_ball_zero_iff.1 hw
    have hmem : p - w ∈ ball p e := by
      rw [mem_ball, dist_eq_norm]
      simpa using hw'
    have h1 : DifferentiableAt ℂ (fun w : ℂ => p - w) w :=
      (differentiableAt_const p).sub differentiableAt_id
    exact (DifferentiableAt.comp w (hHd (p - w) hmem) h1).differentiableWithinAt
  have heq0 : ∀ᶠ w in 𝓝 (0 : ℂ), Φ (p - w) = H (p - w) + c / (p - ρ₁ - w) := by
    have hc : ContinuousAt (fun w : ℂ => p - w) 0 := by fun_prop
    have hne : ∀ᶠ w in 𝓝 (0 : ℂ), p - w ≠ ρ₁ := hc.eventually_ne (by simpa using hpρ)
    filter_upwards [hne] with w hw
    rw [hHne _ hw]
    have : p - ρ₁ - w = p - w - ρ₁ := by ring
    rw [this]
    ring
  exact coeff_bound0 (F := fun w => Φ (p - w)) (a := fun k => Bc g k p) (r := p.re - 2)
    (by linarith) (fun w hw => laplace_hasSum hP hw) hHt (sub_ne_zero.2 hpρ) heq0 he' he'e

/-- Lower bound for the moments forced by a pole to the right of `θ`. -/
theorem lower_bound {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {σ θ : ℝ} (hσ : 2 < σ) (hθ : 0 < θ) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z) (hρ₀θ : θ < ρ₀.re) :
    ∃ p : ℂ, p.re = σ ∧ ∃ d e₁ c₀ M : ℝ, 0 < d ∧ d < e₁ ∧ e₁ ≤ σ - θ ∧ 0 < c₀ ∧
      ∀ k : ℕ, c₀ / d ^ (k + 1) - M / e₁ ^ k ≤ ‖Bc g k p‖ + (Bc g k (σ : ℂ)).re := by
  obtain ⟨γ, ρ₁, hρ₁, e, hde, heA, hgap, hdisj⟩ :=
    pole_config hP.iso (fun ρ hρ => hP.re_le_two hρ) hσ hθ hρ₀ hρ₀θ
  obtain ⟨c, hc0, hreal, h, hh, heq⟩ := hP.pole ρ₁ hρ₁
  have hρ₁le := hP.re_le_two hρ₁
  have hpρ : Pt σ γ ≠ ρ₁ := by
    intro hcon
    have : (Pt σ γ).re = ρ₁.re := by rw [hcon]
    rw [Pt_re] at this
    linarith
  set d : ℝ := dist (Pt σ γ) ρ₁ with hd
  have hd0 : 0 < d := dist_pos.2 hpρ
  have he'0 : 0 < (d + e) / 2 := by linarith
  have he'e : (d + e) / 2 < e := by linarith
  have hde' : d < (d + e) / 2 := by linarith
  obtain ⟨M, hM0, hM⟩ := pole_coeff hP (p := Pt σ γ) (by rw [Pt_re]; exact hσ) hρ₁ hh heq
    (by rw [Pt_re]; linarith) hgap he'0 he'e
  rcases hdisj with ⟨hγ, him⟩ | ⟨e₀, hde₀, he₀A, hfar⟩
  · -- real pole seen from the real centre `σ`
    subst hγ
    rw [Pt_zero] at hM hd
    obtain ⟨hcre, hcim⟩ := hreal him
    have hdval : d = σ - ρ₁.re := by
      rw [hd, dist_ofReal_eq, him]
      have : (σ - ρ₁.re) ^ 2 + (0 : ℝ) ^ 2 = (σ - ρ₁.re) ^ 2 := by ring
      rw [this, Real.sqrt_sq (by linarith)]
    have hv : (σ : ℂ) - ρ₁ = ((d : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [hdval]
      · simp [him]
    have hcc : c = ((c.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hcim]
    refine ⟨(σ : ℂ), Complex.ofReal_re σ, d, (d + e) / 2, 2 * c.re, 2 * M, hd0, hde',
      by linarith, by linarith, fun k => ?_⟩
    have h1 := hM k
    have hx : c / ((σ : ℂ) - ρ₁) ^ (k + 1) = ((c.re / d ^ (k + 1) : ℝ) : ℂ) := by
      rw [hv]
      conv_lhs => rw [hcc]
      push_cast
      rfl
    rw [hx] at h1
    have h2 := Complex.abs_re_le_norm (Bc g k (σ : ℂ) - ((c.re / d ^ (k + 1) : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h2
    have h3 := (abs_le.1 (h2.trans h1)).1
    have h4 := Complex.re_le_norm (Bc g k (σ : ℂ))
    have h5 : 2 * c.re / d ^ (k + 1) - 2 * M / ((d + e) / 2) ^ k =
        2 * (c.re / d ^ (k + 1) - M / ((d + e) / 2) ^ k) := by ring
    rw [h5]
    linarith
  · -- complex centre: the moments at `σ` are small
    have hHt : DifferentiableOn ℂ (fun w : ℂ => Φ ((σ : ℂ) - w)) (ball 0 e₀) := by
      intro w hw
      have hw' : ‖w‖ < e₀ := mem_ball_zero_iff.1 hw
      have hdist : dist (σ : ℂ) ((σ : ℂ) - w) = ‖w‖ := by
        rw [dist_eq_norm]; simp
      have hZ : (σ : ℂ) - w ∉ Z := by
        intro hZ
        have := hfar _ hZ
        rw [hdist] at this
        linarith
      have h0 : 0 < ((σ : ℂ) - w).re := by
        have h2 := Complex.abs_re_le_norm w
        have h3 := (abs_le.1 h2).2
        rw [Complex.sub_re, Complex.ofReal_re]
        linarith
      have h1 : DifferentiableAt ℂ (fun w : ℂ => (σ : ℂ) - w) w :=
        (differentiableAt_const _).sub differentiableAt_id
      exact (DifferentiableAt.comp w (hP.differentiableAt h0 hZ) h1).differentiableWithinAt
    have he₀'0 : 0 < (d + e₀) / 2 := by linarith
    have he₀'e : (d + e₀) / 2 < e₀ := by linarith
    obtain ⟨M₀, hM₀0, hM₀⟩ := coeff_bound0 (F := fun w : ℂ => Φ ((σ : ℂ) - w))
      (a := fun k => Bc g k (σ : ℂ)) (r := σ - 2) (by linarith)
      (fun w hw => laplace_hasSum hP (p := (σ : ℂ)) (by rw [Complex.ofReal_re]; exact hw))
      hHt (c := 0) (v := 1) one_ne_zero (Eventually.of_forall fun w => by simp) he₀'0 he₀'e
    set e₁ : ℝ := min ((d + e) / 2) ((d + e₀) / 2) with he₁
    have he₁d : d < e₁ := lt_min hde' (by linarith)
    have he₁0 : 0 < e₁ := hd0.trans he₁d
    refine ⟨Pt σ γ, Pt_re σ γ, d, e₁, ‖c‖, M + M₀, hd0, he₁d,
      (min_le_left _ _).trans (by linarith), norm_pos_iff.2 hc0, fun k => ?_⟩
    have h1 := hM k
    have h2 := hM₀ k
    simp only [zero_div, sub_zero] at h2
    have hnorm : ‖c / (Pt σ γ - ρ₁) ^ (k + 1)‖ = ‖c‖ / d ^ (k + 1) := by
      rw [norm_div, norm_pow, hd, dist_eq_norm]
    have h3 := norm_sub_le (Bc g k (Pt σ γ)) (Bc g k (Pt σ γ) - c / (Pt σ γ - ρ₁) ^ (k + 1))
    rw [sub_sub_cancel, hnorm] at h3
    have h4 := (abs_le.1 (Complex.abs_re_le_norm (Bc g k (σ : ℂ)))).1
    have h5 : M / ((d + e) / 2) ^ k ≤ M / e₁ ^ k :=
      div_le_div_of_nonneg_left hM0 (pow_pos he₁0 k)
        (pow_le_pow_left₀ he₁0.le (min_le_left _ _) k)
    have h6 : M₀ / ((d + e₀) / 2) ^ k ≤ M₀ / e₁ ^ k :=
      div_le_div_of_nonneg_left hM₀0 (pow_pos he₁0 k)
        (pow_le_pow_left₀ he₁0.le (min_le_right _ _) k)
    rw [add_div]
    linarith

/-- **Window form of Landau's theorem.** -/
theorem landau_window {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
    (hP : PoleData g Φ Z) {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (hW : WindowHypU g θ δ) : ∀ ρ ∈ Z, ρ.re ≤ θ := by
  intro ρ hρ
  by_contra hcon
  have hcon' : θ < ρ.re := not_le.1 hcon
  obtain ⟨σ, hσ, C₁, hC₁, hB⟩ := window_bound hP hθ hθ1 hδ hW
  obtain ⟨p, hp, d, e₁, c₀, M, hd, hde, heA, hc₀, hlow⟩ := lower_bound hP hσ hθ hρ hcon'
  obtain ⟨η, hη, U₀, hno⟩ := no_room M hd hde hc₀ hC₁
  obtain ⟨U, hU, k, hk, hbd⟩ := hB η hη U₀
  have h1 := hbd p hp
  have h2 := hlow k
  have h3 := hno U hU k hk
  have he₁0 : 0 < e₁ := hd.trans hde
  have h4 : C₁ * Real.exp (η * U) / (σ - θ) ^ k ≤ C₁ * Real.exp (η * U) / e₁ ^ k :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos he₁0 k)
      (pow_le_pow_left₀ he₁0.le heA k)
  linarith

end IndependentLandau

#print axioms IndependentLandau.landau_window
#check @IndependentLandau.landau_window
