import IndependentLandau.Elementary

/-! Geometry of a locally finite pole set `Z` seen from the vertical line `re s = σ`:
existence of a centre on that line with a unique nearest pole. -/

open Complex Set Filter Topology Metric

noncomputable section

namespace IndependentLandau

/-- The point `σ + iγ`. -/
def Pt (σ γ : ℝ) : ℂ := (σ : ℂ) + (γ : ℂ) * I

@[simp] theorem Pt_re (σ γ : ℝ) : (Pt σ γ).re = σ := by simp [Pt]

@[simp] theorem Pt_im (σ γ : ℝ) : (Pt σ γ).im = γ := by simp [Pt]

theorem Pt_zero (σ : ℝ) : Pt σ 0 = (σ : ℂ) := by simp [Pt]

theorem dist_Pt (σ γ : ℝ) (ρ : ℂ) :
    dist (Pt σ γ) ρ = Real.sqrt ((σ - ρ.re) ^ 2 + (γ - ρ.im) ^ 2) := by
  rw [Complex.dist_eq_re_im, Pt_re, Pt_im]

theorem dist_Pt_Pt (σ γ' γ : ℝ) : dist (Pt σ γ') (Pt σ γ) = |γ' - γ| := by
  rw [dist_Pt, Pt_re, Pt_im, sub_self]
  simp [Real.sqrt_sq_eq_abs]

theorem dist_Pt_self_im (σ : ℝ) (ρ : ℂ) : dist (Pt σ ρ.im) ρ = |σ - ρ.re| := by
  rw [dist_Pt, sub_self]
  simp [Real.sqrt_sq_eq_abs]

theorem dist_Pt_le (σ γ' γ : ℝ) (ρ : ℂ) : dist (Pt σ γ') ρ ≤ dist (Pt σ γ) ρ + |γ' - γ| := by
  have := dist_triangle (Pt σ γ') (Pt σ γ) ρ
  rw [dist_Pt_Pt] at this
  linarith

/-- A locally finite set in the right half plane meets a closed disc inside that half
plane in a finite set. -/
theorem finite_inter_closedBall {Z : Set ℂ}
    (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {c : ℂ} {r : ℝ} (hr : r < c.re) :
    (Z ∩ closedBall c r).Finite := by
  by_contra hfin
  have hinf : (Z ∩ closedBall c r).Infinite := hfin
  obtain ⟨x, hxK, hacc⟩ :=
    hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall c r) inter_subset_right
  have hx : 0 < x.re := by
    have h1 : dist x c ≤ r := hxK
    have h2 := Complex.abs_re_le_norm (x - c)
    rw [Complex.dist_eq] at h1
    rw [Complex.sub_re] at h2
    have h3 := (abs_le.1 (h2.trans h1)).1
    linarith
  have hbot : 𝓝[≠] x ⊓ 𝓟 (Z ∩ closedBall c r) = ⊥ := by
    rw [inf_principal_eq_bot]
    exact mem_of_superset (hiso x hx) fun w hw hS => hw hS.1
  exact hacc.ne hbot

/-- Two distinct points to the left of the line `re s = σ` are equidistant from at most
one point of that line. -/
theorem equidistant_subsingleton {σ : ℝ} {a b : ℂ} (ha : a.re < σ) (hb : b.re < σ)
    (hab : a ≠ b) : {γ : ℝ | dist (Pt σ γ) a = dist (Pt σ γ) b}.Subsingleton := by
  intro γ₁ h₁ γ₂ h₂
  simp only [Set.mem_ofPred_eq, dist_Pt] at h₁ h₂
  rw [Real.sqrt_inj (by positivity) (by positivity)] at h₁ h₂
  by_contra hne
  have h3 : (γ₁ - γ₂) * (b.im - a.im) = 0 := by linear_combination (h₁ - h₂) / 2
  have him : a.im = b.im := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact (sub_eq_zero.1 h).symm
  rw [him] at h₁
  have h4 : (σ - a.re) ^ 2 = (σ - b.re) ^ 2 := by linarith
  have h5 : (a.re - b.re) * ((σ - a.re) + (σ - b.re)) = 0 := by linear_combination -h4
  have hre : a.re = b.re := by
    rcases mul_eq_zero.1 h5 with h | h
    · exact sub_eq_zero.1 h
    · exfalso; linarith
  exact hab (Complex.ext hre him)

theorem dist_ofReal_eq (σ : ℝ) (ρ : ℂ) :
    dist (σ : ℂ) ρ = Real.sqrt ((σ - ρ.re) ^ 2 + ρ.im ^ 2) := by
  rw [Complex.dist_eq_re_im]
  simp

/-- Pole configuration: there is a centre `σ + iγ` with a unique nearest pole `ρ₁` at
distance `< σ - θ`, isolated by a gap `e`; moreover either the centre is `σ` and `ρ₁`
is real, or every pole is farther from `σ` than `ρ₁` is from the centre, with a gap. -/
theorem pole_config {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z)
    (hle : ∀ ρ ∈ Z, ρ.re ≤ 2) {σ θ : ℝ} (hσ : 2 < σ) (hθ : 0 < θ) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z)
    (hρ₀θ : θ < ρ₀.re) :
    ∃ γ : ℝ, ∃ ρ₁ ∈ Z, ∃ e : ℝ, dist (Pt σ γ) ρ₁ < e ∧ e ≤ σ - θ ∧
      (∀ ρ ∈ Z, ρ ≠ ρ₁ → e ≤ dist (Pt σ γ) ρ) ∧
      ((γ = 0 ∧ ρ₁.im = 0) ∨
        ∃ e₀ : ℝ, dist (Pt σ γ) ρ₁ < e₀ ∧ e₀ ≤ σ - θ ∧ ∀ ρ ∈ Z, e₀ ≤ dist (σ : ℂ) ρ) := by
  have hlt : ∀ ρ ∈ Z, ρ.re < σ := fun ρ hρ => (hle ρ hρ).trans_lt hσ
  by_cases hcase : ∃ γ : ℝ, ∃ ρ ∈ Z, ∃ e₀ : ℝ, dist (Pt σ γ) ρ < e₀ ∧ e₀ ≤ σ - θ ∧
      ∀ ρ' ∈ Z, e₀ ≤ dist (σ : ℂ) ρ'
  · -- Case 2: perturb `γ` to make the nearest pole unique.
    obtain ⟨γ, ρ, hρ, e₀, hρe₀, he₀A, hfar⟩ := hcase
    set ε : ℝ := min (e₀ - dist (Pt σ γ) ρ) (θ / 2) with hε
    have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
    have hε1 : ε ≤ e₀ - dist (Pt σ γ) ρ := min_le_left _ _
    have hε2 : ε ≤ θ / 2 := min_le_right _ _
    set F : Set ℂ := Z ∩ closedBall (Pt σ γ) (e₀ + ε) with hF
    have hFfin : F.Finite := finite_inter_closedBall hiso (by rw [Pt_re]; linarith)
    have hρF : ρ ∈ F := by
      refine ⟨hρ, ?_⟩
      rw [mem_closedBall, dist_comm]
      linarith
    set Bad : Set ℝ := ⋃ a ∈ F, ⋃ b ∈ F, {γ' : ℝ | a ≠ b ∧ dist (Pt σ γ') a = dist (Pt σ γ') b}
      with hBad
    have hBadfin : Bad.Finite := by
      refine hFfin.biUnion fun a ha => hFfin.biUnion fun b hb => Set.Subsingleton.finite ?_
      intro x hx y hy
      exact equidistant_subsingleton (hlt a ha.1) (hlt b hb.1) hx.1 hx.2 hy.2
    obtain ⟨γ', hγ'I, hγ'B⟩ :=
      (Set.Ioo_infinite (show γ - ε < γ + ε by linarith)).exists_notMem_finite hBadfin
    have hγ'ε : |γ' - γ| < ε := by
      rw [abs_lt]; exact ⟨by linarith [hγ'I.1], by linarith [hγ'I.2]⟩
    have hγε' : |γ - γ'| < ε := by rw [abs_sub_comm]; exact hγ'ε
    obtain ⟨ρ₁, hρ₁F, hmin⟩ := Set.exists_min_image F (dist (Pt σ γ')) hFfin ⟨ρ, hρF⟩
    have hd₁ : dist (Pt σ γ') ρ₁ < e₀ := by
      have h1 := hmin ρ hρF
      have h2 := dist_Pt_le σ γ' γ ρ
      linarith
    have hstrict : ∀ ρ' ∈ F, ρ' ≠ ρ₁ → dist (Pt σ γ') ρ₁ < dist (Pt σ γ') ρ' := by
      intro ρ' hρ' hne
      refine lt_of_le_of_ne (hmin ρ' hρ') fun heq => hγ'B ?_
      rw [hBad]
      exact Set.mem_iUnion₂.2 ⟨ρ₁, hρ₁F, Set.mem_iUnion₂.2 ⟨ρ', hρ', hne.symm, heq⟩⟩
    obtain ⟨e, hde, hee₀, hgap⟩ := exists_gap hFfin (Pt σ γ') ρ₁ hd₁ hstrict
    refine ⟨γ', ρ₁, hρ₁F.1, e, hde, hee₀.trans he₀A, ?_, Or.inr ⟨e₀, hd₁, he₀A, hfar⟩⟩
    intro ρ' hρ'Z hne
    by_cases hin : ρ' ∈ F
    · exact hgap ρ' hin hne
    · have h1 : e₀ + ε < dist (Pt σ γ) ρ' := by
        by_contra hcon
        refine hin ⟨hρ'Z, ?_⟩
        rw [mem_closedBall, dist_comm]
        exact not_lt.1 hcon
      have h2 := dist_Pt_le σ γ γ' ρ'
      linarith
  · -- Case 1: the nearest pole to `σ` is real and unique.
    have hno : ∀ γ : ℝ, ∀ ρ ∈ Z, ∀ e₀ : ℝ, dist (Pt σ γ) ρ < e₀ → e₀ ≤ σ - θ →
        ∃ ρ' ∈ Z, dist (σ : ℂ) ρ' < e₀ := by
      intro γ ρ hρ e₀ h1 h2
      by_contra hcon
      refine hcase ⟨γ, ρ, hρ, e₀, h1, h2, fun ρ' hρ' => ?_⟩
      by_contra hlt'
      exact hcon ⟨ρ', hρ', not_le.1 hlt'⟩
    have h0 : dist (Pt σ ρ₀.im) ρ₀ < σ - θ := by
      rw [dist_Pt_self_im, abs_of_pos (by linarith [hlt ρ₀ hρ₀])]
      linarith
    obtain ⟨ρ', hρ'Z, hρ'A⟩ := hno ρ₀.im ρ₀ hρ₀ (σ - θ) h0 le_rfl
    set F₀ : Set ℂ := Z ∩ closedBall (σ : ℂ) (dist (σ : ℂ) ρ') with hF₀
    have hF₀fin : F₀.Finite :=
      finite_inter_closedBall hiso (by rw [Complex.ofReal_re]; linarith)
    have hρ'F : ρ' ∈ F₀ := ⟨hρ'Z, by rw [mem_closedBall, dist_comm]⟩
    obtain ⟨ρ₁, hρ₁F, hmin⟩ := Set.exists_min_image F₀ (dist (σ : ℂ)) hF₀fin ⟨ρ', hρ'F⟩
    have hρ₁Z : ρ₁ ∈ Z := hρ₁F.1
    have hglob : ∀ ρ ∈ Z, dist (σ : ℂ) ρ₁ ≤ dist (σ : ℂ) ρ := by
      intro ρ hρ
      by_cases hin : ρ ∈ F₀
      · exact hmin ρ hin
      · have h1 : dist (σ : ℂ) ρ' < dist (σ : ℂ) ρ := by
          by_contra hcon
          refine hin ⟨hρ, ?_⟩
          rw [mem_closedBall, dist_comm]
          exact not_lt.1 hcon
        exact (hmin ρ' hρ'F).trans h1.le
    have hd₀A : dist (σ : ℂ) ρ₁ < σ - θ := (hmin ρ' hρ'F).trans_lt hρ'A
    have key : ∀ ρ ∈ Z, dist (σ : ℂ) ρ = dist (σ : ℂ) ρ₁ → ρ.im = 0 := by
      intro ρ hρ hdist
      by_contra him
      have h1 : dist (Pt σ ρ.im) ρ < dist (σ : ℂ) ρ := by
        rw [dist_Pt_self_im, dist_ofReal_eq, ← Real.sqrt_sq_eq_abs]
        refine Real.sqrt_lt_sqrt (sq_nonneg _) ?_
        have : 0 < ρ.im ^ 2 := by positivity
        linarith
      obtain ⟨ρ'', hρ''Z, hρ''⟩ := hno ρ.im ρ hρ (dist (σ : ℂ) ρ₁) (by rw [← hdist]; exact h1)
        hd₀A.le
      exact absurd (hglob ρ'' hρ''Z) (not_le.2 hρ'')
    have hρ₁im : ρ₁.im = 0 := key ρ₁ hρ₁Z rfl
    set r₁ : ℝ := (dist (σ : ℂ) ρ₁ + (σ - θ)) / 2 with hr₁
    set F₁ : Set ℂ := Z ∩ closedBall (σ : ℂ) r₁ with hF₁
    have hF₁fin : F₁.Finite :=
      finite_inter_closedBall hiso (by rw [Complex.ofReal_re, hr₁]; linarith)
    have hstrict : ∀ ρ ∈ F₁, ρ ≠ ρ₁ → dist (σ : ℂ) ρ₁ < dist (σ : ℂ) ρ := by
      intro ρ hρ hne
      refine lt_of_le_of_ne (hglob ρ hρ.1) fun heq => hne ?_
      have him : ρ.im = 0 := key ρ hρ.1 heq.symm
      have h1 := heq
      rw [dist_ofReal_eq, dist_ofReal_eq, him, hρ₁im,
        Real.sqrt_inj (by positivity) (by positivity)] at h1
      have h2 : (ρ.re - ρ₁.re) * ((σ - ρ.re) + (σ - ρ₁.re)) = 0 := by linear_combination h1
      have hre : ρ.re = ρ₁.re := by
        rcases mul_eq_zero.1 h2 with h | h
        · exact sub_eq_zero.1 h
        · exfalso; linarith [hlt ρ hρ.1, hlt ρ₁ hρ₁Z]
      exact Complex.ext hre (him.trans hρ₁im.symm)
    obtain ⟨e, hde, her₁, hgap⟩ :=
      exists_gap hF₁fin (σ : ℂ) ρ₁ (show dist (σ : ℂ) ρ₁ < r₁ by rw [hr₁]; linarith) hstrict
    refine ⟨0, ρ₁, hρ₁Z, e, ?_, ?_, ?_, Or.inl ⟨rfl, hρ₁im⟩⟩
    · rw [Pt_zero]; exact hde
    · rw [hr₁] at her₁; linarith
    · intro ρ hρ hne
      rw [Pt_zero]
      by_cases hin : ρ ∈ F₁
      · exact hgap ρ hin hne
      · have h1 : r₁ < dist (σ : ℂ) ρ := by
          by_contra hcon
          refine hin ⟨hρ, ?_⟩
          rw [mem_closedBall, dist_comm]
          exact not_lt.1 hcon
        linarith

end IndependentLandau
