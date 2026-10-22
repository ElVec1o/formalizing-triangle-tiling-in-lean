import Erdos634.Draft.LaczFormalColumnMain

/-!
# The wall frame with a BASE wall: the rules `T(m)`, `A(m)` at the level `0` (two-barrier corner)

Erdős #634, base-`β` row, Column Lemma.  Credit: AI assistant (Column Lemma and Wall Lemma proposals), Beeson–Roșu, Beeson,
Laczkovich.  UNAUDITED.  Axiom-clean; no `sorry`.

`WFrame.MJ_main` (`LaczFormalColumnMain`) proves the rules `T(m)`, `A(m)` at the levels `lv ≥ 1`: standard cells stand
below.  The level `0` is the level of the BASE of the target in `LaczFormalMJMain`, where it uses (i) the base points are frontier
points (`base_front`, `bfig`), (ii) the line `l` leaves the target below the base (`ns_start_y`).  Here the base is a BASE WALL: a
horizontal line `{y = 0}` crossed by no tile on the stretch `0 < x < λ`, with the one-sided angle sum `π` above it
(`BaseWall`: `hside`, `hsum`; for an interior base wall `hsum` is `half_angle_sum`, for the base of the target it is
`pin_angle_sum`).  Then `MJ_main0` gives `T(m)`, `A(m)` at ALL levels `lv ≥ 0`, i.e. the full corner induction `M(j)` at the
corner of TWO walls (the leg wall `{O + y v}` and the base wall `{O + x e0}`) of angle `β`.  This is the "two-barrier frame": it
is not `~5000` lines but the same induction with one more pair of hypotheses.  The stack standing on a FAULT SEGMENT `Λ` with its
left end on a `β`-wall is this corner (the base wall is `Λ`).  `ofLFrame_base` : the corner frame of a target is such a frame.
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace WFrame

variable (F : WFrame D e f α β γ p q r)

/-- The base wall functional `crossL (−e0)` and its level at the origin: `gB (pt x y) = cB − y κ`, so the closed side
`{gB ≤ cB}` is `{y ≥ 0}`. -/
noncomputable def gB : Plane →ₗ[ℝ] ℝ := crossL (-F.e0)

noncomputable def cB : ℝ := cross (-F.e0) F.O

theorem gB_sub_cB (z : Plane) : F.gB z - F.cB = -(F.ht z * cross F.e0 F.v) := by
  have hκ : cross F.e0 F.v ≠ 0 := F.hcr.ne'
  unfold gB cB ht
  rw [crossL_apply, div_mul_cancel₀ _ hκ]
  simp only [cross, PiLp.neg_apply, PiLp.sub_apply]; ring

theorem gB_pt (x y : ℝ) : F.gB (F.pt x y) = F.cB - y * cross F.e0 F.v := by
  have := F.gB_sub_cB (F.pt x y)
  rw [F.ht_pt] at this
  linarith

/-- The base wall: no tile crosses `{y = 0}` on `0 < x < λ`, and the one-sided angle sum above it is `π`. -/
structure BaseWall : Prop where
  hside : ∀ x : ℝ, 0 < x → x < F.lam → ∀ i : Fin N, F.pt x 0 ∈ (D.tile i).carrier →
    (D.tile i).carrier ⊆ {z | F.gB z ≤ F.cB} ∨ (D.tile i).carrier ⊆ {z | F.cB ≤ F.gB z}
  hsum : ∀ x : ℝ, 0 < x → x < F.lam →
    ∑ i ∈ Side D.toDissection F.gB F.cB, (D.tile i).localAngle (F.pt x 0) = Real.pi

/-- The rule `T(m)` at all levels `lv ≥ 0`. -/
def TRule0 (H m : ℕ) : Prop :=
  ∀ lv : ℕ, lv + m + 1 ≤ H → m + 1 ≤ e → F.Ground lv (m + 1) →
    (∀ x : ℕ, x ≤ m → F.UpCell (x : ℝ) (lv : ℝ)) → F.DownCell (m : ℝ) (lv : ℝ)

/-- The rule `A(m)` at all levels `lv ≥ 0`. -/
def ARule0 (H m : ℕ) : Prop :=
  ∀ lv : ℕ, lv + m + 1 ≤ H → m + 1 ≤ e → F.Ground lv (m + 1) →
    (∀ x : ℕ, x ≤ m → F.UpCell (x : ℝ) (lv : ℝ)) →
    ∀ (i : Fin N) (K Z : Plane) (t : ℝ),
      TileVerts (D.tile i) (F.pt ((m : ℝ) + 1) (lv : ℝ)) K Z →
      K = F.pt ((m : ℝ) + 1) (lv : ℝ) + t • F.e0 → 0 < t →
      (dist (F.pt ((m : ℝ) + 1) (lv : ℝ)) K = (tb e f : ℝ) ∨ dist (F.pt ((m : ℝ) + 1) (lv : ℝ)) K = (tc e f : ℝ)) →
      0 < cross F.e0 (Z - F.pt ((m : ℝ) + 1) (lv : ℝ)) →
      (D.tile i).localAngle (F.pt ((m : ℝ) + 1) (lv : ℝ)) ≠ β → False

theorem TRule0.toTRule {H m : ℕ} (h : F.TRule0 H m) : F.TRule H m :=
  fun lv _ hrH hme hG hups => h lv hrH hme hG hups

theorem ARule0.toARule {H m : ℕ} (h : F.ARule0 H m) : F.ARule H m :=
  fun lv _ hrH hme hG hups => h lv hrH hme hG hups

/-- Vertices of height `≥ 0` give a tile above the base wall. -/
theorem ht_nonneg_of_verts {i : Fin N} {A B C : Plane} (hv : TileVerts (D.tile i) A B C)
    (hA : 0 ≤ F.ht A) (hB : 0 ≤ F.ht B) (hC : 0 ≤ F.ht C) : ∀ j : Fin 3, 0 ≤ F.ht ((D.tile i).pts j) := by
  intro j
  rcases hv.pts_mem j with h | h | h <;> rw [h] <;> assumption

theorem tile_mem_SideB {i : Fin N} (h : ∀ j : Fin 3, 0 ≤ F.ht ((D.tile i).pts j)) :
    i ∈ Side D.toDissection F.gB F.cB := by
  rw [mem_Side]
  intro z hz
  refine Tri.carrier_subset_halfplane (D.tile i) F.gB F.cB (fun j => ?_) z hz
  have := F.gB_sub_cB ((D.tile i).pts j)
  have h1 := h j
  have h2 := F.hcr
  nlinarith

/-- The line `l` is not straddled at a point of the base wall. -/
theorem ns_J0 {H m : ℕ} (hB : F.Bnd H) (BW : F.BaseWall) (hrH : 0 + m + 1 ≤ H) :
    ¬ F.StrL ((m : ℝ) + 1) ((0 : ℕ) : ℝ) (F.pt ((m : ℝ) + 1) ((0 : ℕ) : ℝ)) := by
  have hHr : ((0 : ℕ) : ℝ) + m + 1 ≤ H := by exact_mod_cast hrH
  have hx : ((m : ℝ) + 1) < F.lam := by linarith [hB.1]
  have hxpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hpt : F.pt ((m : ℝ) + 1) ((0 : ℕ) : ℝ) = F.pt ((m : ℝ) + 1) 0 := by simp
  rw [hpt]
  refine wall_not_straddled D.toDissection F.gB (crossL (F.v - F.e0)) F.cB _ (by rw [F.gB_pt]; simp) ?_
    (fun i hi => BW.hside _ hxpos hx i hi)
  intro w h1 h2
  refine F.w_zero_of ?_ ?_
  · simp only [gB, crossL_apply, cross, PiLp.neg_apply, PiLp.sub_apply] at h1 h2 ⊢
    linarith
  · simp only [gB, crossL_apply, cross, PiLp.neg_apply, PiLp.sub_apply] at h1 ⊢
    linarith

/-- **The down-tile rule `T(m)` at all levels `lv ≥ 0`** (level `0` with the base wall `BW`), from the rules `T(i)`, `A(i)`, `i < m`. -/
theorem Tmain0 {H m : ℕ} (hB : F.Bnd H) (BW : F.BaseWall) (IHT : ∀ i, i < m → F.TRule0 H i)
    (IHA : ∀ i, i < m → F.ARule0 H i) : F.TRule0 H m := by
  classical
  intro lv hrH hme hG hups
  have hnsJ : ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.pt ((m : ℝ) + 1) (lv : ℝ)) := by
    rcases Nat.eq_zero_or_pos lv with rfl | hlv
    · exact F.ns_J0 hB BW hrH
    · exact F.ns_J hB hlv hrH hG (hups m le_rfl)
  have E : F.Env H m lv := ⟨hB, hrH, hme, fun i hi l _ => IHT i hi l, fun i hi l _ => IHA i hi l, hnsJ⟩
  -- Step A: the down tiles between the `m+1` up tiles
  have hDn : ∀ x : ℕ, x + 1 ≤ m → F.DownCell (x : ℝ) (lv : ℝ) := by
    intro x hx
    have h0 : x < m := by omega
    have h1 : lv + x + 1 ≤ H := by omega
    have h2 : x + 1 ≤ e := by omega
    have h3 : F.Ground lv (x + 1) := WFrame.Ground.mono F hG (by omega)
    have h4 : ∀ x'' : ℕ, x'' ≤ x → F.UpCell (x'' : ℝ) (lv : ℝ) := fun x'' hx'' => hups x'' (by omega)
    exact IHT x h0 lv h1 h2 h3 h4
  have hStd0 : F.Std lv m 0 := by
    intro t ht
    have : t = 0 := by omega
    subst this
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simpa using hups x (by omega)
    · simpa using hDn x (by omega)
  have hJ0 : F.Dp m lv ((0 : ℕ) : ℝ) = F.pt ((m : ℝ) + 1) (lv : ℝ) := by
    unfold Dp; simp
  -- nothing straddles `D_1`
  have hnsD1 : ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv (((0 : ℕ) : ℝ) + 1)) := by
    by_cases hm : 1 ≤ m
    · intro hstr
      exact (F.ZA E m 0 (by omega)).1 hm hStd0 hstr
    · have hm0 : m = 0 := by omega
      subst hm0
      have := F.ns_Dend 0 lv hB hrH
      simpa using this
  obtain ⟨-, hcov⟩ := F.lcov (s' := 0) E (by omega) hStd0 hnsD1
  obtain ⟨e', he', hends⟩ := hcov 0 (by omega)
  obtain ⟨hvt, hcF⟩ := chain_tileVerts he' (A := F.Dp m lv ((0 : ℕ) : ℝ)) (B := F.Dp m lv (((0 : ℕ) : ℝ) + 1))
    (by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩)
  have hd := F.dist_Dp m lv ((0 : ℕ) : ℝ)
  rcases tv_bedge F.S hvt hd with ⟨h1, h2, -, -, -⟩ | ⟨h1, h2, -, -, -⟩
  · -- type A: impossible by Claim A
    exfalso
    exact (F.ZA E m 0 (by omega)).2 hStd0 ⟨e'.1, _, hvt, hcF, h2⟩
  · -- type B: the standard down tile
    rw [hJ0] at hvt h1
    have hD1 : F.Dp m lv (((0 : ℕ) : ℝ) + 1) = F.pt (m : ℝ) ((lv : ℝ) + 1) := by
      unfold Dp; congr 1 <;> simp
    rw [hD1] at hvt
    have hu : F.pt (m : ℝ) ((lv : ℝ) + 1) - F.pt ((m : ℝ) + 1) (lv : ℝ) = F.v - F.e0 := by
      rw [F.pt_sub]; module
    have hZc : cross (F.v - F.e0) ((D.tile e'.1).pts (e'.2 + 2)) ≤
        cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (lv : ℝ)) := by
      have := hcF (e'.2 + 2)
      simpa [crossL_apply] using this
    have hcr := tv_cross_ne hvt
    rw [hu] at hcr
    have hside : cross (F.pt (m : ℝ) ((lv : ℝ) + 1) - F.pt ((m : ℝ) + 1) (lv : ℝ))
        ((D.tile e'.1).pts (e'.2 + 2) - F.pt ((m : ℝ) + 1) (lv : ℝ)) < 0 := by
      rw [hu]
      have : cross (F.v - F.e0) ((D.tile e'.1).pts (e'.2 + 2) - F.pt ((m : ℝ) + 1) (lv : ℝ)) ≤ 0 := by
        rw [cross_sub_right]; linarith
      exact lt_of_le_of_ne this hcr
    have hZ := F.third_down (x := (m : ℝ)) (y := (lv : ℝ)) hvt h1 hside
    exact ⟨e'.1, by rw [hZ] at hvt; exact hvt⟩

/-- **The rule `A(m)` at all levels `lv ≥ 0`** (level `0` with the base wall `BW`), from `T(m)`. -/
theorem Amain0 {H m : ℕ} (hB : F.Bnd H) (BW : F.BaseWall) (hT : F.TRule0 H m) : F.ARule0 H m := by
  classical
  intro lv hrH hme hG hups i K Z t hv hK ht hdist hup hne
  obtain ⟨iD, hiD⟩ := hT lv hrH hme hG hups
  obtain ⟨iA, hiA⟩ := hups m le_rfl
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct F.S
  have hHr : (lv : ℝ) + m + 1 ≤ H := by exact_mod_cast hrH
  have hγD : (D.tile iD).localAngle (F.pt ((m : ℝ) + 1) (lv : ℝ)) = γ := (F.down_angles hiD).1
  have hαA : (D.tile iA).localAngle (F.pt ((m : ℝ) + 1) (lv : ℝ)) = α := (F.up_angles hiA).2.1
  -- the angle of `Y` at `J` is `α` or `γ`
  have hY : (D.tile i).localAngle (F.pt ((m : ℝ) + 1) (lv : ℝ)) = α ∨
      (D.tile i).localAngle (F.pt ((m : ℝ) + 1) (lv : ℝ)) = γ := by
    rcases hdist with hb | hc
    · rcases tv_bedge F.S hv hb with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    · rcases tv_cedge F.S hv hc with h | h
      · exact Or.inl h.1
      · exact absurd h.1 hne
  have hiAD : iA ≠ iD := by
    intro h
    rw [h] at hαA
    rw [hγD] at hαA
    exact hαγ.symm hαA
  have hiYA : i ≠ iA := F.Y_ne_up ht hv hK hiA
  have hiYD : i ≠ iD := F.Y_ne_down ht hv hK hiD
  have hZht : (lv : ℝ) < F.ht Z := by
    have e2 : F.ht Z - (lv : ℝ) = cross F.e0 (Z - F.pt ((m : ℝ) + 1) (lv : ℝ)) / cross F.e0 F.v := by
      have := F.ht_sub Z (F.pt ((m : ℝ) + 1) (lv : ℝ)); rwa [F.ht_pt] at this
    have : 0 < F.ht Z - (lv : ℝ) := by rw [e2]; exact div_pos hup F.hcr
    linarith
  have hnbY : ¬ F.Below (lv : ℝ) i := F.not_below_of_TV hv hZht
  have hnbA : ¬ F.Below (lv : ℝ) iA := F.not_below_of_TV hiA (by rw [F.ht_pt]; linarith)
  have hnbD : ¬ F.Below (lv : ℝ) iD := F.not_below_of_TV hiD (by rw [F.ht_pt]; linarith)
  have cA := cnt_ge_one hαA
  have cD := cnt_ge_one hγD
  rcases Nat.eq_zero_or_pos lv with rfl | hlv
  · -- the base wall: `J` is a point of the wall `y = 0`
    have hx : ((m : ℝ) + 1) < F.lam := by
      have : ((0 : ℕ) : ℝ) + m + 1 ≤ H := hHr
      linarith [hB.1]
    have hxpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hsum := BW.hsum ((m : ℝ) + 1) hxpos hx
    simp only [Nat.cast_zero] at hsum hαA hγD hY hZht hiA hiD hv hK
    have hsA : iA ∈ Side D.toDissection F.gB F.cB := by
      refine F.tile_mem_SideB (F.ht_nonneg_of_verts hiA ?_ ?_ ?_) <;> rw [F.ht_pt] <;> linarith
    have hsD : iD ∈ Side D.toDissection F.gB F.cB := by
      refine F.tile_mem_SideB (F.ht_nonneg_of_verts hiD ?_ ?_ ?_) <;> rw [F.ht_pt] <;> linarith
    have hsY : i ∈ Side D.toDissection F.gB F.cB := by
      refine F.tile_mem_SideB (F.ht_nonneg_of_verts hv ?_ ?_ ?_)
      · rw [F.ht_pt]
      · rw [hK, F.ht_add_e0, F.ht_pt]
      · linarith
    rcases hY with h | h
    · have c1 := scnt_ge_two hiYA hsY hsA h hαA
      have c2 := scnt_ge_one hsD hγD
      rcases wall_figure_sum F.S F.gB F.cB hsum with h' | h' | h' <;> omega
    · have c1 := scnt_ge_two hiYD hsY hsD h hγD
      have c2 := scnt_ge_one hsA hαA
      rcases wall_figure_sum F.S F.gB F.cB hsum with h' | h' | h' <;> omega
  · -- an interior point
    -- an interior point, with the three tiles of the ground below
    obtain ⟨lv0, rfl⟩ : ∃ lv0, lv = lv0 + 1 := ⟨lv - 1, by omega⟩
    obtain ⟨iγ, iβ, iα, hγ, hβ, hα, hbγ, hbβ, hbα⟩ :=
      F.ground_junction (ρ := lv0) (k := m + 1) (x := m + 1) hG (by omega) le_rfl
    have hJc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have hcast : (((lv0 + 1 : ℕ)) : ℝ) = (lv0 : ℝ) + 1 := by push_cast; ring
    rw [hJc] at hγ hβ hα
    rw [hcast] at hγD hαA hY
    have hint : F.pt ((m : ℝ) + 1) ((lv0 : ℝ) + 1) ∈ interior D.target.carrier := by
      apply F.pt_interior (by linarith) (by positivity)
      exact (F.latOK hB (by linarith) (by positivity) (by rw [hcast] at hHr; linarith)).2.2
    have hbγ' : F.Below ((lv0 + 1 : ℕ) : ℝ) iγ := hbγ
    have hbα' : F.Below ((lv0 + 1 : ℕ) : ℝ) iα := hbα
    have hne1 : iα ≠ iA := fun h => hnbA (h ▸ hbα')
    have hne2 : iα ≠ i := fun h => hnbY (h ▸ hbα')
    have hne3 : iγ ≠ iD := fun h => hnbD (h ▸ hbγ')
    have hne4 : iγ ≠ i := fun h => hnbY (h ▸ hbγ')
    have hfig := ifig F.S hint
    rcases hY with h | h
    · have c1 := cnt_ge_three hne1 hne2 hiYA.symm hα hαA h
      have c2 := cnt_ge_two hne3 hγ hγD
      omega
    · have c1 := cnt_ge_three hne3 hne4 hiYD.symm hγ hγD h
      have c2 := cnt_ge_two hne1 hα hαA
      omega


/-- **The induction `M(j)` at all levels `lv ≥ 0`** (the corner of the leg wall and the base wall). -/
theorem MJ_main0 {H : ℕ} (hB : F.Bnd H) (BW : F.BaseWall) : ∀ m, F.TRule0 H m ∧ F.ARule0 H m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hT : F.TRule0 H m := F.Tmain0 hB BW (fun i hi => (ih i hi).1) (fun i hi => (ih i hi).2)
    exact ⟨hT, F.Amain0 hB BW hT⟩

end WFrame

end Erdos634.LaczCol
