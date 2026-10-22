import Erdos634.Draft.LaczFormalWalkBase
import Erdos634.Draft.LaczFormalChain

/-!
# Tokens of the steps of a walk

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson, Laczkovich, Paliy.
UNAUDITED.  Axiom-clean; no `sorry`.

Every step `(i, U, U')` of the walk along the base is a tile `i` with an edge `UU'`.  `elemTok` reads its token
off the geometry (edge length `a/b/c`, angle at `U` `α/β/γ`), and `elem_baseTok` proves it is a `BaseTok`:
the angle at `U'` is the one the token table prescribes (`edge_ends`: the two ends of an edge of length
`a` (resp. `b`, `c`) carry `{β,γ}` (resp. `{α,γ}`, `{α,β}`)).
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem BandSetup.distinct {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) :
    α ≠ β ∧ β ≠ γ ∧ α ≠ γ ∧ sideOpp D.model 0 ≠ sideOpp D.model 1 ∧
      sideOpp D.model 1 ≠ sideOpp D.model 2 ∧ sideOpp D.model 0 ≠ sideOpp D.model 2 := by
  have hαβ : α ≠ β := by
    intro h
    apply S.hirr
    refine ⟨1/5, ?_⟩
    have hr := S.hrel
    rw [← h] at hr
    have : α = Real.pi / 5 := by linarith
    rw [this]; push_cast; ring
  have hβγ : β ≠ γ := by rw [S.hγdef]; intro h; linarith [S.hα0]
  have hαγ : α ≠ γ := by rw [S.hγdef]; intro h; linarith [S.hα0, S.hβ0]
  have hnea : sideOpp D.model 0 ≠ sideOpp D.model 1 := by
    rw [S.hsa, S.hsb]; intro h
    have h' : ta e f = tb e f := by exact_mod_cast h
    exact a_not_dvd_b e f S.he S.hef S.hcop (h' ▸ dvd_refl _)
  have hneb : sideOpp D.model 1 ≠ sideOpp D.model 2 := by
    rw [S.hsb, S.hsc]; intro h
    have h' : tb e f = tc e f := by exact_mod_cast h
    have := b_lt_c e f S.he S.hef; omega
  have hac : ta e f < tc e f := by unfold ta tc; nlinarith [S.he, S.hef]
  have hnec : sideOpp D.model 0 ≠ sideOpp D.model 2 := by
    rw [S.hsa, S.hsc]; intro h
    have h' : ta e f = tc e f := by exact_mod_cast h
    omega
  exact ⟨hαβ, hβγ, hαγ, hnea, hneb, hnec⟩

theorem perm3 {x y z a b c : ℝ} (hm : ({x, y, z} : Multiset ℝ) = {c, b, a})
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (x = c ∧ y = b ∧ z = a) ∨ (x = c ∧ y = a ∧ z = b) ∨ (x = b ∧ y = c ∧ z = a) ∨
    (x = b ∧ y = a ∧ z = c) ∨ (x = a ∧ y = c ∧ z = b) ∨ (x = a ∧ y = b ∧ z = c) := by
  have hx : x ∈ ({c, b, a} : Multiset ℝ) := by rw [← hm]; simp
  have hy : y ∈ ({c, b, a} : Multiset ℝ) := by rw [← hm]; simp
  have hz : z ∈ ({c, b, a} : Multiset ℝ) := by rw [← hm]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx hy hz
  have hba := hab.symm
  have hcb := hbc.symm
  have hca := hac.symm
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rcases hz with hz | hz | hz <;>
    first
    | (simp [hx, hy, hz]; done)
    | (exfalso
       rw [hx, hy, hz] at hm
       have h1 := congrArg (Multiset.count c) hm
       have h2 := congrArg (Multiset.count b) hm
       have h3 := congrArg (Multiset.count a) hm
       simp [Multiset.count_cons, hab, hbc, hac, hba, hcb, hca] at h1 h2 h3)

/-- **The two ends of an edge of a tile.**  For three distinct vertices `k, f, g` of tile `i`: the edge `kf` has
length `a` with ends `{β,γ}`, or `b` with ends `{α,γ}`, or `c` with ends `{α,β}` (in either order). -/
theorem edge_ends (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hab : sideOpp D.model 0 ≠ sideOpp D.model 1) (hbc : sideOpp D.model 1 ≠ sideOpp D.model 2)
    (hac : sideOpp D.model 0 ≠ sideOpp D.model 2)
    (hαβ : α ≠ β) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
    (i : Fin N) (k f g : Fin 3) (hkf : k ≠ f) (hkg : k ≠ g) (hfg : f ≠ g) :
    (dist ((D.tile i).pts k) ((D.tile i).pts f) = sideOpp D.model 0 ∧
      (((D.tile i).localAngle ((D.tile i).pts k) = β ∧ (D.tile i).localAngle ((D.tile i).pts f) = γ) ∨
       ((D.tile i).localAngle ((D.tile i).pts k) = γ ∧ (D.tile i).localAngle ((D.tile i).pts f) = β))) ∨
    (dist ((D.tile i).pts k) ((D.tile i).pts f) = sideOpp D.model 1 ∧
      (((D.tile i).localAngle ((D.tile i).pts k) = α ∧ (D.tile i).localAngle ((D.tile i).pts f) = γ) ∨
       ((D.tile i).localAngle ((D.tile i).pts k) = γ ∧ (D.tile i).localAngle ((D.tile i).pts f) = α))) ∨
    (dist ((D.tile i).pts k) ((D.tile i).pts f) = sideOpp D.model 2 ∧
      (((D.tile i).localAngle ((D.tile i).pts k) = α ∧ (D.tile i).localAngle ((D.tile i).pts f) = β) ∨
       ((D.tile i).localAngle ((D.tile i).pts k) = β ∧ (D.tile i).localAngle ((D.tile i).pts f) = α))) := by
  -- the multiset of the three side lengths in the order `(kf, kg, fg)`
  have hm : ({dist ((D.tile i).pts k) ((D.tile i).pts f), dist ((D.tile i).pts k) ((D.tile i).pts g),
      dist ((D.tile i).pts f) ((D.tile i).pts g)} : Multiset ℝ) =
      {sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0} := by
    have hcase : (f = k + 1 ∧ g = k + 2) ∨ (f = k + 2 ∧ g = k + 1) := by
      revert hkf hkg hfg; revert k f g; decide
    have tm := tile_multiset D i k
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [dist_comm ((D.tile i).pts k) ((D.tile i).pts (k+2))]; exact tm
    · rw [dist_comm ((D.tile i).pts k) ((D.tile i).pts (k+2)),
        dist_comm ((D.tile i).pts (k+2)) ((D.tile i).pts (k+1))]
      exact (Multiset.cons_swap _ _ _).trans tm
  -- the angle at a vertex from the opposite side
  have hang : ∀ m n o : Fin 3, m ≠ n → m ≠ o → n ≠ o →
      (dist ((D.tile i).pts n) ((D.tile i).pts o) = sideOpp D.model 0 →
        (D.tile i).localAngle ((D.tile i).pts m) = α) ∧
      (dist ((D.tile i).pts n) ((D.tile i).pts o) = sideOpp D.model 1 →
        (D.tile i).localAngle ((D.tile i).pts m) = β) ∧
      (dist ((D.tile i).pts n) ((D.tile i).pts o) = sideOpp D.model 2 →
        (D.tile i).localAngle ((D.tile i).pts m) = γ) := by
    intro m n o h1 h2 h3
    have hc := tile_vertex_angle_cases D α β γ hα' hβ' hγ' i m
    have hopp : dist ((D.tile i).pts n) ((D.tile i).pts o) =
        dist ((D.tile i).pts (m+1)) ((D.tile i).pts (m+2)) := by
      revert h1 h2 h3
      fin_cases m <;> fin_cases n <;> fin_cases o <;> intro h1 h2 h3 <;> simp at h1 h2 h3 <;>
        first | rfl | exact dist_comm _ _
    rw [hopp]
    rcases hc with ⟨hA, hd⟩ | ⟨hA, hd⟩ | ⟨hA, hd⟩
    · refine ⟨fun _ => hA, fun h => absurd (hd.symm.trans h) hab, fun h => absurd (hd.symm.trans h) hac⟩
    · refine ⟨fun h => absurd (hd.symm.trans h) hab.symm, fun _ => hA,
        fun h => absurd (hd.symm.trans h) hbc⟩
    · refine ⟨fun h => absurd (hd.symm.trans h) hac.symm, fun h => absurd (hd.symm.trans h) hbc.symm,
        fun _ => hA⟩
  obtain ⟨k0, k1, k2⟩ := hang k f g hkf hkg hfg
  obtain ⟨f0, f1, f2⟩ := hang f k g hkf.symm hfg hkg
  rcases perm3 hm hab hbc hac with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
      ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · exact Or.inr (Or.inr ⟨hx, Or.inl ⟨k0 hz, f1 hy⟩⟩)
  · exact Or.inr (Or.inr ⟨hx, Or.inr ⟨k1 hz, f0 hy⟩⟩)
  · exact Or.inr (Or.inl ⟨hx, Or.inl ⟨k0 hz, f2 hy⟩⟩)
  · exact Or.inr (Or.inl ⟨hx, Or.inr ⟨k2 hz, f0 hy⟩⟩)
  · exact Or.inl ⟨hx, Or.inl ⟨k1 hz, f2 hy⟩⟩
  · exact Or.inl ⟨hx, Or.inr ⟨k2 hz, f1 hy⟩⟩


/-! ## Reading the token off a step -/

def tokOf : Side → Corner → Tok
  | .a, .B => .aBG | .a, .G => .aGB | .b, .A => .bAG | .b, .G => .bGA
  | .c, .A => .cAB | .c, .B => .cBA | _, _ => .cBA

open Classical in
noncomputable def sideOfLen (A B x : ℝ) : Side := if x = A then .a else if x = B then .b else .c

open Classical in
noncomputable def cornerOfAng (α β θ : ℝ) : Corner := if θ = α then .A else if θ = β then .B else .G

/-- The token of a walk entry `(i, U, U')`. -/
noncomputable def elemTok (D : CongruentDissection N) (α β : ℝ) (e : Fin N × Plane × Plane) : Tok :=
  tokOf (sideOfLen (sideOpp D.model 0) (sideOpp D.model 1) (dist e.2.1 e.2.2))
    (cornerOfAng α β ((D.tile e.1).localAngle e.2.1))

theorem sideOfLen_a {A B x : ℝ} (h : x = A) : sideOfLen A B x = .a := by
  unfold sideOfLen; rw [if_pos h]
theorem sideOfLen_b {A B x : ℝ} (hxA : x ≠ A) (h : x = B) : sideOfLen A B x = .b := by
  unfold sideOfLen; rw [if_neg hxA, if_pos h]
theorem sideOfLen_c {A B x : ℝ} (hxA : x ≠ A) (hxB : x ≠ B) : sideOfLen A B x = .c := by
  unfold sideOfLen; rw [if_neg hxA, if_neg hxB]
theorem cornerOfAng_A {α β θ : ℝ} (h : θ = α) : cornerOfAng α β θ = .A := by
  unfold cornerOfAng; rw [if_pos h]
theorem cornerOfAng_B {α β θ : ℝ} (hxA : θ ≠ α) (h : θ = β) : cornerOfAng α β θ = .B := by
  unfold cornerOfAng; rw [if_neg hxA, if_pos h]
theorem cornerOfAng_G {α β θ : ℝ} (hxA : θ ≠ α) (hxB : θ ≠ β) : cornerOfAng α β θ = .G := by
  unfold cornerOfAng; rw [if_neg hxA, if_neg hxB]

theorem fin3_pair (kk f g : Fin 3) (h1 : f ≠ kk) (h2 : g ≠ kk) (h3 : g ≠ f) :
    (f = kk + 1 ∧ g = kk + 2) ∨ (f = kk + 2 ∧ g = kk + 1) := by
  revert kk f g; decide

/-- **A step of the walk is a `BaseTok`.**  Tile `i` with the three distinct vertices `kk` (at `U`), `fi`
(at `U'`), `g` (at `Z`); `U, U'` on the base in increasing order. -/
theorem elem_baseTok {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (i : Fin N) (kk fi g : Fin 3) (hfk : fi ≠ kk) (hgk : g ≠ kk)
    (hgf : g ≠ fi) {U U' Z : Plane} (hU : (D.tile i).pts kk = U) (hU' : (D.tile i).pts fi = U')
    (hZ : (D.tile i).pts g = Z)
    (hm1 : U ∈ segment ℝ (D.target.pts p) (D.target.pts q))
    (hm2 : U' ∈ segment ℝ (D.target.pts p) (D.target.pts q))
    (hord : dist (D.target.pts p) U < dist (D.target.pts p) U') :
    BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f))
      (elemTok D α β (i, U, U')).side (elemTok D α β (i, U, U')).left
      (elemTok D α β (i, U, U')).right i U U' Z := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  have hverts : TileVerts (D.tile i) U U' Z := by
    refine ⟨kk, ?_⟩
    rcases fin3_pair kk fi g hfk hgk hgf with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; subst h1; subst h2; exact ⟨hU, hU', hZ⟩
    · right; subst h1; subst h2; exact ⟨hU, hZ, hU'⟩
  have hee := edge_ends D α β γ S.hα' S.hβ' S.hγ' hab hbc hac hαβ hβγ hαγ i kk fi g hfk.symm hgk.symm
    hgf.symm
  rw [hU, hU'] at hee
  have hsa := S.hsa
  have hsb := S.hsb
  have hsc := S.hsc
  have mk : ∀ t : Tok, elemTok D α β (i, U, U') = t →
      dist U U' = lenOf (ta e f) (tb e f) (tc e f) t.side →
      (D.tile i).localAngle U = angOf α β γ t.left →
      (D.tile i).localAngle U' = angOf α β γ t.right →
      BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f))
        (elemTok D α β (i, U, U')).side (elemTok D α β (i, U, U')).left
        (elemTok D α β (i, U, U')).right i U U' Z := by
    intro t ht h1 h2 h3
    rw [ht]
    exact ⟨hm1, hm2, hord, hverts, h1, h2, h3⟩
  have hel : ∀ (s : Side) (c : Corner), elemTok D α β (i, U, U') = tokOf s c →
      elemTok D α β (i, U, U') = tokOf s c := fun _ _ h => h
  rcases hee with ⟨hd, hA⟩ | ⟨hd, hA⟩ | ⟨hd, hA⟩
  · -- length a
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine mk .aBG ?_ (by simp [Tok.side, lenOf, hd, hsa]) (by simpa [Tok.left, angOf] using h1)
        (by simpa [Tok.right, angOf] using h2)
      unfold elemTok; simp only []
      rw [sideOfLen_a hd, cornerOfAng_B (by rw [h1]; exact hαβ.symm) h1]; rfl
    · refine mk .aGB ?_ (by simp [Tok.side, lenOf, hd, hsa]) (by simpa [Tok.left, angOf] using h1)
        (by simpa [Tok.right, angOf] using h2)
      unfold elemTok; simp only []
      rw [sideOfLen_a hd, cornerOfAng_G (by rw [h1]; exact hαγ.symm) (by rw [h1]; exact hβγ.symm)]; rfl
  · -- length b
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine mk .bAG ?_ (by simp [Tok.side, lenOf, hd, hsb]) (by simpa [Tok.left, angOf] using h1)
        (by simpa [Tok.right, angOf] using h2)
      unfold elemTok; simp only []
      rw [sideOfLen_b (by rw [hd]; exact hab.symm) hd, cornerOfAng_A h1]; rfl
    · refine mk .bGA ?_ (by simp [Tok.side, lenOf, hd, hsb]) (by simpa [Tok.left, angOf] using h1)
        (by simpa [Tok.right, angOf] using h2)
      unfold elemTok; simp only []
      rw [sideOfLen_b (by rw [hd]; exact hab.symm) hd,
        cornerOfAng_G (by rw [h1]; exact hαγ.symm) (by rw [h1]; exact hβγ.symm)]; rfl
  · -- length c
    have hxA : dist U U' ≠ sideOpp D.model 0 := by rw [hd]; exact hac.symm
    have hxB : dist U U' ≠ sideOpp D.model 1 := by rw [hd]; exact hbc.symm
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine mk .cAB ?_ (by simp [Tok.side, lenOf, hd, hsc]) (by simpa [Tok.left, angOf] using h1)
        (by simpa [Tok.right, angOf] using h2)
      unfold elemTok; simp only []
      rw [sideOfLen_c hxA hxB, cornerOfAng_A h1]; rfl
    · refine mk .cBA ?_ (by simp [Tok.side, lenOf, hd, hsc]) (by simpa [Tok.left, angOf] using h1)
        (by simpa [Tok.right, angOf] using h2)
      unfold elemTok; simp only []
      rw [sideOfLen_c hxA hxB, cornerOfAng_B (by rw [h1]; exact hαβ.symm) h1]; rfl


/-- The three side lengths of a tile seen from the vertices `k, f, g` (order `kf, kg, fg`). -/
theorem tri_ms (D : CongruentDissection N) (i : Fin N) (k f g : Fin 3) (hkf : k ≠ f) (hkg : k ≠ g)
    (hfg : f ≠ g) :
    ({dist ((D.tile i).pts k) ((D.tile i).pts f), dist ((D.tile i).pts k) ((D.tile i).pts g),
      dist ((D.tile i).pts f) ((D.tile i).pts g)} : Multiset ℝ) =
      {sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0} := by
  have hcase : (f = k + 1 ∧ g = k + 2) ∨ (f = k + 2 ∧ g = k + 1) := by
    revert hkf hkg hfg; revert k f g; decide
  have tm := tile_multiset D i k
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [dist_comm ((D.tile i).pts k) ((D.tile i).pts (k+2))]; exact tm
  · rw [dist_comm ((D.tile i).pts k) ((D.tile i).pts (k+2)),
      dist_comm ((D.tile i).pts (k+2)) ((D.tile i).pts (k+1))]
    exact (Multiset.cons_swap _ _ _).trans tm

/-- **At a `β`-corner whose edge to `U'` has length `c`, the other edge has length `a`.** -/
theorem beta_corner_other_edge {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (i : Fin N) (kk fi g : Fin 3) (hfk : fi ≠ kk) (hgk : g ≠ kk)
    (hgf : g ≠ fi) (hβ : (D.tile i).localAngle ((D.tile i).pts kk) = β)
    (hc : dist ((D.tile i).pts kk) ((D.tile i).pts fi) = sideOpp D.model 2) :
    dist ((D.tile i).pts kk) ((D.tile i).pts g) = sideOpp D.model 0 := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  have hm := tri_ms D i kk fi g hfk.symm hgk.symm hgf.symm
  have hc1 := tile_vertex_angle_cases D α β γ S.hα' S.hβ' S.hγ' i kk
  have hcase : (fi = kk + 1 ∧ g = kk + 2) ∨ (fi = kk + 2 ∧ g = kk + 1) := fin3_pair kk fi g hfk hgk hgf
  have hz : dist ((D.tile i).pts fi) ((D.tile i).pts g) = sideOpp D.model 1 := by
    have hopp : dist ((D.tile i).pts (kk+1)) ((D.tile i).pts (kk+2)) =
        dist ((D.tile i).pts fi) ((D.tile i).pts g) := by
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact dist_comm _ _
    rw [← hopp]
    rcases hc1 with ⟨hA, hd⟩ | ⟨hA, hd⟩ | ⟨hA, hd⟩
    · exact absurd (hβ.symm.trans hA) hαβ.symm
    · exact hd
    · exact absurd (hβ.symm.trans hA) hβγ
  rcases perm3 hm hab hbc hac with ⟨hx, hy, hz'⟩ | ⟨hx, hy, hz'⟩ | ⟨hx, hy, hz'⟩ | ⟨hx, hy, hz'⟩ |
      ⟨hx, hy, hz'⟩ | ⟨hx, hy, hz'⟩
  · exact absurd (hz.symm.trans hz') hab.symm
  · exact hy
  · exact absurd (hx.symm.trans hc) hbc
  · exact absurd (hx.symm.trans hc) hbc
  · exact absurd (hx.symm.trans hc) hac
  · exact absurd (hx.symm.trans hc) hac

#print axioms beta_corner_other_edge

/-- **The angle at a vertex from the opposite side.** -/
theorem angle_of_opp (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hab : sideOpp D.model 0 ≠ sideOpp D.model 1) (hbc : sideOpp D.model 1 ≠ sideOpp D.model 2)
    (hac : sideOpp D.model 0 ≠ sideOpp D.model 2) (i : Fin N) (m n o : Fin 3) (h1 : m ≠ n)
    (h2 : m ≠ o) (h3 : n ≠ o) :
    (dist ((D.tile i).pts n) ((D.tile i).pts o) = sideOpp D.model 0 →
      (D.tile i).localAngle ((D.tile i).pts m) = α) ∧
    (dist ((D.tile i).pts n) ((D.tile i).pts o) = sideOpp D.model 1 →
      (D.tile i).localAngle ((D.tile i).pts m) = β) ∧
    (dist ((D.tile i).pts n) ((D.tile i).pts o) = sideOpp D.model 2 →
      (D.tile i).localAngle ((D.tile i).pts m) = γ) := by
  have hc := tile_vertex_angle_cases D α β γ hα' hβ' hγ' i m
  have hcase : (n = m + 1 ∧ o = m + 2) ∨ (n = m + 2 ∧ o = m + 1) := fin3_pair m n o h1.symm h2.symm h3.symm
  have hopp : dist ((D.tile i).pts n) ((D.tile i).pts o) =
      dist ((D.tile i).pts (m+1)) ((D.tile i).pts (m+2)) := by
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact dist_comm _ _
  rw [hopp]
  rcases hc with ⟨hA, hd⟩ | ⟨hA, hd⟩ | ⟨hA, hd⟩
  · exact ⟨fun _ => hA, fun h => absurd (hd.symm.trans h) hab, fun h => absurd (hd.symm.trans h) hac⟩
  · exact ⟨fun h => absurd (hd.symm.trans h) hab.symm, fun _ => hA, fun h => absurd (hd.symm.trans h) hbc⟩
  · exact ⟨fun h => absurd (hd.symm.trans h) hac.symm, fun h => absurd (hd.symm.trans h) hbc.symm, fun _ => hA⟩

#print axioms angle_of_opp

end Erdos634.LaczJunction.Walk
