-- Draft/LaczFormalRG12GExc.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, the graph Gamma_except: (a) the DEFINITION `GExc` (gamma-run clause, shaped like `GaEdge`/`RunEnd`, with `Y` the nearer of `U_{i0}, V_{j0}`),
-- (b) the FIG. 5 case split at a vertex of Gamma_kite in the form needed for statement (i): at a vertex `V` of Gamma_kite (an interior (2,2,2) vertex carrying a kite 2*beta = the head of `GKite X V` and a
-- kite 2*alpha = the tail of `GKite V Z`) there is NO straight line of tile sides through `V` such that both tiles flanking one ray of it have angle gamma at `V` (`kite_vertex_no_gamma_line`).
-- Route: `fan222_tile` gives the six sectors in cyclic order with labels; the two kites are pairs of CONSECUTIVE sectors (labels beta,beta and alpha,alpha: `next_sector`); a straight line forces the triples
-- `(gamma, x, y)` and `(z, t, gamma)` with `{x,y} = {z,t} = {alpha, beta}` (`straight_run_labels`), and then the beta pair and the alpha pair cannot both be adjacent (`fig5_comb`).  This is the printed
-- exclusion of Fig. 5 (A) and (B) (the printed text uses 2alpha+gamma != pi and "not supported by a common segment"; the figure was read from the PDF, p. 357).
-- Hypotheses: `HasFansC`, `AngGen` for the model angles (alpha, beta, gamma pairwise distinct, none right: named, witnessed by `angGen_witness`), gamma < pi/2, != pi/3, `CaseC`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2, Lemma 6.2, Fig. 5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12Fan222Tile
import Erdos634.Draft.LaczFormalRG12GKiteEx

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-! ## (a) The graph `Γ_except` -/

/-- The tile of the division element `e = (tile, tail, head)` has angle `γ` (label 2) at its HEAD. -/
def GammaHead (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (e : Fin N × Plane × Plane) : Prop :=
  ∃ k, (D.tile e.1).pts k = e.2.2 ∧ idx e.1 k = 2

/-- **The `γ`-run of a division** (paper: the maximal index `i_0` such that `T_i` has angle `γ` at `U_i` for every `i ≤ i_0`): the division `L` is a nonempty prefix `L'` of elements with `γ` at their head, followed
by `L''` whose first element (if any) does not have `γ` at its head; `H` is the head of the last element of `L'` (the point `U_{i_0}`). -/
def GRunEnd (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (L : List (Fin N × Plane × Plane)) (H : Plane) : Prop :=
  ∃ L' L'' : List (Fin N × Plane × Plane), L = L' ++ L'' ∧ L' ≠ [] ∧ (∀ x ∈ L', GammaHead D idx x) ∧
    (∀ e ∈ L''.head?, ¬ GammaHead D idx e) ∧ ∃ e0, L'.getLast? = some e0 ∧ e0.2.2 = H

/-- **The edges of `Γ_except`** (Laczkovich, DCG 48 (2012), Sect. 6.2, l. 1318-1334).  `X → Y` iff `X` is the start of a maximal segment `XZ` (both divisions nonempty, ending together at `Z`; the segment lies in the
interior of `A` except perhaps its ends because tiles lie on both sides), the first tile of each division has angle `γ` at its far end, the `γ`-runs of the two divisions end at `H1` (left, `U_{i_0}`) and `H2` (right,
`V_{j_0}`), and `Y` is the nearer to `X` (`Y = U_{i_0} = V_{j_0}` if they are equally near).  (Both points lie on the ray from `X` along `d`, so equal distance means equal point.) -/
def GExc (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (X Y : Plane) : Prop :=
  ∃ (d : V2) (Z : Plane) (L1 L2 : List (Fin N × Plane × Plane)) (H1 H2 : Plane),
    d ≠ 0 ∧ NoBack D.toRegionDissection d X ∧ WalkT D.toRegionDissection d X Z L1 ∧ WalkR D.toRegionDissection d X Z L2 ∧ L1 ≠ [] ∧ L2 ≠ [] ∧
    (∀ i U', ¬ TriStep (D.tile i) d Z U') ∧ (∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Z) ∧
    GRunEnd D idx L1 H1 ∧ GRunEnd D idx L2 H2 ∧
    ((Y = H1 ∧ dist X H1 ≤ dist X H2) ∨ (Y = H2 ∧ dist X H2 ≤ dist X H1))

/-! ## (b) Fig. 5 -/

/-- A sector of the fan whose tile has a left side starting at `V` along `d` has its start ray along `d`. -/
theorem sec_start {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) {i : Fin N} {d : V2} {U : Plane}
    (h : TriStep (D.tile i) d V U) : ∃ x : AtV D V, x.1 = i ∧ Par (F.p x) d := by
  obtain ⟨kk, f, g, hk, -⟩ := id h
  have hmem : V ∈ (D.tile i).carrier := hk ▸ subset_convexHull ℝ _ ⟨kk, rfl⟩
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec ⟨i, hmem⟩) ⟨kk, hk⟩
  exact ⟨⟨i, hmem⟩, rfl, triStep_start h kk2 fl2 hk2 hp2 hq2 (F.hok _)⟩

/-- A sector of the fan whose tile has a left side ending at `V` along `d` has its end ray along `-d`. -/
theorem sec_end {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) {i : Fin N} {d : V2} {U : Plane}
    (h : TriStep (D.tile i) d U V) : ∃ x : AtV D V, x.1 = i ∧ Par (F.q x) (neg2 d) := by
  obtain ⟨kk, f, g, hk, hf, -⟩ := id h
  have hmem : V ∈ (D.tile i).carrier := hf ▸ subset_convexHull ℝ _ ⟨f, rfl⟩
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec ⟨i, hmem⟩) ⟨f, hf⟩
  exact ⟨⟨i, hmem⟩, rfl, triStep_end h kk2 fl2 hk2 hp2 hq2 (F.hok _)⟩

/-- Consecutive sectors: if the end ray of the sector `s_j` and the start ray of the sector `y` are parallel then `y = s_{j+1}`. -/
theorem next_sector {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) (s : ℕ → AtV D V)
    (hpar : ∀ j, Par (F.p (s (j + 1))) (F.q (s j))) {j : ℕ} {y : AtV D V} {r : V2}
    (hq : Par (F.q (s j)) r) (hp : Par (F.p y) r) : y = s (j + 1) := by
  by_contra hne
  have hdis := tiles_disjoint D V F.p F.q F.hloc
  exact start_inj F.p F.q F.hok hdis hne ((hpar j).trans (hq.trans hp.symm))

/-- The label of a sector is the angle label of the corner of its tile at `V`. -/
theorem label_eq {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} {V : Plane} {s : ℕ → AtV D.toRegionDissection V} {ℓ : ℕ → Fin 3}
    (hlab : ∀ j, ∃ k, (D.tile (s j).1).pts k = V ∧ idx (s j).1 k = ℓ j) {j : ℕ} {i : Fin N} (hi : (s j).1 = i) {k : Fin 3}
    (hk : (D.tile i).pts k = V) : idx i k = ℓ j := by
  obtain ⟨k', hk', hl⟩ := hlab j
  rw [hi] at hk' hl
  have : k' = k := (D.tile i).indep.injective (hk'.trans hk.symm)
  rw [← this]; exact hl

theorem not_par_neg2 {d : V2} (hd : d ≠ 0) : ¬ Par d (neg2 d) := by
  rintro ⟨-, h⟩
  unfold dt neg2 at h
  simp only at h
  have h1 : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hd (Prod.ext hh.1 hh.2)
  rcases h1 with h1 | h1 <;> nlinarith [sq_pos_of_ne_zero h1, sq_nonneg d.1, sq_nonneg d.2]

theorem par_neg_swap {u v : V2} (h : Par u (neg2 v)) : Par v (neg2 u) := by
  have := par_neg h
  rw [neg2_neg2] at this
  exact this.symm

theorem par_of_neg_par {u v : V2} (h : Par u (neg2 v)) : Par (neg2 u) v := by
  have := par_neg h
  rw [neg2_neg2] at this
  exact this

theorem per_mod {α : Type*} (f : ℕ → α) (hper : ∀ n, f (n + 6) = f n) : ∀ n, f n = f (n % 6) := by
  have key : ∀ q r, f (r + 6 * q) = f r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih => intro r; rw [show r + 6 * (q + 1) = (r + 6 * q) + 6 by ring, hper, ih]
  intro n
  have := key (n / 6) (n % 6)
  rw [Nat.mod_add_div] at this
  exact this

/-- **Fig. 5, the combinatorial core.**  Labels `ℓ : ℕ → Fin 3` of six cyclic sectors (period 6); if the corners `a, a+1` carry `γ` and a straight line makes `(a+1, a+2, a+3)` and `(a+4, a+5, a+6)` triples of different
labels, then the two `β` corners and the two `α` corners cannot BOTH be adjacent. -/
theorem fig5_comb (ℓ : ℕ → Fin 3) (hper : ∀ n, ℓ (n + 6) = ℓ n) {a b c : ℕ} (ha0 : ℓ a = 2) (ha1 : ℓ (a + 1) = 2)
    (h1 : ℓ (a + 1) ≠ ℓ (a + 2) ∧ ℓ (a + 1) ≠ ℓ (a + 3) ∧ ℓ (a + 2) ≠ ℓ (a + 3))
    (h2 : ℓ (a + 4) ≠ ℓ (a + 5) ∧ ℓ (a + 4) ≠ ℓ (a + 6) ∧ ℓ (a + 5) ≠ ℓ (a + 6))
    (hb : ℓ b = 1 ∧ ℓ (b + 1) = 1) (hc : ℓ c = 0 ∧ ℓ (c + 1) = 0) : False := by
  have hm := per_mod ℓ hper
  have hI : ∀ n, ∃ i < 6, ℓ n = ℓ (a + i) ∧ ℓ (n + 1) = ℓ (a + i + 1) := by
    intro n
    refine ⟨(n % 6 + 6 - a % 6) % 6, by omega, ?_, ?_⟩
    · rw [hm n, hm (a + (n % 6 + 6 - a % 6) % 6)]; congr 1; omega
    · rw [hm (n + 1), hm (a + (n % 6 + 6 - a % 6) % 6 + 1)]; congr 1; omega
  obtain ⟨i, hi, hbi, hbi'⟩ := hI b
  obtain ⟨j, hj, hcj, hcj'⟩ := hI c
  have e6 : ℓ (a + 6) = ℓ a := hper a
  have bnd : ∀ n, (ℓ n).val < 3 := fun n => (ℓ n).isLt
  have ne : ∀ {x y : ℕ}, ℓ x ≠ ℓ y → (ℓ x).val ≠ (ℓ y).val := fun h e => h (Fin.ext e)
  have v2 : ∀ {x : ℕ}, ℓ x = 2 → (ℓ x).val = 2 := fun h => by rw [h]; rfl
  have v1 : ∀ {x : ℕ}, ℓ x = 1 → (ℓ x).val = 1 := fun h => by rw [h]; rfl
  have v0 : ∀ {x : ℕ}, ℓ x = 0 → (ℓ x).val = 0 := fun h => by rw [h]; rfl
  have e6v : (ℓ (a + 6)).val = (ℓ a).val := by rw [e6]
  obtain ⟨b1, b2⟩ := hb
  obtain ⟨c1, c2⟩ := hc
  rw [hbi] at b1
  rw [hbi'] at b2
  rw [hcj] at c1
  rw [hcj'] at c2
  have := v2 ha0
  have := v2 ha1
  have := ne h1.1
  have := ne h1.2.1
  have := ne h1.2.2
  have := ne h2.1
  have := ne h2.2.1
  have := ne h2.2.2
  have := v1 b1
  have := v1 b2
  have := v0 c1
  have := v0 c2
  have := bnd (a + 2)
  have := bnd (a + 3)
  have := bnd (a + 4)
  have := bnd (a + 5)
  interval_cases i <;> interval_cases j <;> (try simp only [add_assoc, Nat.reduceAdd, Nat.add_zero] at *) <;> omega

set_option maxHeartbeats 3200000 in
/-- **Fig. 5 / statement (i) core.**  Let `V` be a vertex of Gamma_kite (head of `GKite X V`, tail of `GKite V Z`).  There is NO straight line `±d` of tile sides through `V` (a tile `i2` starts at `V` along `d`) such that
the left tile `i` ending at `V` along `d` and the right tile `j` starting at `V` along `-d` (the two tiles flanking the ray `-d`) both have angle `γ` at `V`. -/
theorem kite_vertex_no_gamma_line [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (G : AngGen (fun l => D.model.angleAt l)) {X V Z : Plane} (hXV : GKite D idx X V) (hVZ : GKite D idx V Z)
    {d : V2} {A B W : Plane} {i j i2 : Fin N} (hi : TriStep (D.tile i) d A V) (hj : TriStep (D.tile j) (neg2 d) V B) (hnext : TriStep (D.tile i2) d V W)
    (hgi : ∃ k, (D.tile i).pts k = V ∧ idx i k = 2) (hgj : ∃ k, (D.tile j).pts k = V ∧ idx j k = 2) : False := by
  classical
  obtain ⟨⟨hVint, c0, c1, c2⟩, -⟩ := gkite_vertex_type D P hreg idx hC.hidxA hC.hregc h1 h3 hXV
  obtain ⟨F, s, ℓ, hF, hlab, hsurj, hperS⟩ := fan222_tile D idx hC.hidxA hVint c0 c1 c2 G
  have hpar : ∀ j, Par (F.p (s (j + 1))) (F.q (s j)) := fun j => hF.hpar j
  -- periodicity of labels, shift-surjectivity of sectors
  have hmodS := per_mod s hperS
  have hperL : ∀ n, ℓ (n + 6) = ℓ n := by
    intro n
    obtain ⟨k, hk, -⟩ := hlab n
    have hk' : (D.tile (s (n + 6)).1).pts k = V := by rw [hperS n]; exact hk
    have h1' := label_eq hlab (j := n + 6) rfl hk'
    have h2' := label_eq hlab (j := n) rfl hk
    rw [← h1', ← h2', hperS n]
  have hshift : ∀ (c : ℕ) (x : AtV D.toRegionDissection V), ∃ m < 6, s (c + m) = x := by
    intro c x
    obtain ⟨j0, hj0, hsj⟩ := hsurj x
    refine ⟨(j0 + 6 - c % 6) % 6, by omega, ?_⟩
    rw [hmodS (c + (j0 + 6 - c % 6) % 6), ← hsj, hmodS j0]
    congr 1; omega
  -- the three sectors on the line
  obtain ⟨x1, hx1i, hx1q⟩ := sec_end F hi
  obtain ⟨x2, hx2i, hx2p⟩ := sec_start F hj
  obtain ⟨x3, hx3i, hx3p⟩ := sec_start F hnext
  obtain ⟨a0, -, hsa0⟩ := hsurj x1
  have hx2 : x2 = s (a0 + 1) := next_sector F s hpar (j := a0) (by rw [hsa0]; exact hx1q) hx2p
  -- labels gamma at a0, a0+1
  obtain ⟨kgi, hkgi, hgli⟩ := hgi
  obtain ⟨kgj, hkgj, hglj⟩ := hgj
  have hla : ℓ a0 = 2 := by
    rw [← hgli]; exact (label_eq hlab (j := a0) (by rw [hsa0]; exact hx1i) hkgi).symm
  have hla1 : ℓ (a0 + 1) = 2 := by
    rw [← hglj]; exact (label_eq hlab (j := a0 + 1) (by rw [← hx2]; exact hx2i) hkgj).symm
  -- the straight line: x3 = s (a0 + 1 + m)
  obtain ⟨m, hm6, hsm⟩ := hshift (a0 + 1) x3
  have hd0 : d ≠ 0 := by
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar0, hleft⟩ := id hnext
    exact hpar0.ne_right
  have hopp : Par (F.p (s (a0 + 1 + m))) (neg2 (F.p (s (a0 + 1)))) := by
    rw [hsm, ← hx2]
    exact hx3p.trans (par_of_neg_par hx2p).symm
  have hm0 : m ≠ 0 := by
    intro h0
    subst h0
    simp only [Nat.add_zero] at hsm
    have hx32 : x3 = x2 := by rw [← hsm, hx2]
    rw [hx32] at hx3p
    exact not_par_neg2 hd0 (hx3p.symm.trans hx2p)
  obtain ⟨hm3, hl12, hl13, hl23⟩ := straight_run_labels G hF (a0 + 1) m (by omega) (by omega) hopp
  subst hm3
  -- second triple: from the ray of s (a0+4) to the ray of s (a0+7) = s (a0+1)
  have hopp2 : Par (F.p (s (a0 + 4 + 3))) (neg2 (F.p (s (a0 + 4)))) := by
    have e7 : a0 + 4 + 3 = (a0 + 1) + 6 := by omega
    have e4 : a0 + 4 = a0 + 1 + 3 := by omega
    rw [e7, hperS, e4]
    exact par_neg_swap hopp
  obtain ⟨-, hl45, hl46, hl56⟩ := straight_run_labels G hF (a0 + 4) 3 (by omega) (by omega) hopp2
  -- the beta kite (head of XV): consecutive sectors with label 1
  obtain ⟨iB, jB, dB, kkB, fB, kkB', fB', -, hSiB, hSjB, -, hfB, -, hifB, hkB', -, hjkB, -⟩ := hXV
  obtain ⟨yB1, hyB1i, hyB1q⟩ := sec_end F hSiB
  obtain ⟨yB2, hyB2i, hyB2p⟩ := sec_start F hSjB
  obtain ⟨b0, -, hsb0⟩ := hsurj yB1
  have hyB2 : yB2 = s (b0 + 1) := next_sector F s hpar (j := b0) (by rw [hsb0]; exact hyB1q) hyB2p
  have hlb : ℓ b0 = 1 := by
    rw [← hifB]; exact (label_eq hlab (j := b0) (by rw [hsb0]; exact hyB1i) hfB).symm
  have hlb1 : ℓ (b0 + 1) = 1 := by
    rw [← hjkB]; exact (label_eq hlab (j := b0 + 1) (by rw [← hyB2]; exact hyB2i) hkB').symm
  -- the alpha kite (tail of VZ): consecutive sectors with label 0
  obtain ⟨iA, jA, dA, kkA, fA, kkA', fA', -, hSiA, hSjA, hkA, -, hikA, -, -, hfA', -, hjfA⟩ := hVZ
  obtain ⟨yA2, hyA2i, hyA2p⟩ := sec_start F hSiA
  obtain ⟨yA1, hyA1i, hyA1q⟩ := sec_end F hSjA
  obtain ⟨c0', -, hsc0⟩ := hsurj yA1
  have hyA2 : yA2 = s (c0' + 1) := next_sector F s hpar (j := c0') (r := dA) (by rw [hsc0]; rw [neg2_neg2'] at hyA1q; exact hyA1q) hyA2p
  have hlc : ℓ c0' = 0 := by
    rw [← hjfA]; exact (label_eq hlab (j := c0') (by rw [hsc0]; exact hyA1i) hfA').symm
  have hlc1 : ℓ (c0' + 1) = 0 := by
    rw [← hikA]; exact (label_eq hlab (j := c0' + 1) (by rw [← hyA2]; exact hyA2i) hkA).symm
  exact fig5_comb ℓ hperL hla hla1 ⟨hl12, hl13, hl23⟩ ⟨hl45, hl46, hl56⟩ ⟨hlb, hlb1⟩ ⟨hlc, hlc1⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.fig5_comb
#print axioms Erdos634.Draft.LaczFormal.RG.kite_vertex_no_gamma_line
