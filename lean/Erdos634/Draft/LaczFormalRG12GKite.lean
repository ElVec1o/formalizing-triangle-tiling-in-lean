-- Draft/LaczFormalRG12GKite.lean -- Laczkovich (DCG 48 (2012)), proof of Lemma 6.2, the graph Gamma_kite: `GKite D idx X Y` = "the segment XY is the common side of two tiles (on opposite sides) having angle alpha at X and beta at Y"
-- (labels idx = 0 / 1; the side XY is then the side `c`).  Proved here (local, no topology): an endpoint of an edge of Gamma_kite is an INTERIOR vertex of type `p = r = 2` (`2 alpha + 2 beta + 2 gamma = 2 pi`) -- `gkite_vertex_type`
-- (paper: "Y is in the interior of A ... p = r = 2") -- and each vertex has at most one outgoing and at most one incoming edge (`gkite_succ_le_one`, `gkite_pred_le_one`), because it carries exactly two alpha-corners
-- and two beta-corners.  EXISTENCE of the outgoing edge (paper: "there is exactly one kite having angle 2 alpha at Y") is in `LaczFormalRG12GKiteEx` (`gkite_succ_exists`, `gkite_succ_unique`, `gkite_pred_unique`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 6.2, 4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12L61Final

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- `XY` is an edge of Gamma_kite: two distinct tiles lie on opposite sides of the segment `XY`, each has `XY` as a side, both with angle alpha (label 0) at `X` and beta (label 1) at `Y`. -/
def GKite (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (X Y : Plane) : Prop :=
  ∃ (i j : Fin N) (d : V2) (kk f kk' f' : Fin 3), i ≠ j ∧ TriStep (D.tile i) d X Y ∧ TriStep (D.tile j) (neg2 d) Y X ∧
    (D.tile i).pts kk = X ∧ (D.tile i).pts f = Y ∧ idx i kk = 0 ∧ idx i f = 1 ∧
    (D.tile j).pts kk' = Y ∧ (D.tile j).pts f' = X ∧ idx j kk' = 1 ∧ idx j f' = 0

theorem two_le_cnt {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} {i j : Fin N} {a b : Fin 3} {Y : Plane} {l : Fin 3}
    (hij : i ≠ j) (h1 : (D.tile i).pts a = Y) (h2 : idx i a = l) (h3 : (D.tile j).pts b = Y) (h4 : idx j b = l) : 2 ≤ cnt D idx Y l := by
  unfold cnt
  apply Finset.one_lt_card.2
  refine ⟨(i, a), ?_, (j, b), ?_, ?_⟩
  · simp [h1, h2]
  · simp [h3, h4]
  · simp [hij]

/-- A tiling vertex carrying at least two alpha-corners (hence two beta-corners) is an interior vertex of type `(2, 2, 2)`. -/
theorem vertex_222 [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) {Y : Plane} (hvert : ∃ j k, (D.tile j).pts k = Y)
    (h2 : 2 ≤ cnt D idx Y 1) :
    Y ∈ interior D.region ∧ cnt D idx Y 0 = 2 ∧ cnt D idx Y 1 = 2 ∧ cnt D idx Y 2 = 2 := by
  have hpi := Real.pi_pos
  have hγ0 := model_angle_pos' D 2
  have hAs := Asum_eq D idx hregc Y
  have hp : (2 : ℝ) ≤ (cnt D idx Y 0 : ℝ) := by exact_mod_cast (hregc Y ▸ h2)
  have hr0 : (0 : ℝ) ≤ (cnt D idx Y 2 : ℝ) := Nat.cast_nonneg _
  have hbig : Real.pi < Asum D idx Y := by
    rw [hAs]; nlinarith [mul_nonneg hr0 hγ0.le]
  have hint : Y ∈ interior D.region ∧ Asum D idx Y = 2 * Real.pi := by
    rcases vertex_A D P hreg idx hidxA hvert with ⟨hi, h | h⟩ | ⟨hni, h | ⟨k, -, hk⟩⟩
    · exact ⟨hi, h⟩
    · linarith
    · linarith
    · have := (polyAngle_bounds P (k + 1)).2; linarith
  obtain ⟨hi, hA2⟩ := hint
  rw [hAs] at hA2
  have hle : cnt D idx Y 0 ≤ cnt D idx Y 2 :=
    caseII_arith hγ0 h1 h3 (cnt D idx Y 0) (cnt D idx Y 2) 2 (Or.inr rfl) (by rw [hA2]; push_cast; ring)
  have hle' : (cnt D idx Y 0 : ℝ) ≤ (cnt D idx Y 2 : ℝ) := by exact_mod_cast hle
  have hp2 : (cnt D idx Y 0 : ℝ) = 2 := by
    by_contra hne
    have : (2 : ℝ) < (cnt D idx Y 0 : ℝ) := lt_of_le_of_ne hp (Ne.symm hne)
    nlinarith [mul_nonneg (sub_nonneg.2 hle') hγ0.le]
  have hr2 : (cnt D idx Y 2 : ℝ) = 2 := by
    by_contra hne
    have : (cnt D idx Y 0 : ℝ) < (cnt D idx Y 2 : ℝ) := lt_of_le_of_ne hle' (by intro h; apply hne; linarith)
    nlinarith [mul_pos (sub_pos.2 this) hγ0]
  have e0 : cnt D idx Y 0 = 2 := by exact_mod_cast hp2
  exact ⟨hi, e0, by rw [← hregc Y, e0], by exact_mod_cast hr2⟩

/-- **Laczkovich Lemma 6.2, first claim.**  If `XY` is an edge of Gamma_kite then `Y` (and `X`) is an interior vertex of the tiling with `p = r = 2`. -/
theorem gkite_vertex_type [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) {X Y : Plane} (h : GKite D idx X Y) :
    (Y ∈ interior D.region ∧ cnt D idx Y 0 = 2 ∧ cnt D idx Y 1 = 2 ∧ cnt D idx Y 2 = 2) ∧
    (X ∈ interior D.region ∧ cnt D idx X 0 = 2 ∧ cnt D idx X 1 = 2 ∧ cnt D idx X 2 = 2) := by
  obtain ⟨i, j, d, kk, f, kk', f', hij, -, -, hk, hf, hik, hif, hk', hf', hjk, hjf⟩ := h
  constructor
  · exact vertex_222 D P hreg idx hidxA hregc h1 h3 ⟨i, f, hf⟩ (two_le_cnt hij hf hif hk' hjk)
  · exact vertex_222 D P hreg idx hidxA hregc h1 h3 ⟨i, kk, hk⟩ (hregc X ▸ two_le_cnt hij hk hik hf' hjf)

/-- Two alpha-corners at a vertex with `cnt = 2`: any alpha-corner is one of two given ones. -/
theorem mem_of_cnt_two {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} {Y : Plane} {l : Fin 3} (hc : cnt D idx Y l = 2)
    {p q r : Fin N × Fin 3} (hp : (D.tile p.1).pts p.2 = Y ∧ idx p.1 p.2 = l) (hq : (D.tile q.1).pts q.2 = Y ∧ idx q.1 q.2 = l) (hpq : p ≠ q)
    (hr : (D.tile r.1).pts r.2 = Y ∧ idx r.1 r.2 = l) : r = p ∨ r = q := by
  by_contra hno
  push Not at hno
  have hsub : ({p, q, r} : Finset (Fin N × Fin 3)) ⊆ Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = Y ∧ idx p.1 p.2 = l) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [*]
  have h3 : ({p, q, r} : Finset (Fin N × Fin 3)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hpq, Ne.symm hno.1]), Finset.card_pair (Ne.symm hno.2)]
  have := Finset.card_le_card hsub
  rw [h3] at this
  unfold cnt at hc
  omega

/-- **At most one outgoing edge.**  Gamma_kite has out-degree `<= 1` (a vertex has exactly two alpha-corners). -/
theorem gkite_succ_le_one [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) {Y Z Z' : Plane} (h : GKite D idx Y Z) (h' : GKite D idx Y Z') : Z = Z' := by
  have hc : cnt D idx Y 0 = 2 := (gkite_vertex_type D P hreg idx hidxA hregc h1 h3 h).2.2.1
  obtain ⟨i, j, d, kk, f, kk', f', hij, -, -, hk, hf, hik, hif, hk', hf', hjk, hjf⟩ := h
  obtain ⟨i2, j2, d2, kk2, g2, kk2', g2', hij2, -, -, hk2, hf2, hik2, hif2, hk2', hf2', hjk2, hjf2⟩ := h'
  have pq : ((i, kk) : Fin N × Fin 3) ≠ (j, f') := fun e => hij (by simpa using congrArg Prod.fst e)
  have A := mem_of_cnt_two hc (p := (i, kk)) (q := (j, f')) (r := (i2, kk2)) ⟨hk, hik⟩ ⟨hf', hjf⟩ pq ⟨hk2, hik2⟩
  have B := mem_of_cnt_two hc (p := (i, kk)) (q := (j, f')) (r := (j2, g2')) ⟨hk, hik⟩ ⟨hf', hjf⟩ pq ⟨hf2', hjf2⟩
  have inj := fun t => (idx t).injective
  rcases A with A | A
  · -- tile i2 = tile i
    simp only [Prod.mk.injEq] at A
    obtain ⟨rfl, -⟩ := A
    have : f = g2 := inj i2 (hif.trans hif2.symm)
    rw [← hf, ← hf2, this]
  · simp only [Prod.mk.injEq] at A
    obtain ⟨rfl, rfl⟩ := A
    have : kk' = g2 := inj i2 (hjk.trans hif2.symm)
    rw [← hk', ← hf2, this]

/-- **At most one incoming edge.**  Gamma_kite has in-degree `<= 1` (a vertex has exactly two beta-corners). -/
theorem gkite_pred_le_one [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) {X X' Y : Plane} (h : GKite D idx X Y) (h' : GKite D idx X' Y) : X = X' := by
  have hc : cnt D idx Y 1 = 2 := (gkite_vertex_type D P hreg idx hidxA hregc h1 h3 h).1.2.2.1
  obtain ⟨i, j, d, kk, f, kk', f', hij, -, -, hk, hf, hik, hif, hk', hf', hjk, hjf⟩ := h
  obtain ⟨i2, j2, d2, kk2, g2, kk2', g2', hij2, -, -, hk2, hf2, hik2, hif2, hk2', hf2', hjk2, hjf2⟩ := h'
  have pq : ((i, f) : Fin N × Fin 3) ≠ (j, kk') := fun e => hij (by simpa using congrArg Prod.fst e)
  have A := mem_of_cnt_two hc (p := (i, f)) (q := (j, kk')) (r := (i2, g2)) ⟨hf, hif⟩ ⟨hk', hjk⟩ pq ⟨hf2, hif2⟩
  have inj := fun t => (idx t).injective
  rcases A with A | A
  · simp only [Prod.mk.injEq] at A
    obtain ⟨rfl, -⟩ := A
    have : kk = kk2 := inj i2 (hik.trans hik2.symm)
    rw [← hk, ← hk2, this]
  · simp only [Prod.mk.injEq] at A
    obtain ⟨rfl, rfl⟩ := A
    have : f' = kk2 := inj i2 (hjf.trans hik2.symm)
    rw [← hf', ← hk2, this]

end Erdos634.Draft.LaczFormal.RG
