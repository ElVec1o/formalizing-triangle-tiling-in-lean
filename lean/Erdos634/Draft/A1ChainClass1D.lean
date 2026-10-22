-- Draft/A1ChainClass1D.lean — row0c Lemma 1 (b′), the one-dimensional core (node A1).
--
-- Formalization debt on a paper-level PROVED result (PROOF_row0c.md, P1 A1 (b′)); NOT /goal
-- progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  H59: no (e, f) evaluated.
--
-- Pure real-line statement, no geometry.  A *chain* is a finite family of nondegenerate closed
-- intervals `[a e, b e]` meeting pairwise in at most a point, each carrying a class
-- `φ (a e) = φ (b e)` (in the application `φ t` is the coset mod L of the point at parameter `t`).
--
-- * `anchor` — for `t₀` in the chain's union, let `p` be the left end of the connected component
--   of the union through `t₀`.  Then EVERY chain interval through `t₀` has class `φ p`.  Route:
--   `p` is a left endpoint of a chain interval (it lies in one, and that interval sits in the
--   component); split the component into the closed unions of the good (class `φ p`) and bad
--   intervals; a common point lies on two distinct intervals, hence (at-most-a-point
--   intersection) is an endpoint of both, so the classes agree.  This replaces the paper's
--   "chain P = c₀, c₁, …, c_m = Q" and needs no sorting and no maximal segment object.
-- * `class_eq` — two chains (the two sides of a line), each covering whatever the other covers
--   to the left of `t₀` (`htr₁`, `htr₂`, supplied in the plane by `Dissection.wall_cover`), have
--   the same component left end, so any two intervals of either chain through `t₀` share a class.
import Mathlib

namespace Erdos634.Geometry.A1Pos

open Set

/-- A point strictly inside `[a, b]` and in a nondegenerate `[c, d]` gives two common points. -/
theorem not_subsingleton_of_mem_Ioo {a b c d y : ℝ} (hcd : c < d) (hy : y ∈ Ioo a b)
    (hy2 : y ∈ Icc c d) (hsub : (Icc a b ∩ Icc c d).Subsingleton) : False := by
  have hyin : y ∈ Icc a b ∩ Icc c d := ⟨Ioo_subset_Icc_self hy, hy2⟩
  rcases lt_or_eq_of_le hy2.2 with hyd | hyd
  · have hmin : y < min b d := lt_min hy.2 hyd
    have hz : (y + min b d) / 2 ∈ Icc a b ∩ Icc c d := by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · linarith [hy.1]
      · linarith [min_le_left b d]
      · linarith [hy2.1]
      · linarith [min_le_right b d]
    have := hsub hz hyin
    linarith
  · have hcy : c < y := hyd ▸ hcd
    have hmax : max a c < y := max_lt hy.1 hcy
    have hz : (max a c + y) / 2 ∈ Icc a b ∩ Icc c d := by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · linarith [le_max_left a c]
      · linarith [hy.2]
      · linarith [le_max_right a c]
      · linarith [hy2.2]
    have := hsub hz hyin
    linarith

/-- Two nondegenerate closed intervals meeting in at most a point meet only at endpoints. -/
theorem endpoint_of_subsingleton {a b c d y : ℝ} (hab : a < b) (hcd : c < d)
    (hsub : (Icc a b ∩ Icc c d).Subsingleton) (h1 : y ∈ Icc a b) (h2 : y ∈ Icc c d) :
    (y = a ∨ y = b) ∧ (y = c ∨ y = d) := by
  constructor
  · by_contra h
    push Not at h
    exact not_subsingleton_of_mem_Ioo hcd
      ⟨lt_of_le_of_ne h1.1 (Ne.symm h.1), lt_of_le_of_ne h1.2 h.2⟩ h2 hsub
  · by_contra h
    push Not at h
    rw [inter_comm] at hsub
    exact not_subsingleton_of_mem_Ioo hab
      ⟨lt_of_le_of_ne h2.1 (Ne.symm h.1), lt_of_le_of_ne h2.2 h.2⟩ h1 hsub

variable {ι Q : Type*}

/-- The union of a chain's intervals. -/
def chainUnion (S : Finset ι) (a b : ι → ℝ) : Set ℝ := ⋃ e ∈ S, Icc (a e) (b e)

theorem isClosed_chainUnion (S : Finset ι) (a b : ι → ℝ) : IsClosed (chainUnion S a b) :=
  S.finite_toSet.isClosed_biUnion fun _ _ => isClosed_Icc

theorem isCompact_chainUnion (S : Finset ι) (a b : ι → ℝ) : IsCompact (chainUnion S a b) :=
  S.finite_toSet.isCompact_biUnion fun _ _ => isCompact_Icc

/-- The chain hypotheses: nondegenerate intervals, pairwise meeting in at most a point, endpoint
classes equal. -/
structure IsChain (S : Finset ι) (a b : ι → ℝ) (φ : ℝ → Q) : Prop where
  lt : ∀ e ∈ S, a e < b e
  disj : ∀ e ∈ S, ∀ e' ∈ S, e ≠ e' → (Icc (a e) (b e) ∩ Icc (a e') (b e')).Subsingleton
  cls : ∀ e ∈ S, φ (a e) = φ (b e)

/-- **Anchor.**  The left end `p` of the component of the chain union through `t₀` has the
minimality property, and every chain interval through `t₀` carries the class `φ p`. -/
theorem anchor {S : Finset ι} {a b : ι → ℝ} {φ : ℝ → Q} (hS : IsChain S a b φ) {t₀ : ℝ}
    (ht₀ : t₀ ∈ chainUnion S a b) :
    ∃ p ≤ t₀, Icc p t₀ ⊆ chainUnion S a b ∧
      (∀ p', p' ≤ t₀ → Icc p' t₀ ⊆ chainUnion S a b → p ≤ p') ∧
      ∀ e ∈ S, t₀ ∈ Icc (a e) (b e) → φ (a e) = φ p := by
  classical
  set U := chainUnion S a b with hU
  set C := connectedComponentIn U t₀ with hC
  have hUc : IsClosed U := isClosed_chainUnion S a b
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have ht₀C : t₀ ∈ C := mem_connectedComponentIn ht₀
  have hCU : C ⊆ U := connectedComponentIn_subset U t₀
  have hCclosed : IsClosed C := by
    have hcl : closure C ⊆ C :=
      hCpre.closure.subset_connectedComponentIn (subset_closure ht₀C)
        (closure_minimal hCU hUc)
    exact closure_subset_iff_isClosed.mp hcl
  have hCbdd : BddBelow C := ((isCompact_chainUnion S a b).bddBelow).mono hCU
  have hCne : C.Nonempty := ⟨t₀, ht₀C⟩
  set p := sInf C with hp
  have hpC : p ∈ C := hCclosed.csInf_mem hCne hCbdd
  have hpt : p ≤ t₀ := csInf_le hCbdd ht₀C
  -- any preconnected subset of `U` meeting `C` lies in `C`
  have hsubC : ∀ s : Set ℝ, IsPreconnected s → s ⊆ U → ∀ y ∈ s, y ∈ C → s ⊆ C := by
    intro s hs hsU y hys hyC
    have := hs.subset_connectedComponentIn hys hsU
    rwa [← connectedComponentIn_eq hyC] at this
  have hIcc : Icc p t₀ ⊆ C := hCpre.Icc_subset hpC ht₀C
  refine ⟨p, hpt, hIcc.trans hCU, ?_, ?_⟩
  · intro p' hp' hsub
    have : Icc p' t₀ ⊆ C :=
      hsubC _ isPreconnected_Icc hsub t₀ ⟨hp', le_rfl⟩ ht₀C
    exact csInf_le hCbdd (this ⟨le_rfl, hp'⟩)
  -- `p` is the left endpoint of a chain interval
  obtain ⟨e₀, he₀S, hpe₀⟩ : ∃ e ∈ S, p ∈ Icc (a e) (b e) := by
    have := hCU hpC
    simp only [hU, chainUnion, mem_iUnion] at this
    obtain ⟨e, he, hpe⟩ := this
    exact ⟨e, he, hpe⟩
  have hae₀ : a e₀ = p := by
    have hsub : Icc (a e₀) (b e₀) ⊆ C := by
      refine hsubC _ isPreconnected_Icc ?_ p hpe₀ hpC
      intro z hz
      simp only [hU, chainUnion, mem_iUnion]
      exact ⟨e₀, he₀S, hz⟩
    have h1 : p ≤ a e₀ := csInf_le hCbdd (hsub ⟨le_rfl, (hS.lt e₀ he₀S).le⟩)
    exact le_antisymm hpe₀.1 h1
  -- split `C` into good and bad intervals
  intro e heS he₀
  by_contra hbad
  let G : Set ℝ := ⋃ e' ∈ S.filter (fun e' => φ (a e') = φ p), Icc (a e') (b e')
  let B : Set ℝ := ⋃ e' ∈ S.filter (fun e' => φ (a e') ≠ φ p), Icc (a e') (b e')
  have hGc : IsClosed G := (Finset.finite_toSet _).isClosed_biUnion fun _ _ => isClosed_Icc
  have hBc : IsClosed B := (Finset.finite_toSet _).isClosed_biUnion fun _ _ => isClosed_Icc
  have hcov : C ⊆ G ∪ B := by
    intro z hz
    have := hCU hz
    simp only [hU, chainUnion, mem_iUnion] at this
    obtain ⟨e', he', hz'⟩ := this
    by_cases hg : φ (a e') = φ p
    · left
      exact mem_biUnion (Finset.mem_filter.mpr ⟨he', hg⟩) hz'
    · right
      exact mem_biUnion (Finset.mem_filter.mpr ⟨he', hg⟩) hz'
  have hG : (C ∩ G).Nonempty :=
    ⟨p, hpC, mem_biUnion (Finset.mem_filter.mpr ⟨he₀S, by rw [hae₀]⟩) hpe₀⟩
  have hB : (C ∩ B).Nonempty :=
    ⟨t₀, ht₀C, mem_biUnion (Finset.mem_filter.mpr ⟨heS, hbad⟩) he₀⟩
  obtain ⟨y, -, hyG, hyB⟩ := isPreconnected_closed_iff.mp hCpre G B hGc hBc hcov hG hB
  obtain ⟨e₁, he₁, hy₁⟩ := mem_iUnion₂.mp hyG
  obtain ⟨e₂, he₂, hy₂⟩ := mem_iUnion₂.mp hyB
  rw [Finset.mem_filter] at he₁ he₂
  have hne : e₁ ≠ e₂ := by
    rintro rfl
    exact he₂.2 he₁.2
  obtain ⟨hy1, hy2⟩ := endpoint_of_subsingleton (hS.lt e₁ he₁.1) (hS.lt e₂ he₂.1)
    (hS.disj e₁ he₁.1 e₂ he₂.1 hne) hy₁ hy₂
  have hφ1 : φ y = φ (a e₁) := by
    rcases hy1 with h | h
    · rw [h]
    · rw [h, hS.cls e₁ he₁.1]
  have hφ2 : φ y = φ (a e₂) := by
    rcases hy2 with h | h
    · rw [h]
    · rw [h, hS.cls e₂ he₂.1]
  exact he₂.2 (hφ2.symm.trans (hφ1.trans he₁.2))

/-- **Two sides of a line.**  If each chain covers whatever the other covers to the left of `t₀`,
any two intervals (of either chain) through `t₀` have the same class. -/
theorem class_eq {S T : Finset ι} {a b : ι → ℝ} {φ : ℝ → Q} (hS : IsChain S a b φ)
    (hT : IsChain T a b φ) {t₀ : ℝ}
    (htr₁ : ∀ p < t₀, Icc p t₀ ⊆ chainUnion S a b → Icc p t₀ ⊆ chainUnion T a b)
    (htr₂ : ∀ p < t₀, Icc p t₀ ⊆ chainUnion T a b → Icc p t₀ ⊆ chainUnion S a b)
    {e e' : ι} (he : e ∈ S ∨ e ∈ T) (he' : e' ∈ S ∨ e' ∈ T)
    (h0 : t₀ ∈ Icc (a e) (b e)) (h0' : t₀ ∈ Icc (a e') (b e')) :
    φ (a e) = φ (a e') := by
  have memU : ∀ {R : Finset ι} {g : ι}, g ∈ R → t₀ ∈ Icc (a g) (b g) → t₀ ∈ chainUnion R a b :=
    fun hg h => mem_biUnion hg h
  -- the two anchors coincide when both chains reach `t₀`
  have key : t₀ ∈ chainUnion S a b → t₀ ∈ chainUnion T a b →
      ∃ p, (∀ g ∈ S, t₀ ∈ Icc (a g) (b g) → φ (a g) = φ p) ∧
        (∀ g ∈ T, t₀ ∈ Icc (a g) (b g) → φ (a g) = φ p) := by
    intro hs ht
    obtain ⟨p, hp, hpU, hpmin, hpcls⟩ := anchor hS hs
    obtain ⟨q, hq, hqU, hqmin, hqcls⟩ := anchor hT ht
    have hqp : q ≤ p := by
      rcases lt_or_eq_of_le hp with h | h
      · exact hqmin p hp (htr₁ p h hpU)
      · rw [h]; exact hq
    have hpq : p ≤ q := by
      rcases lt_or_eq_of_le hq with h | h
      · exact hpmin q hq (htr₂ q h hqU)
      · rw [h]; exact hp
    have heq : p = q := le_antisymm hpq hqp
    exact ⟨p, hpcls, fun g hg h => by rw [hqcls g hg h, heq]⟩
  rcases he with he | he <;> rcases he' with he' | he'
  · obtain ⟨p, -, -, -, hcls⟩ := anchor hS (memU he h0)
    rw [hcls e he h0, hcls e' he' h0']
  · obtain ⟨p, h1, h2⟩ := key (memU he h0) (memU he' h0')
    rw [h1 e he h0, h2 e' he' h0']
  · obtain ⟨p, h1, h2⟩ := key (memU he' h0') (memU he h0)
    rw [h2 e he h0, h1 e' he' h0']
  · obtain ⟨p, -, -, -, hcls⟩ := anchor hT (memU he h0)
    rw [hcls e he h0, hcls e' he' h0']

end Erdos634.Geometry.A1Pos

#print axioms Erdos634.Geometry.A1Pos.anchor
#print axioms Erdos634.Geometry.A1Pos.class_eq
