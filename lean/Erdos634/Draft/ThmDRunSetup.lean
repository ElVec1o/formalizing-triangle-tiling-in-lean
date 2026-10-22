import Erdos634.Draft.ThmDRunTile

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' run port, module R1: the setup `SetupT` and its normal form  (UNAUDITED)

Port of `SideRunGFrame.SetupG` (section 4: `mem`, `pts_mem`, `interior_seg`, `gA_pos_of_left`, `gB_pos_of_right`,
`base_range`) and of `SideRunGThetaMain.setup_of_sides_apex_pinned` to the `γ = 2α` tile `(u², v² − u², u v)`:

* `alphaT u v = arccos (v / 2u)`, `modelAngles_of_sidesT` : a triangle with `sideOpp = (u², v²−u², uv)` has the
  corner angles `α, π − 3α, 2α` (cosine rule; `cos γ = (v² − 2u²)/(2u²) = cos 2α`).
* `SetupT` : model data + `β = π − 3α`, `γ = 2α`, `α/π` irrational (a HYPOTHESIS here, as in `IrrPi α` of `GPair`;
  `cos α = v/2u` is rational and `v/u ∉ ℤ`, so it is Niven's theorem), target `= Tg L ax ay`.
* `setup_of_sidesT_pinned` : a `CongruentDissection` whose target has the sides `(d₁, d₂, L)` of the triangle
  `Q = (0,0), B = (L,0), A = (ax,ay)` and whose model has the sides `(u², v²−u², uv)` is moved by an isometry to a `SetupT`
  with `g (τ 0) = Q`, `g (τ 1) = B`.
-/

open scoped Classical

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.TilePlacement Erdos634.Draft.SideRun Set

variable {N : ℕ}

/-! ## 1. The model angles -/

/-- `α = arccos (v / 2u)` -/
noncomputable def alphaT (u v : ℝ) : ℝ := Real.arccos (v / (2 * u))

theorem cos_alphaT {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) :
    Real.cos (alphaT u v) = v / (2 * u) := by
  unfold alphaT
  apply Real.cos_arccos
  · have : 0 < v / (2 * u) := div_pos (by linarith) (by linarith)
    linarith
  · rw [div_le_one (by positivity)]; linarith

theorem alphaT_pos {u v : ℝ} (hu : 0 < u) (hv : v < 2 * u) (hv0 : 0 < v) : 0 < alphaT u v := by
  unfold alphaT
  apply Real.arccos_pos.mpr
  rw [div_lt_one (by positivity)]; linarith

theorem alphaT_le_half_pi {u v : ℝ} (hu : 0 < u) (hv0 : 0 < v) : alphaT u v ≤ Real.pi / 2 :=
  Real.arccos_le_pi_div_two.mpr (by positivity)

theorem cornerAngle_eq_of_cosT {p q r : Plane} {a b d θ : ℝ} (ha : dist p q = a)
    (hb : dist r q = b) (hd : dist p r = d) (ha0 : 0 < a) (hb0 : 0 < b) (hθ0 : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi) (hcos : Real.cos θ = (a ^ 2 + b ^ 2 - d ^ 2) / (2 * a * b)) :
    cornerAngle p q r = θ := by
  have hlaw :=
    EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p q r
  rw [ha, hb, hd] at hlaw
  have hc : Real.cos (cornerAngle p q r) = Real.cos θ := by
    rw [hcos]; unfold cornerAngle; field_simp; linarith
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨hθ0, hθπ⟩ hc

/-- **The model angles from the model sides.** -/
theorem modelAngles_of_sidesT (R : Tri) {u v : ℕ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u)
    (hs0 : sideOpp R 0 = (u : ℝ) ^ 2) (hs1 : sideOpp R 1 = (v : ℝ) ^ 2 - (u : ℝ) ^ 2)
    (hs2 : sideOpp R 2 = (u : ℝ) * v) :
    cornerAngle (R.pts 1) (R.pts 0) (R.pts 2) = alphaT u v ∧
    cornerAngle (R.pts 2) (R.pts 1) (R.pts 0) = Real.pi - 3 * alphaT u v ∧
    cornerAngle (R.pts 0) (R.pts 2) (R.pts 1) = 2 * alphaT u v := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have huvR : (u : ℝ) < v := by exact_mod_cast huv
  have hvR : (v : ℝ) < 2 * u := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < v := by linarith
  have hb0 : (0 : ℝ) < (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by nlinarith
  have d12 : dist (R.pts 1) (R.pts 2) = (u : ℝ) ^ 2 := by rw [← hs0]; rfl
  have d20 : dist (R.pts 2) (R.pts 0) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by rw [← hs1]; rfl
  have d01 : dist (R.pts 0) (R.pts 1) = (u : ℝ) * v := by rw [← hs2]; rfl
  have hcosα := cos_alphaT huR huvR hvR
  have hα0 := alphaT_pos huR hvR hv0
  have hαh := alphaT_le_half_pi huR hv0
  have hα' : cornerAngle (R.pts 1) (R.pts 0) (R.pts 2) = alphaT u v := by
    have h1 : dist (R.pts 1) (R.pts 0) = (u : ℝ) * v := by rw [dist_comm]; exact d01
    refine cornerAngle_eq_of_cosT (a := (u : ℝ) * v) (b := (v : ℝ) ^ 2 - (u : ℝ) ^ 2)
      (d := (u : ℝ) ^ 2) h1 d20 d12 (by positivity) hb0 hα0.le (by linarith [Real.pi_pos]) ?_
    rw [hcosα]
    field_simp
    ring
  have hγ' : cornerAngle (R.pts 0) (R.pts 2) (R.pts 1) = 2 * alphaT u v := by
    refine cornerAngle_eq_of_cosT (a := (v : ℝ) ^ 2 - (u : ℝ) ^ 2) (b := (u : ℝ) ^ 2)
      (d := (u : ℝ) * v) (by rw [dist_comm]; exact d20) d12 d01
      hb0 (by positivity) (by linarith) (by linarith [Real.pi_pos]) ?_
    rw [Real.cos_two_mul, hcosα]
    field_simp
    ring
  have hsum := Erdos634.Geometry.cornerAngle_sum R
  rw [hα', hγ'] at hsum
  refine ⟨hα', ?_, hγ'⟩
  linarith

/-- **`ModelDataT` from the model sides** -/
theorem modelDataT_of_sides (D : CongruentDissection N) {u v : ℕ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u)
    (hs0 : sideOpp D.model 0 = (u : ℝ) ^ 2) (hs1 : sideOpp D.model 1 = (v : ℝ) ^ 2 - (u : ℝ) ^ 2)
    (hs2 : sideOpp D.model 2 = (u : ℝ) * v) :
    ModelDataT D ((u : ℝ) ^ 2) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((u : ℝ) * v) (alphaT u v)
      (Real.pi - 3 * alphaT u v) (2 * alphaT u v) := by
  obtain ⟨h1, h2, h3⟩ := modelAngles_of_sidesT D.model hu huv hv hs0 hs1 hs2
  exact ⟨hs0, hs1, hs2, h1, h2, h3⟩

/-! ## 2. The setup -/

structure SetupT (D : CongruentDissection N) (u v : ℕ) (α β γ L ax ay : ℝ) : Prop where
  hu : 0 < u
  huv : u < v
  hv : v < 2 * u
  hco : Nat.Coprime u v
  hirr : Irrational (α / Real.pi)
  hα : 0 < α
  hβ : β = Real.pi - 3 * α
  hγ : γ = 2 * α
  hM : ModelDataT D ((u : ℝ) ^ 2) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((u : ℝ) * v) α β γ
  hL : 0 < L
  hay : 0 < ay
  htgt : ∀ (h1 : 0 < L) (h2 : 0 < ay), D.target = Tg L ax ay h1 h2

namespace SetupT

variable {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

theorem u0 (S : SetupT D u v α β γ L ax ay) : (0 : ℝ) < u := by exact_mod_cast S.hu
theorem uv' (S : SetupT D u v α β γ L ax ay) : (u : ℝ) < v := by exact_mod_cast S.huv
theorem v0 (S : SetupT D u v α β γ L ax ay) : (0 : ℝ) < v := S.u0.trans S.uv'
theorem v2 (S : SetupT D u v α β γ L ax ay) : (v : ℝ) < 2 * u := by exact_mod_cast S.hv
theorem b_pos (S : SetupT D u v α β γ L ax ay) : (0 : ℝ) < (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
  have := S.u0; have := S.uv'; nlinarith
theorem tgt (S : SetupT D u v α β γ L ax ay) : D.target = Tg L ax ay S.hL S.hay := S.htgt S.hL S.hay

theorem mem (S : SetupT D u v α β γ L ax ay) {p : Plane} (hp : p ∈ D.target.carrier) :
    0 ≤ p 1 ∧ 0 ≤ gA ax ay p ∧ 0 ≤ gB L ax ay p := by
  rw [S.tgt] at hp; exact Tg_bounds S.hL S.hay hp

theorem pts_mem (S : SetupT D u v α β γ L ax ay) (i : Fin N) (k : Fin 3) :
    0 ≤ ((D.tile i).pts k) 1 ∧ 0 ≤ gA ax ay ((D.tile i).pts k) ∧ 0 ≤ gB L ax ay ((D.tile i).pts k) :=
  S.mem (pts_mem_target D.toDissection i k)

theorem interior_seg (S : SetupT D u v α β γ L ax ay) {P Q : Plane} (hP : P ∈ D.target.carrier)
    (hQ : Q ∈ D.target.carrier) (h1 : 0 < P 1 ∨ 0 < Q 1)
    (h2 : 0 < gA ax ay P ∨ 0 < gA ax ay Q) (h3 : 0 < gB L ax ay P ∨ 0 < gB L ax ay Q) :
    openSegment ℝ P Q ⊆ interior D.target.carrier := by
  rw [S.tgt] at hP hQ ⊢; exact openSegment_interior_Tg S.hL S.hay hP hQ h1 h2 h3

theorem gA_pos_of_left (S : SetupT D u v α β γ L ax ay) {x y t : ℝ} (ht : 0 < t)
    (h : mkPt (x - t) y ∈ D.target.carrier) : 0 < gA ax ay (mkPt x y) := by
  have h1 := (S.mem h).2.1
  rw [gA_mk] at h1 ⊢
  nlinarith [mul_pos S.hay ht]

theorem gB_pos_of_right (S : SetupT D u v α β γ L ax ay) {x y t : ℝ} (ht : 0 < t)
    (h : mkPt (x + t) y ∈ D.target.carrier) : 0 < gB L ax ay (mkPt x y) := by
  have h1 := (S.mem h).2.2
  rw [gB_mk] at h1 ⊢
  nlinarith [mul_pos S.hay ht]

theorem base_range (S : SetupT D u v α β γ L ax ay) {x : ℝ} (h : mkPt x 0 ∈ D.target.carrier) :
    0 ≤ x ∧ x ≤ L := by
  obtain ⟨-, h2, h3⟩ := S.mem h
  rw [gA_mk] at h2
  rw [gB_mk] at h3
  have hay := S.hay
  constructor
  · by_contra hneg
    push Not at hneg
    nlinarith [mul_pos hay (neg_pos.mpr hneg)]
  · by_contra hneg
    push Not at hneg
    nlinarith [mul_pos hay (sub_pos.mpr hneg)]

end SetupT

/-! ## 3. The normal form -/

/-- `T` has side lengths `a, b, c`, in some vertex order `τ` (same as `FDBBaseBetaE1.HasSides`) -/
def HasSidesT (T : Tri) (a b c : ℝ) : Prop :=
  ∃ τ : Equiv.Perm (Fin 3), dist (T.pts (τ 1)) (T.pts (τ 2)) = a ∧
    dist (T.pts (τ 2)) (T.pts (τ 0)) = b ∧ dist (T.pts (τ 0)) (T.pts (τ 1)) = c

theorem sideOpp_relabel_of_hasSidesT {M : Tri} {a b c : ℝ} (h : HasSidesT M a b c) :
    ∃ σ : Equiv.Perm (Fin 3), sideOpp (M.relabel σ) 0 = a ∧ sideOpp (M.relabel σ) 1 = b ∧
      sideOpp (M.relabel σ) 2 = c := by
  obtain ⟨τ, m0, m1, m2⟩ := h
  refine ⟨τ, ?_, ?_, ?_⟩
  · show dist ((M.relabel τ).pts 1) ((M.relabel τ).pts 2) = a
    rw [Tri.relabel_pts, Tri.relabel_pts]; exact m0
  · show dist ((M.relabel τ).pts 2) ((M.relabel τ).pts 0) = b
    rw [Tri.relabel_pts, Tri.relabel_pts]; exact m1
  · show dist ((M.relabel τ).pts 0) ((M.relabel τ).pts 1) = c
    rw [Tri.relabel_pts, Tri.relabel_pts]; exact m2

open Erdos634.SssCongruent in
theorem exists_iso_of_dist3T {T U : Tri}
    (h01 : dist (T.pts 0) (T.pts 1) = dist (U.pts 0) (U.pts 1))
    (h12 : dist (T.pts 1) (T.pts 2) = dist (U.pts 1) (U.pts 2))
    (h20 : dist (T.pts 2) (T.pts 0) = dist (U.pts 2) (U.pts 0)) :
    ∃ g : Plane ≃ᵢ Plane, ∀ k, g (T.pts k) = U.pts k := by
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  have hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j) := by
    intro i j
    rcases htri i with rfl | rfl | rfl <;> rcases htri j with rfl | rfl | rfl <;>
      simp_all [dist_comm]
  refine ⟨sssIso hd, ?_⟩
  intro k
  rcases htri k with rfl | rfl | rfl
  · rw [sssIso_apply]
    have h0 : T.pts 0 + -T.pts 0 = (0 : Plane) := by abel
    rw [h0, map_zero, zero_add]
  · rw [sssIso_apply]
    have h1 : T.pts 1 + -T.pts 0 = ev T 0 := by simp [ev]; abel
    rw [h1, evMap_basis]
    show U.pts 1 - U.pts 0 + U.pts 0 = U.pts 1
    abel
  · rw [sssIso_apply]
    have h2 : T.pts 2 + -T.pts 0 = ev T 1 := by simp [ev]; abel
    rw [h2, evMap_basis]
    show U.pts 2 - U.pts 0 + U.pts 0 = U.pts 2
    abel

/-- **THE NORMAL FORM for the `γ = 2α` tile, vertices named.**  A congruent dissection `D₀` whose target has
`dist (τ 1, τ 2) = d₁`, `dist (τ 2, τ 0) = d₂`, `dist (τ 0, τ 1) = L` (the sides of `Q = (0,0)`, `B = (L,0)`, `A = (ax,ay)`)
and whose model has the sides `u², v² − u², u v` gives, after an isometry `g`, a `SetupT` on that triangle with
`g (τ 0) = Q`, `g (τ 1) = B`. -/
theorem setup_of_sidesT_pinned (u v : ℕ) (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hco : Nat.Coprime u v)
    (hirr : Irrational (alphaT u v / Real.pi))
    {L ax ay d₁ d₂ : ℝ} (hL : 0 < L) (hay : 0 < ay)
    (hd₁ : dist (mkPt L 0) (mkPt ax ay) = d₁) (hd₂ : dist (mkPt ax ay) (mkPt 0 0) = d₂)
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = d₁)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = d₂)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = L)
    (hMod : HasSidesT D₀.model ((u : ℝ) ^ 2) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((u : ℝ) * v)) :
    ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane),
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      g (D₀.target.pts (τ 0)) = mkPt 0 0 ∧ g (D₀.target.pts (τ 1)) = mkPt L 0 ∧
      SetupT D u v (alphaT u v) (Real.pi - 3 * alphaT u v) (2 * alphaT u v) L ax ay := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (v : ℝ) < 2 * u := by exact_mod_cast hv
  have huvR : (u : ℝ) < v := by exact_mod_cast huv
  have h12 : dist ((Tg L ax ay hL hay).pts 1) ((Tg L ax ay hL hay).pts 2) = d₁ := hd₁
  have h20 : dist ((Tg L ax ay hL hay).pts 2) ((Tg L ax ay hL hay).pts 0) = d₂ := hd₂
  have h01 : dist ((Tg L ax ay hL hay).pts 0) ((Tg L ax ay hL hay).pts 1) = L := by
    show dist (mkPt 0 0) (mkPt L 0) = L
    have := dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this
  obtain ⟨g, hg0⟩ := exists_iso_of_dist3T (T := D₀.target.relabel τ) (U := Tg L ax ay hL hay)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h3.trans h01.symm)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h1.trans h12.symm)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h2.trans h20.symm)
  have hg : ∀ k, g (D₀.target.pts k) = (Tg L ax ay hL hay).pts (τ.symm k) := by
    intro k
    have := hg0 (τ.symm k)
    rwa [Tri.relabel_pts, Equiv.apply_symm_apply] at this
  obtain ⟨σm, m0, m1, m2⟩ := sideOpp_relabel_of_hasSidesT hMod
  have hmod : D₀.model.Congruent (D₀.model.relabel σm) := Tri.congruent_relabel D₀.model σm
  have hMD := modelDataT_of_sides (Erdos634.E1NormalForm.normalFormC D₀ g τ.symm hmod) hu huv hv m0 m1 m2
  exact ⟨Erdos634.E1NormalForm.normalFormC D₀ g τ.symm hmod, g, fun _ _ => rfl, hg0 0, hg0 1,
    ⟨hu, huv, hv, hco, hirr, alphaT_pos hu0 hvR (by linarith), rfl, rfl, hMD, hL, hay,
      fun _ _ => Erdos634.E1NormalForm.normalFormC_target D₀ hg hmod⟩⟩

end Erdos634.Draft.ThmDRun

#print axioms Erdos634.Draft.ThmDRun.setup_of_sidesT_pinned
#print axioms Erdos634.Draft.ThmDRun.modelAngles_of_sidesT
