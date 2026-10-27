module

public import Certificates.Kernel.Multipliers.U43Cone
public import Certificates.Kernel.Multipliers.ZProd
public import Certificates.Kernel.Co2.Words
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.LieType.Multipliers.U43Kernel

set_option exponentiation.threshold 512

public section

namespace CertificateChecks.KernelU43

open CFSG.KC CFSG.KC.LceS CFSG.Certificates.LCE CFSG.Certificates.LabZ CFSG.LieType.Multipliers
  CFSG.LieType.Multipliers.U43 CFSG.CosetTable CertificateChecks.KernelMult

noncomputable abbrev gen : ℕ → PG 2 coverWs := CFSG.KC.MiscCoset.pgGen coverWs

theorem bval_rel {e : ℕ} (w : List (Fin 2 × Bool)) (h : e = CFSG.KC.Co2B.ent (CFSG.KC.MiscCoset.encW w))
    (hlen : w.length < 1024) :
    bval gen (wWord e) (wLen e) = PresentedGroup.mk _ (FreeGroup.mk w) := by
  rw [h, KernelCo2.bval_ent gen _ (fun l hl => ?_) (by simpa [CFSG.KC.MiscCoset.encW] using hlen)]
  · exact CFSG.KC.MiscCoset.sword_pgGen coverWs w
  · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
    have := x.1.isLt
    omega

theorem mem_comm (i : Fin 2) {k : ℕ} (hk : k < 7) :
    commWord [(i, true)] (rels.getD k []) ∈ coverWs := by
  revert i k
  decide

theorem mem_cover (i : Fin 2) : (i, false) :: commWords (coverPairs i) ∈ coverWs := by
  revert i
  decide

theorem zk_central {k : ℕ} (hk : k < 7) : zk k ∈ Subgroup.center (PG 2 coverWs) := by
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← PresentedGroup.closure_range_of,
    Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro _ ⟨i, rfl⟩
  have h : PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk}
      (FreeGroup.mk (commWord [(i, true)] (rels.getD k []))) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map_of_mem (mem_comm i hk))
  rw [mk_commWord, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem cover_one (i : Fin 2) :
    PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk}
      (FreeGroup.mk ((i, false) :: commWords (coverPairs i))) = 1 :=
  PresentedGroup.one_of_mem (List.mem_map_of_mem (mem_cover i))

noncomputable def gg (d : ℕ) : PG 2 coverWs :=
  if d < 9 then bval gen (wWord (CFSG.KC.U43Alt.rel d)) (wLen (CFSG.KC.U43Alt.rel d))
  else if d = 9 then bval gen (wWord (CFSG.KC.U43Alt.sub 0)) (wLen (CFSG.KC.U43Alt.sub 0)) else 1

theorem gg_rel {k : ℕ} (hk : k < 7) : gg k = zk k := by
  have he : ∀ k < 7, CFSG.KC.U43Alt.rel k = CFSG.KC.Co2B.ent (CFSG.KC.MiscCoset.encW (rels.getD k [])) := by
    decide
  have hl : ∀ k < 7, (rels.getD k []).length < 1024 := by decide
  have h9 : k < 9 := by omega
  simp only [gg, h9, ↓reduceIte]
  rw [bval_rel _ (he k hk) (hl k hk)]
  rfl

theorem gg_cover (i : Fin 2) : gg (7 + i.val) = 1 := by
  have he : ∀ i : Fin 2, CFSG.KC.U43Alt.rel (7 + i.val) =
      CFSG.KC.Co2B.ent (CFSG.KC.MiscCoset.encW ((i, false) :: commWords (coverPairs i))) := by
    decide
  have hl : ∀ i : Fin 2, ((i, false) :: commWords (coverPairs i)).length < 1024 := by decide
  have h9 : 7 + i.val < 9 := by omega
  simp only [gg, h9, ↓reduceIte]
  rw [bval_rel _ (he i) (hl i)]
  exact cover_one i

theorem gg_b : gg 9 = PresentedGroup.of 1 := by
  have he : CFSG.KC.U43Alt.sub 0 = CFSG.KC.Co2B.ent (CFSG.KC.MiscCoset.encW [((1 : Fin 2), true)]) := by
    decide
  simp only [gg, show ¬ (9 < 9) from by omega, ↓reduceIte]
  rw [bval_rel _ he (by decide)]
  rfl

theorem gg_big {d : ℕ} (hd : 10 ≤ d) : gg d = 1 := by
  simp only [gg, show ¬ (d < 9) from by omega, show ¬ (d = 9) from by omega, ↓reduceIte]

theorem gg_central {r : ℕ} (hr : r < 9) : gg r ∈ Subgroup.center (PG 2 coverWs) := by
  rcases Nat.lt_or_ge r 7 with h | h
  · exact gg_rel h ▸ zk_central h
  · have e : r = 7 + (⟨r - 7, by omega⟩ : Fin 2).val := by simp only; omega
    rw [e, gg_cover]
    exact Subgroup.one_mem _

theorem gg_center_or (d : ℕ) : gg d ∈ Subgroup.center (PG 2 coverWs) ∨ gg d = PresentedGroup.of 1 := by
  rcases Nat.lt_or_ge d 9 with h | h
  · exact Or.inl (gg_central h)
  · rcases Nat.lt_or_ge d 10 with h' | h'
    · have : d = 9 := by omega
      rw [this, gg_b]
      exact Or.inr rfl
    · rw [gg_big h']
      exact Or.inl (Subgroup.one_mem _)

theorem gg_comm (i j : ℕ) : Commute (gg i) (gg j) := by
  rcases gg_center_or i with hi | hi
  · exact (Subgroup.mem_center_iff.mp hi (gg j)).symm
  rcases gg_center_or j with hj | hj
  · exact Subgroup.mem_center_iff.mp hj (gg i)
  rw [hi, hj]

theorem gg_letters {r : ℕ} (hr : r < 9) (c : ℕ) : Commute (letV gen c) (gg r) :=
  Subgroup.mem_center_iff.mp (gg_central hr) _

theorem hRT : ∀ r < 9, wWord (CFSG.KD.U43C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.U43C.selRT r)) ∧
    bval gen (wWord (CFSG.KD.U43C.selRT r)) (wLen (CFSG.KD.U43C.selRT r)) = gg r ∧
      ∀ c, Commute (letV gen c) (gg r) := by
  have hcl : ∀ r < 9, wWord (CFSG.KD.U43C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.U43C.selRT r)) := by
    decide
  intro r hr
  refine ⟨hcl r hr, ?_, gg_letters hr⟩
  simp only [gg, hr, ↓reduceIte]
  rfl

theorem hST : ∀ j < 1, bval gen (wWord (CFSG.KD.U43C.selST j)) (wLen (CFSG.KD.U43C.selST j)) =
    gg (9 + j) := by
  intro j hj
  have : j = 0 := by omega
  subst this
  simp only [gg, show ¬ (9 + 0 < 9) from by omega, show 9 + 0 = 9 from rfl, ↓reduceIte]
  rfl

theorem cyc_of {c wid R V : ℕ} (hc : c < 2 ^ 20) (hwid : wid < 512)
    (h : LabZ.cycZ CFSG.KD.U43C.blk CFSG.KD.U43C.selWT CFSG.KD.U43C.LB CFSG.KD.U43C.BIAS 0x6cff c wid R V
      = true) :
    zprod gg 10 (decZ V) = zprod gg 10 (decZ (CFSG.KD.U43C.TG wid)) :=
  cyc_sound gen gg gg_comm
    (coneOk_intro CFSG.KD.U43C.sH0 CFSG.KD.U43C.sH1 (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      CFSG.KD.U43C.sH6 Cids CFSG.KD.U43C.sH7 CFSG.KD.U43C.sH8 Cfacts Clab)
    hRT hST rfl hc hwid h

theorem rel_of {c wid R V : ℕ} (ρ : List ℤ) (hc : c < 2 ^ 20) (hwid : wid < 512)
    (h : LabZ.cycZ CFSG.KD.U43C.blk CFSG.KD.U43C.selWT CFSG.KD.U43C.LB CFSG.KD.U43C.BIAS 0x6cff c wid R V
      = true)
    (hρ : ∀ d < 10, decZ V d - decZ (CFSG.KD.U43C.TG wid) d = ρ.getD d 0) :
    zprod gg 10 (fun d => ρ.getD d 0) = 1 := by
  rw [← zprod_congr gg hρ]
  change zprod gg 10 (decZ V - decZ (CFSG.KD.U43C.TG wid)) = 1
  rw [zprod_sub gg_comm, cyc_of hc hwid h, mul_inv_cancel]

theorem r0 : zprod gg 10 (fun d => ([0, -1, 0, 0, 0, 0, 0, 0, 0, 6] : List ℤ).getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U43C.sY0 (by decide)
theorem r1 : zprod gg 10 (fun d => ([6, 0, 0, -2, 0, 0, 0, 0, 0, 0] : List ℤ).getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U43C.sY1 (by decide)
theorem r2 : zprod gg 10 (fun d => ([-9, -1, 0, 3, 0, 0, 0, 0, 0, 6] : List ℤ).getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U43C.sY2 (by decide)
theorem r3 : zprod gg 10 (fun d => ([5, -1, 0, 0, -2, 0, 0, 0, 0, 0] : List ℤ).getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U43C.sY3 (by decide)
theorem r4 : zprod gg 10 (fun d => ([18, -2, 0, 0, 0, -3, 0, 0, 0, 0] : List ℤ).getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U43C.sY4 (by decide)
theorem r5 : zprod gg 10 (fun d => ([-265, 24, 6, 17, -2, 24, 6, 0, 0, 18] : List ℤ).getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U43C.sY5 (by decide)
theorem r6 : zprod gg 10 (fun d => ([-210, 23, 6, 11, 1, 21, 3, -1, 0, 6] : List ℤ).getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U43C.sY6 (by decide)
theorem r7 : zprod gg 10 (fun d => ([-345, 98, 25, -156, 49, 42, 39, 0, -1, 96] : List ℤ).getD d 0) =
    1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U43C.sY7 (by decide)
theorem r8 : zprod gg 10 (fun d => ([329, 3, 0, -108, 23, -24, 9, -1, 0, 0] : List ℤ).getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U43C.sY8 (by decide)

@[expose] def rels9 (c : List ℤ) : List ((ℕ → ℤ) × ℤ) :=
  [(fun d => ([0, -1, 0, 0, 0, 0, 0, 0, 0, 6] : List ℤ).getD d 0, c.getD 0 0),
    (fun d => ([6, 0, 0, -2, 0, 0, 0, 0, 0, 0] : List ℤ).getD d 0, c.getD 1 0),
    (fun d => ([-9, -1, 0, 3, 0, 0, 0, 0, 0, 6] : List ℤ).getD d 0, c.getD 2 0),
    (fun d => ([5, -1, 0, 0, -2, 0, 0, 0, 0, 0] : List ℤ).getD d 0, c.getD 3 0),
    (fun d => ([18, -2, 0, 0, 0, -3, 0, 0, 0, 0] : List ℤ).getD d 0, c.getD 4 0),
    (fun d => ([-265, 24, 6, 17, -2, 24, 6, 0, 0, 18] : List ℤ).getD d 0, c.getD 5 0),
    (fun d => ([-210, 23, 6, 11, 1, 21, 3, -1, 0, 6] : List ℤ).getD d 0, c.getD 6 0),
    (fun d => ([-345, 98, 25, -156, 49, 42, 39, 0, -1, 96] : List ℤ).getD d 0, c.getD 7 0),
    (fun d => ([329, 3, 0, -108, 23, -24, 9, -1, 0, 0] : List ℤ).getD d 0, c.getD 8 0)]

theorem rels9_one (c : List ℤ) : ∀ p ∈ rels9 c, zprod gg 10 p.1 = 1 := by
  intro p hp
  simp only [rels9, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [r0, r1, r2, r3, r4, r5, r6, r7, r8]

theorem target (c t : List ℤ)
    (ht : ∀ d < 10, ((rels9 c).map fun p => p.2 • p.1).sum d = t.getD d 0) :
    zprod gg 10 (fun d => t.getD d 0) = 1 := by
  rw [← zprod_congr gg ht]
  exact zprod_combo gg_comm 10 (rels9 c) (rels9_one c)

theorem zprod_ten (g : ℕ → PG 2 coverWs) (v : ℕ → ℤ) :
    zprod g 10 v = g 0 ^ v 0 * g 1 ^ v 1 * g 2 ^ v 2 * g 3 ^ v 3 * g 4 ^ v 4 * g 5 ^ v 5 *
      g 6 ^ v 6 * g 7 ^ v 7 * g 8 ^ v 8 * g 9 ^ v 9 := by
  simp only [zprod_succ, show zprod g 0 v = 1 from rfl, one_mul]

theorem gg7 : gg 7 = 1 := gg_cover 0
theorem gg8 : gg 8 = 1 := gg_cover 1

theorem kernel_relations : zk 5 ^ 3 = 1 ∧ zk 6 ^ 12 = 1 ∧ zk 0 = zk 6 ^ 6 ∧ zk 1 = 1 ∧ zk 2 = 1 ∧
    zk 3 = zk 6 ^ 6 ∧ zk 4 = zk 6 ^ 3 := by
  have ta := target [-22, -179, -179, 75, -36, -77, -48, 30, -62] [1, 0, 0, 0, 0, 0, 6, 110, -30, 0]
    (by decide)
  have tb := target [654, -647, -647, -102, 67, 32, -7, -6, 7] [0, 1, 0, 0, 0, 0, 0, 0, 6, 0]
    (by decide)
  have tc := target [-542, 523, 523, 90, -57, -32, 3, 7, -10] [0, 0, 1, 0, 0, 0, 0, 7, -7, 0]
    (by decide)
  have td := target [97, -304, -304, 59, -25, -74, -51, 30, -63] [0, 0, 0, 1, 0, 0, 6, 114, -30, 0]
    (by decide)
  have te := target [-300, -8, -8, 155, -82, -130, -70, 48, -97] [0, 0, 0, 0, 1, 0, 9, 167, -48, 0]
    (by decide)
  have tf := target [-228, 160, 160, 60, -36, -37, -13, 12, -23] [0, 0, 0, 0, 0, 3, 0, 36, -12, 0]
    (by decide)
  have tg := target [-164, -232, -232, 166, -83, -157, -93, 60, -123] [0, 0, 0, 0, 0, 0, 12, 216, -60, 0]
    (by decide)
  simp only [zprod_ten, gg7, gg8, gg_rel (show 0 < 7 by omega), gg_rel (show 1 < 7 by omega),
    gg_rel (show 2 < 7 by omega), gg_rel (show 3 < 7 by omega), gg_rel (show 4 < 7 by omega),
    gg_rel (show 5 < 7 by omega), gg_rel (show 6 < 7 by omega), one_zpow, mul_one,
    List.getD_cons_zero, List.getD_cons_succ, zpow_zero, one_mul, zpow_one] at ta tb tc td te tf tg
  have h12 : zk 6 ^ 12 = 1 := by exact_mod_cast tg
  have inv6 : (zk 6 ^ 6)⁻¹ = zk 6 ^ 6 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add]
    exact h12
  have inv9 : (zk 6 ^ 9)⁻¹ = zk 6 ^ 3 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add]
    exact h12
  refine ⟨by exact_mod_cast tf, h12, ?_, tb, tc, ?_, ?_⟩
  · rw [← inv6]
    exact eq_inv_of_mul_eq_one_left (by exact_mod_cast ta)
  · rw [← inv6]
    exact eq_inv_of_mul_eq_one_left (by exact_mod_cast td)
  · rw [← inv9]
    exact eq_inv_of_mul_eq_one_left (by exact_mod_cast te)

end CertificateChecks.KernelU43

end
