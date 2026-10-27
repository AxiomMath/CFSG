
module

public import Certificates.Kernel.Multipliers.TwoCover
public import Certificates.Kernel.Multipliers.U43Cone
public import Certificates.Kernel.Multipliers.ZProd
public import Certificates.Kernel.Multipliers.Ent
public import CFSG.Certificates.Kernel.Bounds.J2CovAlt.Checks.C
public import CFSG.Certificates.Kernel.Bounds.J2CovAlt.Checks.M
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J2CoverRowBase

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelJ2Cov

open CFSG.KC CFSG.KC.LceS CFSG.Certificates.LCE CFSG.Certificates.LabZ CFSG.LieType.Multipliers
  CFSG.CosetTable CertificateChecks.KernelMult CertificateChecks.KernelTwoCover
  CFSG.Certificates.CosetEnumeration CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J2Cover

abbrev cov : List (List (Fin 2 × Bool)) := coverWords j2Rels j2CommWord

noncomputable abbrev z (k : ℕ) : PG 2 cov := zk j2Rels j2CommWord k

noncomputable abbrev gen : ℕ → PG 2 cov := CFSG.KC.MiscCoset.pgGen cov

noncomputable def gg (d : ℕ) : PG 2 cov :=
  if d < 5 then bval gen (wWord (CFSG.KD.J2C.selRT d)) (wLen (CFSG.KD.J2C.selRT d))
  else if d = 5 then bval gen (wWord (CFSG.KD.J2C.selST 0)) (wLen (CFSG.KD.J2C.selST 0)) else 1

theorem rel_ent : ∀ k < 3, CFSG.KD.J2C.selRT k = ent (j2Rels.getD k []) := by
  decide +kernel

theorem cover_ent0 : CFSG.KD.J2C.selRT 3 = ent ((0, false) :: j2CommWord 0) := by
  decide +kernel

theorem cover_ent1 : CFSG.KD.J2C.selRT 4 = ent ((1, false) :: j2CommWord 1) := by
  decide +kernel

theorem gg_rel {k : ℕ} (hk : k < 3) : gg k = z k := by
  have hl : ∀ k < 3, (j2Rels.getD k []).length < 1024 := by decide +kernel
  simp only [gg, show k < 5 by omega, ↓reduceIte]
  rw [bval_ent (by norm_num) cov _ (rel_ent k hk) (hl k hk)]
  rfl

theorem gg_cover {i : ℕ} (hi : i < 2) : gg (3 + i) = 1 := by
  have h5 : 3 + i < 5 := by omega
  simp only [gg, h5, ↓reduceIte]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [bval_ent (by norm_num) cov _ cover_ent0 (by decide +kernel)]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (cover_mem j2Rels j2CommWord 0))
  · rw [bval_ent (by norm_num) cov _ cover_ent1 (by decide +kernel)]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (cover_mem j2Rels j2CommWord 1))

theorem gg_central {r : ℕ} (hr : r < 5) : gg r ∈ Subgroup.center (PG 2 cov) := by
  rcases Nat.lt_or_ge r 3 with h | h
  · exact gg_rel h ▸ zk_central j2Rels j2CommWord (by simpa [j2Rels] using h)
  · have e : r = 3 + (r - 3) := by omega
    rw [e, gg_cover (by omega)]
    exact Subgroup.one_mem _

theorem gg_center_or (d : ℕ) : gg d ∈ Subgroup.center (PG 2 cov) ∨ gg d = gg 5 := by
  rcases Nat.lt_or_ge d 5 with h | h
  · exact Or.inl (gg_central h)
  · rcases Nat.lt_or_ge d 6 with h' | h'
    · exact Or.inr (by rw [show d = 5 by omega])
    · left
      simp only [gg, show ¬ (d < 5) from by omega, show ¬ (d = 5) from by omega, ↓reduceIte]
      exact Subgroup.one_mem _

theorem gg_comm (i j : ℕ) : Commute (gg i) (gg j) := by
  rcases gg_center_or i with hi | hi
  · exact (Subgroup.mem_center_iff.mp hi (gg j)).symm
  rcases gg_center_or j with hj | hj
  · exact Subgroup.mem_center_iff.mp hj (gg i)
  rw [hi, hj]

theorem hRT : ∀ r < 5, wWord (CFSG.KD.J2C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.J2C.selRT r)) ∧
    bval gen (wWord (CFSG.KD.J2C.selRT r)) (wLen (CFSG.KD.J2C.selRT r)) = gg r ∧
      ∀ c, Commute (letV gen c) (gg r) := by
  have hcl : ∀ r < 5, wWord (CFSG.KD.J2C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.J2C.selRT r)) := by
    decide +kernel
  intro r hr
  refine ⟨hcl r hr, ?_, fun c => Subgroup.mem_center_iff.mp (gg_central hr) _⟩
  simp only [gg, hr, ↓reduceIte]

theorem hST : ∀ j < 1, bval gen (wWord (CFSG.KD.J2C.selST j)) (wLen (CFSG.KD.J2C.selST j)) =
    gg (5 + j) := by
  intro j hj
  have : j = 0 := by omega
  subst this
  simp only [gg, show ¬ (5 + 0 < 5) from by omega, show 5 + 0 = 5 from rfl, ↓reduceIte]

theorem cyc_of {c wid R V : ℕ} (hc : c < 2 ^ 20) (hwid : wid < 1024)
    (h : LabZ.cycZ CFSG.KD.J2C.blk CFSG.KD.J2C.selWT CFSG.KD.J2C.LB CFSG.KD.J2C.BIAS 353 c wid R V
      = true) :
    zprod gg 6 (decZ V) = zprod gg 6 (decZ (CFSG.KD.J2C.TG wid)) :=
  cyc_sound gen gg gg_comm
    (KernelU43.coneOk_intro CFSG.KD.J2C.sH0 CFSG.KD.J2C.sH1 (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) CFSG.KD.J2C.sH6 CFSG.KD.J2C.sI CFSG.KD.J2C.sH7 CFSG.KD.J2C.sH8
      CFSG.KD.J2C.sW CFSG.KD.J2C.sL)
    hRT hST rfl hc hwid h

theorem rel_of {c wid R V : ℕ} (ρ : List ℤ) (hc : c < 2 ^ 20) (hwid : wid < 1024)
    (h : LabZ.cycZ CFSG.KD.J2C.blk CFSG.KD.J2C.selWT CFSG.KD.J2C.LB CFSG.KD.J2C.BIAS 353 c wid R V
      = true)
    (hρ : ∀ d < 6, decZ V d - decZ (CFSG.KD.J2C.TG wid) d = ρ.getD d 0) :
    zprod gg 6 (fun d => ρ.getD d 0) = 1 := by
  rw [← zprod_congr gg hρ]
  change zprod gg 6 (decZ V - decZ (CFSG.KD.J2C.TG wid)) = 1
  rw [zprod_sub gg_comm, cyc_of hc hwid h, mul_inv_cancel]

@[expose] def rhos : List (List ℤ) :=
  [[9, 7, -2, -7, 0, 14], [-3, 1, 0, -1, 0, 0], [1, 0, 0, 1, -1, 0], [15, -5, 0, -9, 0, -14]]

theorem rhos_one : ∀ ρ ∈ rhos, zprod gg 6 (fun d => ρ.getD d 0) = 1 := by
  have h := CFSG.KD.J2C.cyc_all
  intro ρ hρ
  simp only [rhos, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl
  · exact rel_of _ (by decide +kernel) (by decide +kernel) (h 0 (by decide)) (by decide +kernel)
  · exact rel_of _ (by decide +kernel) (by decide +kernel) (h 1 (by decide)) (by decide +kernel)
  · exact rel_of _ (by decide +kernel) (by decide +kernel) (h 2 (by decide)) (by decide +kernel)
  · exact rel_of _ (by decide +kernel) (by decide +kernel) (h 3 (by decide)) (by decide +kernel)

theorem pow_off {t : List ℤ} {k : ℕ} (ht : ∀ d < 6, d ≠ k → d ≠ 3 → d ≠ 4 → t.getD d 0 = 0) :
    ∀ d < 6, d ≠ k → gg d ^ t.getD d 0 = 1 := by
  intro d hd hk
  by_cases h3 : d = 3
  · subst h3
    rw [gg_cover (i := 0) (by omega), one_zpow]
  by_cases h4 : d = 4
  · subst h4
    rw [gg_cover (i := 1) (by omega), one_zpow]
  rw [ht d hd hk h3 h4, zpow_zero]

theorem z0_eq : z 0 = 1 := by
  have t := zprod_target gg_comm 6 [0, 0, 1, 0] rhos rhos_one [1, 0, 0, 1, -1, 0]
    (by decide +kernel)
  rw [zprod_eq_single (k := 0) (by omega) (by rfl) (pow_off (by decide))] at t
  rw [← gg_rel (by omega), t]

theorem z1_eq : z 1 = 1 := by
  have t := zprod_target gg_comm 6 [0, 1, 3, 0] rhos rhos_one [0, 1, 0, 2, -3, 0]
    (by decide +kernel)
  rw [zprod_eq_single (k := 1) (by omega) (by rfl) (pow_off (by decide))] at t
  rw [← gg_rel (by omega), t]

theorem z2_sq : z 2 ^ 2 = 1 := by
  have t := zprod_target gg_comm 6 [-1, 2, 30, -1] rhos rhos_one [0, 0, 2, 44, -30, 0]
    (by decide +kernel)
  rw [zprod_eq_pow (k := 2) (by omega) (pow_off (by decide))] at t
  rw [← gg_rel (by omega)]
  exact_mod_cast t

theorem card_rels : Finite (PG 2 j2Rels) ∧ Nat.card (PG 2 j2Rels) ≤ 604800 := by
  obtain ⟨hfin, hcard⟩ := CFSG.Sporadic.Bridge.J2.finite_card_le
  have e1 := mulEquivOfIsPresentation isPresentation_gJ2
  have e2 := Equiv.ofBijective _ toNative_bijective
  have : Finite (PG 2 j2Rels) := Finite.of_equiv _ (e2.trans e1.toEquiv.symm)
  exact ⟨this, by rw [Nat.card_congr (e2.trans e1.toEquiv.symm).symm]; exact hcard⟩

theorem card_le : Finite (PG 2 cov) ∧ Nat.card (PG 2 cov) ≤ 1209600 := by
  obtain ⟨hfin, hcard⟩ := card_rels
  obtain ⟨f, c⟩ := card_le_two_mul j2Rels j2CommWord
    (zk_central j2Rels j2CommWord (k := 2) (by decide)) z2_sq (fun k hk => by
      have hk' : k < 3 := by simpa [j2Rels] using hk
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · rw [show zk j2Rels j2CommWord 0 = z 0 from rfl, z0_eq]
        exact Subgroup.one_mem _
      · rw [show zk j2Rels j2CommWord 1 = z 1 from rfl, z1_eq]
        exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _)
  exact ⟨f, c.trans (by omega)⟩

theorem codes_rels : codes j2Rels = CFSG.KD.J2M.Rc := by
  decide +kernel

theorem codes_cover :
    codes ((List.finRange 2).map fun i => (i, false) :: j2CommWord i) = CFSG.KD.J2M.Wc := by
  decide +kernel

theorem two_dvd : 2 ∣ orderOf (z 2) :=
  two_dvd_orderOf_of_mono j2Rels j2CommWord codes_rels codes_cover CFSG.KD.J2M.sQ
    CFSG.KD.J2M.pt_all (k := 2) (by decide) rfl

theorem bounds : Finite (PG 2 j2Cover) ∧ Nat.card (PG 2 j2Cover) ≤ 1209600 ∧
    2 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ j2Cover.map FreeGroup.mk}
      (FreeGroup.mk j2R3)) :=
  ⟨card_le.1, card_le.2, two_dvd⟩

end CertificateChecks.KernelJ2Cov

end
