
module

public import Certificates.Kernel.SporSch.HN.PtRK
public import Certificates.Kernel.SporSch.HN.Pt2103K
public import Certificates.Kernel.SporSch.HN.FixK.P2103
public import Certificates.Kernel.SporSch.HN.FixK.Spec
public import Certificates.Kernel.SporSch.HN.ArrStrong
public import Certificates.Kernel.SporSch.HN.Intr2098
public import Certificates.Kernel.SporSch.HN.OrbCert
public import CFSG.Certificates.Kernel.SporSch.HNXPtSound
public import CFSG.Certificates.Kernel.HNLocalSound
public import CFSG.Sporadic.HNSchreier.PointwiseCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNPt2103

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS CFSG.KS.SporSch CFSG.KS.HNArr CFSG.KS.Ord
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.Sporadic.He.Native CFSG.Sporadic.He CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.HNArrS CertificateChecks.KernelSporSch.HNPtR Matrix

local notation "OM" => ordMat 5 133 13 1729

@[expose] noncomputable def genJ (c : ℕ) : JH :=
  if c < 17 then sL c else if c < 34 then (sL (c - 17))⁻¹ else if c = 34 then aJ else bJ

theorem sIdx_eq (c : ℕ) : sIdx c = if c < 34 then 13 + c else c - 34 := by
  change Bool.rec (motive := fun _ => ℕ) (c - 34) (13 + c) (Nat.blt c 34) = _
  cases h : Nat.blt c 34
  · rw [if_neg (fun hc => absurd (Nat.blt_eq.mpr hc) (by rw [h]; decide))]
  · rw [if_pos (Nat.blt_eq.mp h)]

theorem om_rows {W : ℕ} {Y : ℕ → ℕ} (h : lanesEq W Y = true) : OM W = toMat 5 133 (rows5 Y) := by
  ext i j
  rw [toMat, Matrix.of_apply, rows5_get Y i.isLt j.isLt, ← HNXP.lanesEq_sound h i i.isLt j j.isLt]
  rfl

theorem R_canon {c : ℕ} (hc : c < 36) : Canon 5 133 13 (CFSG.KD.HNPt.R c) :=
  HNXP.canon_of_validHN (allN_spec valid_R c hc)

theorem R_mat {c : ℕ} (hc : c < 36) :
    OM (CFSG.KD.HNPt.R c) = matJ (genJ c) := by
  rw [om_rows (allN_spec bridge_R c hc), sIdx_eq, genJ]
  rcases Nat.lt_or_ge c 17 with h1 | h1
  · rw [if_pos (by omega), if_pos h1, (mat_sL c h1).1]
    rfl
  rcases Nat.lt_or_ge c 34 with h2 | h2
  · rw [if_pos h2, if_neg (by omega), if_pos h2, (mat_sL (c - 17) (by omega)).2,
      show 13 + c = 30 + (c - 17) by omega]
    rfl
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rcases (by omega : c = 34 ∨ c = 35) with rfl | rfl
  · rw [if_pos rfl, mat_aJ, ← toMat_rowsA, HNStrong.rowsA_eq]
  · rw [if_neg (by omega), mat_bJ, ← toMat_rowsB, HNStrong.rowsB_eq]

theorem mat_word {cs : List ℕ} (hcs : ∀ c ∈ cs, c < 36) :
    Canon 5 133 13 (wordC CFSG.KD.HNPt.R cs) ∧
      OM (wordC CFSG.KD.HNPt.R cs) = matJ (cs.map genJ).prod := by
  obtain ⟨h1, h2⟩ := HNXP.wordC_sound cs fun c hc => R_canon (hcs c hc)
  refine ⟨h1, h2.trans ?_⟩
  clear h1 h2
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, matJ_mul,
      R_mat (hcs c List.mem_cons_self), ih fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')]

@[expose] def scode (l : ℤ) : ℕ := if 0 < l then l.toNat - 1 else 16 + (-l).toNat

theorem prod_scode : ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 17) →
    ((w.map scode).map genJ).prod = wJ sL w
  | [], _ => rfl
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    rw [List.map_cons, List.map_cons, List.prod_cons, prod_scode w fun z hz =>
      hw z (List.mem_cons_of_mem l hz), wJ]
    congr 1
    unfold scode genJ lJ
    by_cases hp : 0 < l
    · rw [if_pos hp, if_pos hp, if_pos (by omega)]
    · rw [if_neg hp, if_neg hp, if_neg (by omega), if_pos (by omega),
        show 16 + (-l).toNat - 17 = (-l).toNat - 1 by omega]

theorem prod_seed : ∀ w : List ℕ, (∀ l ∈ w, l = 1 ∨ l = 2) →
    ((w.map (33 + ·)).map genJ).prod = seedJ w
  | [], _ => rfl
  | l :: w, hw => by
    rw [List.map_cons, List.map_cons, List.prod_cons, prod_seed w fun z hz =>
      hw z (List.mem_cons_of_mem l hz), seedJ]
    congr 1
    unfold genJ
    rcases hw l List.mem_cons_self with rfl | rfl
    · rw [if_neg (by omega), if_neg (by omega), if_pos rfl, if_pos rfl]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

noncomputable abbrev K1J : JH := wJ sL PointwiseData.k1
noncomputable abbrev K2J : JH := wJ sL PointwiseData.k2
noncomputable abbrev HWJ : JH := wJ sL PointwiseData.hw
noncomputable abbrev C1J : JH := wJ sL PointwiseData.c1
noncomputable abbrev S0J : JH := seedJ PointwiseData.g0 * HWJ

theorem letters_ok : (∀ l ∈ PointwiseData.k1, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ l ∈ PointwiseData.k2, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ l ∈ PointwiseData.hw, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ l ∈ PointwiseData.c1, l ≠ 0 ∧ l.natAbs ≤ 17) ∧ (∀ l ∈ PointwiseData.g0, l = 1 ∨ l = 2) := by
  decide +kernel

theorem codes_ok : CFSG.KD.HNPt2103.k1c = PointwiseData.k1.map scode ∧
    CFSG.KD.HNPt2103.k2c = PointwiseData.k2.map scode ∧
    CFSG.KD.HNPt2103.c1c = PointwiseData.c1.map scode ∧
    CFSG.KD.HNPt2103.s0c = PointwiseData.g0.map (33 + ·) ++ PointwiseData.hw.map scode := by
  decide +kernel

theorem codes_lt : (∀ c ∈ CFSG.KD.HNPt2103.k1c, c < 36) ∧ (∀ c ∈ CFSG.KD.HNPt2103.k2c, c < 36) ∧
    (∀ c ∈ CFSG.KD.HNPt2103.c1c, c < 36) ∧ (∀ c ∈ CFSG.KD.HNPt2103.s0c, c < 36) := by
  decide +kernel

theorem K1_mat :
    Canon 5 133 13 CFSG.KD.HNPt2103.K1 ∧ OM CFSG.KD.HNPt2103.K1 = matJ K1J := by
  rw [← Nat.eq_of_beq_eq_true w_K1]
  obtain ⟨h1, h2⟩ := mat_word codes_lt.1
  refine ⟨h1, ?_⟩
  rw [h2, codes_ok.1, prod_scode _ letters_ok.1]

theorem K2_mat :
    Canon 5 133 13 CFSG.KD.HNPt2103.K2 ∧ OM CFSG.KD.HNPt2103.K2 = matJ K2J := by
  rw [← Nat.eq_of_beq_eq_true w_K2]
  obtain ⟨h1, h2⟩ := mat_word codes_lt.2.1
  refine ⟨h1, ?_⟩
  rw [h2, codes_ok.2.1, prod_scode _ letters_ok.2.1]

theorem C1_mat :
    Canon 5 133 13 CFSG.KD.HNPt2103.C1 ∧ OM CFSG.KD.HNPt2103.C1 = matJ C1J := by
  rw [← Nat.eq_of_beq_eq_true w_C1]
  obtain ⟨h1, h2⟩ := mat_word codes_lt.2.2.1
  refine ⟨h1, ?_⟩
  rw [h2, codes_ok.2.2.1, prod_scode _ letters_ok.2.2.2.1]

theorem S0_mat :
    Canon 5 133 13 CFSG.KD.HNPt2103.S0 ∧ OM CFSG.KD.HNPt2103.S0 = matJ S0J := by
  rw [← Nat.eq_of_beq_eq_true w_S0]
  obtain ⟨h1, h2⟩ := mat_word codes_lt.2.2.2
  refine ⟨h1, ?_⟩
  rw [h2, codes_ok.2.2.2, List.map_append, List.prod_append, prod_seed _ letters_ok.2.2.2.2,
    prod_scode _ letters_ok.2.2.1]

theorem conj_J : S0J * K1J = C1J * S0J := by
  refine matJ_injective ?_
  have e := congrArg OM (Nat.eq_of_beq_eq_true conj)
  rw [(HNXP.mm_sound S0_mat.1 K1_mat.1).2, (HNXP.mm_sound C1_mat.1 S0_mat.1).2, S0_mat.2,
    K1_mat.2, C1_mat.2] at e
  rw [matJ_mul S0J K1J, matJ_mul C1J S0J]
  exact e

theorem consts_parts : constsOK CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M = true ∧
    masksOK CFSG.KD.LgHNX.MS = true :=
  HNXP.andB_true' CFSG.KD.LgHNX.consts

theorem PK_eq {i : ℕ} (hi : i < nPts) :
    PK i = HNXP.xvec CFSG.KD.LgHNX.TX i := by
  obtain ⟨-, -, -, hf⟩ := HNXP.orbit_facts HNXCert.hns_bind
  rw [PK, HNXCert.hns_orbit, (hf i hi).1, HNXP.toVecB_orbitVector]
  rfl

theorem gi_pts {g : JH} {W : ℕ} (hW : Canon 5 133 13 W)
    (hm : OM W = matJ g) {FL IL c : ℕ} (hc : c ≤ 64)
    (h : ptsImg CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.MS CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M (trM W) FL IL c =
      true)
    {k : ℕ} (hk : k < c) (h1 : fldW FL (21 * k) 21 < nPts) (h2 : fldW IL (21 * k) 21 < nPts) :
    gi g (fldW FL (21 * k) 21) = fldW IL (21 * k) 21 := by
  refine PK_injective _ (gi_lt g h1) _ h2 ?_
  rw [PK_gi g h1, PK_eq h1, PK_eq h2, ← hm,
    HNXP.ptsImg_sound consts_parts.1 consts_parts.2 hW hc h k hk]

@[expose] def F8L : List ℕ := [0, 88, 53329, 287809, 304994, 437842, 989112, 1126289]

@[expose] def U8L : List ℕ := [0, 88, 668021, 1393, 768919, 1065883, 1019004, 1051783]

theorem lists_ok : (∀ k < 8, fldW CFSG.KD.HNPt2103.F8 (21 * k) 21 = F8L[k]! ∧
      fldW CFSG.KD.HNPt2103.U8 (21 * k) 21 = U8L[k]! ∧ F8L[k]! < nPts ∧ U8L[k]! < nPts ∧
      (U8L[k]! = F8L[k]! ↔ k < 2)) ∧
    fldW CFSG.KD.HNPt2103.FL0 0 21 = 0 ∧ fldW CFSG.KD.HNPt2103.FL0 21 21 = 88 ∧
    fldW CFSG.KD.HNPt2103.IL0 0 21 = 88 ∧ fldW CFSG.KD.HNPt2103.IL0 21 21 = 0 ∧
    (∀ i < 8, ∀ j < 8, F8L[i]! = F8L[j]! → i = j) ∧ F8L[0]! = 0 ∧ F8L[1]! = 88 ∧ U8L[0]! = 0 ∧
    U8L[1]! = 88 := by
  decide +kernel

theorem TK1_eq : CFSG.KD.HNPt2103.TK1 = trM CFSG.KD.HNPt2103.K1 := (Nat.eq_of_beq_eq_true t_K1).symm
theorem TK2_eq : CFSG.KD.HNPt2103.TK2 = trM CFSG.KD.HNPt2103.K2 := (Nat.eq_of_beq_eq_true t_K2).symm
theorem TS0_eq : CFSG.KD.HNPt2103.TS0 = trM CFSG.KD.HNPt2103.S0 := (Nat.eq_of_beq_eq_true t_S0).symm

theorem fix8 {k : ℕ} (hk : k < 8) : gi K1J F8L[k]! = F8L[k]! := by
  have h := p_K1
  rw [TK1_eq] at h
  obtain ⟨e1, -, l1, -⟩ := lists_ok.1 k hk
  have := gi_pts K1_mat.1 K1_mat.2 (by norm_num) h hk (by rw [e1]; exact l1) (by rw [e1]; exact l1)
  rwa [e1] at this

theorem img8 {k : ℕ} (hk : k < 8) : gi K2J F8L[k]! = U8L[k]! := by
  have h := p_K2
  rw [TK2_eq] at h
  obtain ⟨e1, e2, l1, l2, -⟩ := lists_ok.1 k hk
  have := gi_pts K2_mat.1 K2_mat.2 (by norm_num) h hk (by rw [e1]; exact l1) (by rw [e2]; exact l2)
  rwa [e1, e2] at this

theorem s0_pts : gi S0J 0 = 88 ∧ gi S0J 88 = 0 := by
  have h := p_S0
  rw [TS0_eq] at h
  obtain ⟨-, a0, a1, b0, b1, -⟩ := lists_ok
  have e0 := gi_pts S0_mat.1 S0_mat.2 (by norm_num) h (k := 0) (by norm_num)
    (by rw [Nat.mul_zero, a0]; decide) (by rw [Nat.mul_zero, b0]; decide)
  have e1 := gi_pts S0_mat.1 S0_mat.2 (by norm_num) h (k := 1) (by norm_num)
    (by rw [Nat.mul_one, a1]; decide) (by rw [Nat.mul_one, b1]; decide)
  rw [Nat.mul_zero, a0, b0] at e0
  rw [Nat.mul_one, a1, b1] at e1
  exact ⟨e0, e1⟩

theorem fixSum_of {k lo' n' v' : ℕ}
    (h : CFSG.KD.HNXK.fixOk CFSG.KD.HNPt2103.GK1 CFSG.KD.HNXK.FIX2103 0 k = true)
    (h1 : 2227 * k = lo') (h2 : CFSG.KD.HNXK.fixLen k = n')
    (h3 : CFSG.KD.HNXK.FIX2103 (8 * 0 + k) = v') :
    fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M CFSG.KD.HNPt2103.GK1 lo' n' = v' := by
  subst h1 h2 h3
  exact Nat.eq_of_beq_eq_true (CFSG.KD.HNXK.fixOk_spec h)

theorem leaf_total : ∑ b ∈ Finset.range 17813, fixLeaf CFSG.KD.LgHNX.TX 464 CFSG.KD.LgHNX.CM3
    CFSG.KD.LgHNX.M [CFSG.KD.HNPt2103.GK1] b (hnxC b) = 8 := by
  have z : ∑ b ∈ Finset.range 0, fixLeaf CFSG.KD.LgHNX.TX 464 CFSG.KD.LgHNX.CM3
      CFSG.KD.LgHNX.M [CFSG.KD.HNPt2103.GK1] b (hnxC b) = 0 := rfl
  have s0 := HNXP.fixSum_add _ _ _ _ (fixSum_of CFSG.KD.HNXK.F2103.c0 (lo' := 0) (n' := 2227)
    (v' := 3) (by decide) (by decide) (by decide)) z
  have s1 := HNXP.fixSum_add _ _ _ _ (fixSum_of CFSG.KD.HNXK.F2103.c1 (lo' := 2227) (n' := 2227)
    (v' := 0) (by decide) (by decide) (by decide)) s0
  have s2 := HNXP.fixSum_add _ _ _ _ (fixSum_of CFSG.KD.HNXK.F2103.c2 (lo' := 4454) (n' := 2227)
    (v' := 2) (by decide) (by decide) (by decide)) s1
  have s3 := HNXP.fixSum_add _ _ _ _ (fixSum_of CFSG.KD.HNXK.F2103.c3 (lo' := 6681) (n' := 2227)
    (v' := 1) (by decide) (by decide) (by decide)) s2
  have s4 := HNXP.fixSum_add _ _ _ _ (fixSum_of CFSG.KD.HNXK.F2103.c4 (lo' := 8908) (n' := 2227)
    (v' := 0) (by decide) (by decide) (by decide)) s3
  have s5 := HNXP.fixSum_add _ _ _ _ (fixSum_of CFSG.KD.HNXK.F2103.c5 (lo' := 11135) (n' := 2227)
    (v' := 0) (by decide) (by decide) (by decide)) s4
  have s6 := HNXP.fixSum_add _ _ _ _ (fixSum_of CFSG.KD.HNXK.F2103.c6 (lo' := 13362) (n' := 2227)
    (v' := 1) (by decide) (by decide) (by decide)) s5
  have s7 := HNXP.fixSum_add _ _ _ _ (fixSum_of CFSG.KD.HNXK.F2103.c7 (lo' := 15589) (n' := 2224)
    (v' := 1) (by decide) (by decide) (by decide)) s6
  exact s7

theorem subI_K1 :
    Canon 5 133 13 (CFSG.KC.LL.HN.subI CFSG.KD.HNPt2103.K1) ∧
      OM (CFSG.KC.LL.HN.subI CFSG.KD.HNPt2103.K1) = matJ K1J - 1 := by
  have e : CFSG.KC.LL.HN.subI CFSG.KD.HNPt2103.K1 = CFSG.KC.Ord.redP 13 CFSG.KD.OrdHN.L
      CFSG.KD.OrdHN.H 5 9 (CFSG.KD.HNPt2103.K1 + 4 * CFSG.KD.OrdHN.ONE) := by
    unfold CFSG.KC.LL.HN.subI
    congr 1
  rw [e]
  obtain ⟨h1, h2⟩ := CFSG.KS.HNLocal.subOne_sound CFSG.KD.OrdHN.consts K1_mat.1
  have e3 : CFSG.KS.HNLocal.OM CFSG.KD.HNPt2103.K1 = matJ K1J := K1_mat.2
  exact ⟨h1, h2.trans (by rw [e3])⟩

theorem card_fix_k1 :
    ((Finset.range nPts).filter fun i => gi K1J i = i).card = 8 := by
  have h := HNXP.card_fix_eq (T := CFSG.KD.LgHNX.TX) consts_parts.1 subI_K1.1
  rw [Nat.eq_of_beq_eq_true t_GK1, leaf_total] at h
  rw [← h]
  refine congrArg Finset.card (Finset.filter_congr fun i hi => ?_)
  have hi' : i < nPts := Finset.mem_range.1 hi
  rw [subI_K1.2, ← PK_eq hi', Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero, ← PK_gi K1J hi']
  exact ⟨fun h => by rw [h], fun h => PK_injective _ (gi_lt _ hi') _ hi' h⟩

theorem common_fix {x : ℕ} (hx : x < nPts) :
    (gi K1J x = x ∧ gi K2J x = x) ↔ (x = 0 ∨ x = 88) := by
  obtain ⟨hl, -, -, -, -, hinj, h0, h88, u0, u88⟩ := lists_ok
  have hsub : (Finset.range 8).image (fun k => F8L[k]!) ⊆
      (Finset.range nPts).filter fun i => gi K1J i = i := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
    have hk' := Finset.mem_range.1 hk
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨(hl k hk').2.2.1, fix8 hk'⟩
  have hcard : ((Finset.range 8).image fun k => F8L[k]!).card = 8 := by
    rw [Finset.card_image_of_injOn fun i hi j hj e => hinj i (Finset.mem_coe.1 hi |>
      Finset.mem_range.1) j (Finset.mem_coe.1 hj |> Finset.mem_range.1) e, Finset.card_range]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [card_fix_k1, hcard])
  constructor
  · rintro ⟨h1, h2⟩
    have hm : x ∈ (Finset.range 8).image fun k => F8L[k]! := by
      rw [heq, Finset.mem_filter, Finset.mem_range]
      exact ⟨hx, h1⟩
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hm
    have hk' := Finset.mem_range.1 hk
    have h3 : U8L[k]! = F8L[k]! := by rw [← img8 hk', h2]
    have hk2 := ((hl k hk').2.2.2.2).1 h3
    interval_cases k
    · exact Or.inl h0
    · exact Or.inr h88
  · rintro (rfl | rfl)
    · have a := fix8 (k := 0) (by norm_num)
      have b := img8 (k := 0) (by norm_num)
      rw [h0] at a
      rw [h0, u0] at b
      exact ⟨a, b⟩
    · have a := fix8 (k := 1) (by norm_num)
      have b := img8 (k := 1) (by norm_num)
      rw [h88] at a
      rw [h88, u88] at b
      exact ⟨a, b⟩

theorem pinvs1 (g : JH) : pinvs nPts #[arrJ g] = #[arrJ g⁻¹] := by
  simp [pinvs, pinvCand_arrJ]

theorem base_conj :
    (Data.baseList.all fun b => seedWordIdx (arrJ aJ) (arrJ bJ) PointwiseData.g0
      ((arrJ HWJ)[(arrJ K1J)[(arrJ HWJ⁻¹)[seedWordInvIdx (arrJ aJ⁻¹) (arrJ bJ⁻¹) PointwiseData.g0
        b]!]!]!) == (arrJ C1J)[b]!) = true := by
  rw [List.all_eq_true]
  intro b hb
  have hbl := HNIntr.base_lt b hb
  have h1 := gi_lt (seedJ PointwiseData.g0)⁻¹ hbl
  have h2 := gi_lt HWJ⁻¹ h1
  have h3 := gi_lt K1J h2
  rw [HNIntr.seedWordInvIdx_gi _ hbl, arrJ_get _ h1, arrJ_get _ h2, arrJ_get _ h3,
    seedWordIdx_gi _ (gi_lt _ h3), arrJ_get _ hbl, ← gi_mul _ _ h2, ← gi_mul _ _ h1,
    ← gi_mul _ _ hbl, ← gi_mul _ _ hbl]
  have e : seedJ PointwiseData.g0 * (HWJ * K1J * HWJ⁻¹ * (seedJ PointwiseData.g0)⁻¹) = C1J := by
    have := conj_J
    rw [← mul_inv_cancel_right C1J S0J, ← this]
    group
  rw [e]
  exact beq_self_eq_true _

theorem nat_k : ∀ x < 12,
    PointwiseData.k1.foldr (CFSG.KS.TW.GZ HNNat.natF HNNat.natFI) x =
      (natArr PointwiseData.natP)[x]! ∧
    PointwiseData.k2.foldr (CFSG.KS.TW.GZ HNNat.natF HNNat.natFI) x =
      (natArr PointwiseData.natQ)[x]! ∧
    PointwiseData.c1.foldr (CFSG.KS.TW.GZ HNNat.natF HNNat.natFI) x =
      (natArr PointwiseData.natP2)[x]! := by
  decide +kernel

theorem nat_small :
    (∀ j < 12, (((boolWordArr (natArr PointwiseData.natP) (natArr PointwiseData.natQ)
      PointwiseData.ufix)[j]! == j) == (j == 0)) = true) ∧ PointwiseData.tw.length = 12 ∧
    (∀ b < 12, ((boolWordArr (natArr PointwiseData.natP) (natArr PointwiseData.natQ)
      PointwiseData.tw[b]!)[0]! == b) = true) ∧ (natArr PointwiseData.natP)[7]! = 7 ∧
    (∀ j < 12, ((natArr PointwiseData.natP2)[j]! != j) = true) := by
  decide +kernel

theorem pointwiseChecks_ok :
    pointwiseChecks (hnsData.orbit ()) = true := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := letters_ok
  obtain ⟨n1, n2, n3, n4, n5⟩ := nat_small
  unfold pointwiseChecks
  try dsimp only
  rw [hns_n, natTab_alpha, natTab_beta, regs_get (k := 1) (by omega), regs_get (k := 2) (by omega),
    hS_eq, HNIntr.pinvs2, pword_arrJ SJ_arrs _ l1, pword_arrJ SJ_arrs _ l2,
    pword_arrJ SJ_arrs _ l3, pword_arrJ SJ_arrs _ l4, pinvs1]
  simp only [List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ,
    Bool.and_eq_true, beq_iff_eq, and_assoc, List.size_toArray, List.length_cons,
    List.length_nil]
  refine ⟨trivial, pisInv_arrJ _, pisInv_arrJ _, by decide +kernel, plettersOK_iff.2 l3,
    plettersOK_iff.2 l1, plettersOK_iff.2 l2, plettersOK_iff.2 l4, trivial, pisInv_arrJ _, ?_, ?_,
    ?_, base_conj, ?_, ?_, ?_, CFSG.ONSchreier.allBelowN_iff.2 n1, n2,
    CFSG.ONSchreier.allBelowN_iff.2 n3, n4, CFSG.ONSchreier.allBelowN_iff.2 n5⟩
  · rw [arrJ_get _ (by decide), seedWordIdx_gi _ (gi_lt _ (by decide)), ← gi_mul _ _ (by decide)]
    exact s0_pts.1
  · rw [arrJ_get _ (by decide), seedWordIdx_gi _ (gi_lt _ (by decide)), ← gi_mul _ _ (by decide)]
    exact s0_pts.2
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun x hx => ?_
    rw [arrJ_get _ hx, arrJ_get _ hx]
    have key : (gi K1J x == x && gi K2J x == x) = (x == 0 || x == 88) := by
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
      exact common_fix hx
    rw [key]
    exact beq_self_eq_true _
  · exact HNNat.peq_maps fun x hx => by rw [HNNat.natWord_pt l1 hx, (nat_k x hx).1]
  · exact HNNat.peq_maps fun x hx => by rw [HNNat.natWord_pt l2 hx, (nat_k x hx).2.1]
  · exact HNNat.peq_maps fun x hx => by rw [HNNat.natWord_pt l4 hx, (nat_k x hx).2.2]

end CertificateChecks.KernelSporSch.HNPt2103

end
