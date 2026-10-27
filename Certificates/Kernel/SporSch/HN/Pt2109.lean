
module

public import Certificates.Kernel.SporSch.HN.Pt2103
public import Certificates.Kernel.SporSch.HN.Pt2109K
public import Certificates.Kernel.SporSch.HN.FixK.P2109G0
public import Certificates.Kernel.SporSch.HN.FixK.P2109G1
public import Certificates.Kernel.SporSch.HN.FixK.P2109G2
public import Certificates.Kernel.SporSch.HN.FixK.P2109G3
public import Certificates.Kernel.SporSch.HN.FixK.Spec
public import CFSG.Certificates.Kernel.SporSch.HNXPtLSound
public import CFSG.Certificates.Kernel.VecKTrees
public import CFSG.Sporadic.HNSchreier.ThreeCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNPt2109

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS CFSG.KS.SporSch CFSG.KS.HNArr CFSG.KS.Ord
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.HNArrS CertificateChecks.KernelSporSch.HNPt2103 Matrix

local notation "OM" => ordMat 5 133 13 1729
local notation "TX" => CFSG.KD.LgHNX.TX

theorem scode_lt {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 17) : scode l < 36 := by
  unfold scode
  split <;> omega

theorem strong_elem {w : List ℤ} {cs : List ℕ} {W : ℕ}
    (hw : wordC CFSG.KD.HNPt.R cs = W) (hc : cs = w.map scode)
    (hl : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 17) : Canon 5 133 13 W ∧ OM W = matJ (wJ sL w) := by
  rw [← hw]
  obtain ⟨h1, h2⟩ := mat_word (cs := cs) fun c hc' => by
    rw [hc, List.mem_map] at hc'
    obtain ⟨l, hl', rfl⟩ := hc'
    exact scode_lt (hl l hl')
  refine ⟨h1, ?_⟩
  rw [h2, hc, prod_scode w hl]

noncomputable abbrev G3J : JH := seedJ FAData.g3Root * wJ sL FAData.g3H

theorem letters_ok : (∀ k < 4, ∀ l ∈ FAData.sWords[k]!, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ j < 8, ∀ l ∈ FAData.c1Words[j]!, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ j < 6, ∀ l ∈ FAData.c3Words[j]!, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ l ∈ FAData.g3H, l ≠ 0 ∧ l.natAbs ≤ 17) ∧ (∀ l ∈ FAData.g3Root, l = 1 ∨ l = 2) := by
  decide +kernel

open CFSG.KD.HNPt2109 in
theorem codes_ok : s0c = FAData.sWords[0]!.map scode ∧ s1c = FAData.sWords[1]!.map scode ∧
    s2c = FAData.sWords[2]!.map scode ∧ s3c = FAData.sWords[3]!.map scode ∧
    c1c0 = FAData.c1Words[0]!.map scode ∧ c1c1 = FAData.c1Words[1]!.map scode ∧
    c1c2 = FAData.c1Words[2]!.map scode ∧ c1c3 = FAData.c1Words[3]!.map scode ∧
    c1c4 = FAData.c1Words[4]!.map scode ∧ c1c5 = FAData.c1Words[5]!.map scode ∧
    c1c6 = FAData.c1Words[6]!.map scode ∧ c1c7 = FAData.c1Words[7]!.map scode ∧
    c3c0 = FAData.c3Words[0]!.map scode ∧ c3c1 = FAData.c3Words[1]!.map scode ∧
    c3c2 = FAData.c3Words[2]!.map scode ∧ c3c3 = FAData.c3Words[3]!.map scode ∧
    c3c4 = FAData.c3Words[4]!.map scode ∧ c3c5 = FAData.c3Words[5]!.map scode ∧
    c3c6 = FAData.g3Root.map (33 + ·) ++ FAData.g3H.map scode := by
  decide +kernel

@[expose] noncomputable def SW (k : ℕ) : ℕ :=
  [CFSG.KD.HNPt2109.S0, CFSG.KD.HNPt2109.S1, CFSG.KD.HNPt2109.S2, CFSG.KD.HNPt2109.S3].getD k 0

@[expose] noncomputable def C1W (j : ℕ) : ℕ :=
  [CFSG.KD.HNPt2109.C1_0, CFSG.KD.HNPt2109.C1_1, CFSG.KD.HNPt2109.C1_2, CFSG.KD.HNPt2109.C1_3,
    CFSG.KD.HNPt2109.C1_4, CFSG.KD.HNPt2109.C1_5, CFSG.KD.HNPt2109.C1_6,
    CFSG.KD.HNPt2109.C1_7].getD j 0

@[expose] noncomputable def C3W (j : ℕ) : ℕ :=
  [CFSG.KD.HNPt2109.C3_0, CFSG.KD.HNPt2109.C3_1, CFSG.KD.HNPt2109.C3_2, CFSG.KD.HNPt2109.C3_3,
    CFSG.KD.HNPt2109.C3_4, CFSG.KD.HNPt2109.C3_5, CFSG.KD.HNPt2109.C3_6].getD j 0

noncomputable abbrev SJk (k : ℕ) : JH := wJ sL FAData.sWords[k]!
noncomputable abbrev C1J (j : ℕ) : JH := wJ sL FAData.c1Words[j]!
noncomputable abbrev C3J (j : ℕ) : JH := if j < 6 then wJ sL FAData.c3Words[j]! else G3J

theorem S_mat {k : ℕ} (hk : k < 4) :
    Canon 5 133 13 (SW k) ∧ OM (SW k) = matJ (SJk k) := by
  obtain ⟨a, b, c, d⟩ := w_S
  obtain ⟨e0, e1, e2, e3, -⟩ := codes_ok
  have hl := letters_ok.1 k hk
  interval_cases k
  · exact strong_elem a e0 hl
  · exact strong_elem b e1 hl
  · exact strong_elem c e2 hl
  · exact strong_elem d e3 hl

theorem C1_mat {j : ℕ} (hj : j < 8) :
    Canon 5 133 13 (C1W j) ∧ OM (C1W j) = matJ (C1J j) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := w_C1
  obtain ⟨-, -, -, -, e0, e1, e2, e3, e4, e5, e6, e7, -⟩ := codes_ok
  have hl := letters_ok.2.1 j hj
  interval_cases j
  · exact strong_elem a0 e0 hl
  · exact strong_elem a1 e1 hl
  · exact strong_elem a2 e2 hl
  · exact strong_elem a3 e3 hl
  · exact strong_elem a4 e4 hl
  · exact strong_elem a5 e5 hl
  · exact strong_elem a6 e6 hl
  · exact strong_elem a7 e7 hl

theorem C3_mat {j : ℕ} (hj : j < 7) :
    Canon 5 133 13 (C3W j) ∧ OM (C3W j) = matJ (C3J j) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := w_C3
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, e0, e1, e2, e3, e4, e5, e6⟩ := codes_ok
  obtain ⟨-, -, hl3, hg, hr⟩ := letters_ok
  interval_cases j
  · exact strong_elem a0 e0 (hl3 0 (by norm_num))
  · exact strong_elem a1 e1 (hl3 1 (by norm_num))
  · exact strong_elem a2 e2 (hl3 2 (by norm_num))
  · exact strong_elem a3 e3 (hl3 3 (by norm_num))
  · exact strong_elem a4 e4 (hl3 4 (by norm_num))
  · exact strong_elem a5 e5 (hl3 5 (by norm_num))
  · change Canon 5 133 13 CFSG.KD.HNPt2109.C3_6 ∧ OM CFSG.KD.HNPt2109.C3_6 = matJ G3J
    rw [← a6]
    obtain ⟨h1, h2⟩ := mat_word (cs := CFSG.KD.HNPt2109.c3c6) fun c hc => by
      rw [e6, List.mem_append, List.mem_map, List.mem_map] at hc
      rcases hc with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
      · rcases hr l hl with rfl | rfl <;> norm_num
      · exact scode_lt (hg l hl)
    refine ⟨h1, ?_⟩
    rw [h2, e6, List.map_append, List.prod_append, prod_seed _ hr, prod_scode _ hg]

theorem comm_of {g h : JH} {Wg Wh : ℕ} (hg : Canon 5 133 13 Wg ∧ OM Wg = matJ g)
    (hh : Canon 5 133 13 Wh ∧ OM Wh = matJ h)
    (e : CFSG.KC.LL.HN.mm Wg Wh = CFSG.KC.LL.HN.mm Wh Wg) : g * h = h * g := by
  refine matJ_injective ?_
  have e2 := congrArg OM e
  rw [(HNXP.mm_sound hg.1 hh.1).2, (HNXP.mm_sound hh.1 hg.1).2, hg.2, hh.2] at e2
  rw [matJ_mul g h, matJ_mul h g]
  exact e2

theorem comm1 {j : ℕ} (hj : j < 8) : C1J j * SJk 0 = SJk 0 * C1J j := by
  refine comm_of (C1_mat hj) (S_mat (k := 0) (by norm_num)) ?_
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := cm_C1
  interval_cases j
  · exact a0
  · exact a1
  · exact a2
  · exact a3
  · exact a4
  · exact a5
  · exact a6
  · exact a7

theorem comm3 {j : ℕ} (hj : j < 7) : C3J j * SJk 2 = SJk 2 * C3J j := by
  refine comm_of (C3_mat hj) (S_mat (k := 2) (by norm_num)) ?_
  obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := cm_C3
  interval_cases j
  · exact a0
  · exact a1
  · exact a2
  · exact a3
  · exact a4
  · exact a5
  · exact a6

theorem gi_fn {g : JH} {W : ℕ} (hW : Canon 5 133 13 W)
    (hm : OM W = matJ g) {f h : ℕ → ℕ} {n : ℕ}
    (hp : ptsFn TX CFSG.KD.LgHNX.MS CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M (trM W) f h n = true)
    (hb : ∀ k < n, f k < nPts ∧ h k < nPts) {k : ℕ} (hk : k < n) : gi g (f k) = h k := by
  have hb' : ∀ k < n, f k < 2 ^ 21 ∧ h k < 2 ^ 21 := fun k hk =>
    ⟨by have := (hb k hk).1; change f k < 1140000 at this; omega,
      by have := (hb k hk).2; change h k < 1140000 at this; omega⟩
  refine PK_injective _ (gi_lt g (hb k hk).1) _ (hb k hk).2 ?_
  rw [PK_gi g (hb k hk).1, PK_eq (hb k hk).1, PK_eq (hb k hk).2, ← hm,
    HNXP.ptsFn_sound consts_parts.1 consts_parts.2 hW hp hb' k hk]

theorem fixSum_of {G : ℕ} {V : ℕ → ℕ} {m k lo' n' : ℕ} (h : CFSG.KD.HNXK.fixOk G V m k = true)
    (h1 : 2227 * k = lo') (h2 : CFSG.KD.HNXK.fixLen k = n') :
    fixSum TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G lo' n' = V (8 * m + k) := by
  subst h1 h2
  exact Nat.eq_of_beq_eq_true (CFSG.KD.HNXK.fixOk_spec h)

theorem sum8 {G v0 v1 v2 v3 v4 v5 v6 v7 : ℕ}
    (h0 : fixSum TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 0 2227 = v0)
    (h1 : fixSum TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 2227 2227 = v1)
    (h2 : fixSum TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 4454 2227 = v2)
    (h3 : fixSum TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 6681 2227 = v3)
    (h4 : fixSum TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 8908 2227 = v4)
    (h5 : fixSum TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 11135 2227 = v5)
    (h6 : fixSum TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 13362 2227 = v6)
    (h7 : fixSum TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 15589 2224 = v7) :
    ∑ b ∈ Finset.range 17813, fixLeaf TX 464 CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M [G] b (hnxC b) =
      v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 := by
  have z : ∑ b ∈ Finset.range 0, fixLeaf TX 464 CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M [G] b
      (hnxC b) = 0 := rfl
  have s0 := HNXP.fixSum_add _ _ _ _ h0 z
  have s1 := HNXP.fixSum_add _ _ _ _ h1 s0
  have s2 := HNXP.fixSum_add _ _ _ _ h2 s1
  have s3 := HNXP.fixSum_add _ _ _ _ h3 s2
  have s4 := HNXP.fixSum_add _ _ _ _ h4 s3
  have s5 := HNXP.fixSum_add _ _ _ _ h5 s4
  have s6 := HNXP.fixSum_add _ _ _ _ h6 s5
  have s7 := HNXP.fixSum_add _ _ _ _ h7 s6
  rw [Nat.zero_add] at s7
  exact s7

theorem subI_sound {W : ℕ} (hW : Canon 5 133 13 W) :
    Canon 5 133 13 (CFSG.KC.LL.HN.subI W) ∧ OM (CFSG.KC.LL.HN.subI W) = OM W - 1 := by
  have e : CFSG.KC.LL.HN.subI W = CFSG.KC.Ord.redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9
      (W + 4 * CFSG.KD.OrdHN.ONE) := by
    unfold CFSG.KC.LL.HN.subI
    congr 1
  rw [e]
  exact CFSG.KS.HNLocal.subOne_sound CFSG.KD.OrdHN.consts hW

theorem card_fix_of {g : JH} {W G N : ℕ} (hW : Canon 5 133 13 W)
    (hm : OM W = matJ g) (hG : trM (CFSG.KC.LL.HN.subI W) = G)
    (htot : ∑ b ∈ Finset.range 17813, fixLeaf TX 464 CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M [G] b
      (hnxC b) = N) :
    ((Finset.range nPts).filter fun i => gi g i = i).card = N := by
  have h := HNXP.card_fix_eq (T := TX) consts_parts.1 (subI_sound hW).1
  rw [hG, htot] at h
  rw [← h]
  refine congrArg Finset.card (Finset.filter_congr fun i hi => ?_)
  have hi' : i < nPts := Finset.mem_range.1 hi
  rw [(subI_sound hW).2, hm, ← PK_eq hi', Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero,
    ← PK_gi g hi']
  exact ⟨fun h => by rw [h], fun h => PK_injective _ (gi_lt _ hi') _ hi' h⟩

theorem countP_range (n : ℕ) (p : ℕ → Bool) :
    (List.range n).countP p = ((Finset.range n).filter fun i => p i = true).card := by
  rw [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card, List.countP_eq_length_filter]
  simp

theorem fixList_of {g : JH} {W : ℕ} {L : List ℕ}
    (hW : Canon 5 133 13 W) (hm : OM W = matJ g)
    (hp : ptsFn TX CFSG.KD.LgHNX.MS CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M (trM W) (HNX.lget L) (HNX.lget L)
      L.length = true)
    (hlt : ∀ x ∈ L, x < nPts) (hsort : (L.zip L.tail).all (fun p => decide (p.1 < p.2)) = true)
    (hcard : ((Finset.range nPts).filter fun i => gi g i = i).card = L.length) :
    fixListOK nPts (arrJ g) L = true := by
  have hb : ∀ k < L.length, HNX.lget L k < nPts ∧ HNX.lget L k < nPts := fun k hk => by
    have : HNX.lget L k = L[k] := List.getD_eq_getElem _ _ hk
    rw [this]
    exact ⟨hlt _ (List.getElem_mem hk), hlt _ (List.getElem_mem hk)⟩
  unfold fixListOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hsort, List.all_eq_true.2 fun x hx => ?_⟩, ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have e : HNX.lget L k = L[k] := List.getD_eq_getElem _ _ hk
    have hfx := gi_fn hW hm hp hb hk
    rw [e] at hfx
    rw [arrJ_get _ (hlt _ (List.getElem_mem hk)), hfx]
    simp [hlt _ (List.getElem_mem hk)]
  · rw [countP_range, ← hcard]
    refine congrArg Finset.card (Finset.filter_congr fun i hi => ?_)
    rw [arrJ_get _ (Finset.mem_range.1 hi)]
    simp

theorem ap_toTable {g : JH} {x : ℕ} (hx : x < nPts) : ap (toTable (arrJ g)) x = gi g x := by
  have hv := arrJ_get g hx
  have hs : x < (arrJ g).size := by rw [arrJ_size]; exact hx
  have hlt := gi_lt g hx
  unfold ap toTable
  generalize arrJ g = A at hv hs ⊢
  rw [getElem!_pos _ x (by rw [Array.size_map]; exact hs), Array.getElem_map,
    ← getElem!_pos A x hs, hv, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt (by norm_num))

theorem toTable_size (a : Array ℕ) : (toTable a).size = a.size := by simp [toTable]

theorem tree_spec {letters : Array Table} {gens : ℕ → JH}
    {nl r : ℕ} {P PU PL : List ℕ} {JL : ℕ → List ℕ} (hnl : nl ≤ 8) (hlet : letters.size = nl)
    (hget : ∀ l < nl, letters[l]! = toTable (arrJ (gens l)))
    (himg : ∀ l < nl, ∀ t < P.length, gi (gens l) (HNX.lget P t) = HNX.lget P (HNX.lget (JL l) t))
    (hP0 : 0 < P.length) (hroot : HNX.lget P 0 = r) (hr : r < nPts)
    (hpts : ∀ t < P.length, HNX.lget P t < nPts ∧ P.idxOf (HNX.lget P t) = t)
    (hJ : ∀ l < nl, ∀ t < P.length, HNX.lget (JL l) t < P.length)
    (hpar : ∀ t < P.length, 0 < t → HNX.lget PU t < t ∧ HNX.lget PL t < nl ∧
      HNX.lget (JL (HNX.lget PL t)) (HNX.lget PU t) = t) :
    CFSG.KC.VecK.BFSSpec nPts r letters (Array.range letters.size)
        (treeBFS nPts r letters (Array.range letters.size)) ∧
      (treeBFS nPts r letters (Array.range letters.size)).pts.size = P.length ∧
      ∀ q, (∃ t < P.length, HNX.lget P t = q) ↔
        ∃ t < (treeBFS nPts r letters (Array.range letters.size)).pts.size,
          ap (treeBFS nPts r letters (Array.range letters.size)).pts t = q := by
  have hmem : ∀ l, l ∈ Array.range letters.size ↔ l < nl := fun l => by
    rw [Array.mem_range, hlet]
  have hap : ∀ l < nl, ∀ x < nPts, ap letters[l]! x = gi (gens l) x := fun l hl x hx => by
    rw [hget l hl]
    exact ap_toTable hx
  refine CFSG.KC.VecK.bfs_of_facts (pt := HNX.lget P) (ix := P.idxOf) (by norm_num) hr
    (fun l hl => by have := (hmem l).1 hl; omega)
    (fun l hl x hx => by rw [hap l ((hmem l).1 hl) x hx]; exact gi_lt _ hx)
    ⟨hP0, hroot, fun t ht => (hpts t ht).2, fun t ht l hl => ?_, fun t ht h0 => ?_⟩
  · have hl' := (hmem l).1 hl
    have hj := hJ l hl' t ht
    rw [hap l hl' _ (hpts t ht).1, himg l hl' t ht, (hpts _ hj).2]
    exact ⟨hj, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := hpar t ht h0
    refine ⟨HNX.lget PU t, h1, HNX.lget PL t, (hmem _).2 h2, ?_⟩
    rw [hap _ h2 _ (hpts _ (by omega)).1, himg _ h2 _ (by omega), h3]

theorem img_of {g : JH} {W G : ℕ} {P J : List ℕ}
    (hW : Canon 5 133 13 W ∧ OM W = matJ g) (hG : trM W = G) (hT : treeImg G P J = true)
    (hP : ∀ t < P.length, HNX.lget P t < nPts) (hJ : ∀ t < P.length, HNX.lget J t < P.length) :
    ∀ t < P.length, gi g (HNX.lget P t) = HNX.lget P (HNX.lget J t) := by
  rw [← hG] at hT
  intro t ht
  exact gi_fn hW.1 hW.2 hT (fun k hk => ⟨hP k hk, hP _ (hJ k hk)⟩) ht

open CFSG.KD.HNPt2109 in
@[expose] noncomputable def JL1 (t l : ℕ) : List ℕ :=
  ([[J0_0, J0_1, J0_2, J0_3, J0_4, J0_5, J0_6, J0_7], [J1_0, J1_1, J1_2, J1_3, J1_4, J1_5, J1_6, J1_7],
    [J2_0, J2_1, J2_2, J2_3, J2_4, J2_5, J2_6, J2_7]].getD t []).getD l []

open CFSG.KD.HNPt2109 in
@[expose] noncomputable def JL3 (l : ℕ) : List ℕ := [J3_0, J3_1, J3_2, J3_3, J3_4, J3_5, J3_6].getD l []

open CFSG.KD.HNPt2109 in
@[expose] noncomputable def PT (t : ℕ) : List ℕ := [P0, P1, P2, P3].getD t []

open CFSG.KD.HNPt2109 in
@[expose] noncomputable def PUT (t : ℕ) : List ℕ := [PU0, PU1, PU2, PU3].getD t []

open CFSG.KD.HNPt2109 in
@[expose] noncomputable def PLT (t : ℕ) : List ℕ := [PL0, PL1, PL2, PL3].getD t []

@[expose] def rootT (t : ℕ) : ℕ := [0, 1047, 119497, 0].getD t 0

theorem data1 : ∀ t < 3, 0 < (PT t).length ∧ HNX.lget (PT t) 0 = rootT t ∧ rootT t < nPts ∧
    (∀ i < (PT t).length, HNX.lget (PT t) i < nPts ∧ (PT t).idxOf (HNX.lget (PT t) i) = i) ∧
    (∀ l < 8, ∀ i < (PT t).length, HNX.lget (JL1 t l) i < (PT t).length) ∧
    (∀ i < (PT t).length, 0 < i → HNX.lget (PUT t) i < i ∧ HNX.lget (PLT t) i < 8 ∧
      HNX.lget (JL1 t (HNX.lget (PLT t) i)) (HNX.lget (PUT t) i) = i) := by
  decide +kernel

theorem data3 : 0 < (PT 3).length ∧ HNX.lget (PT 3) 0 = rootT 3 ∧ rootT 3 < nPts ∧
    (∀ i < (PT 3).length, HNX.lget (PT 3) i < nPts ∧ (PT 3).idxOf (HNX.lget (PT 3) i) = i) ∧
    (∀ l < 7, ∀ i < (PT 3).length, HNX.lget (JL3 l) i < (PT 3).length) ∧
    (∀ i < (PT 3).length, 0 < i → HNX.lget (PUT 3) i < i ∧ HNX.lget (PLT 3) i < 7 ∧
      HNX.lget (JL3 (HNX.lget (PLT 3) i)) (HNX.lget (PUT 3) i) = i) := by
  decide +kernel

theorem sizes_PT : (PT 0).length = 1 ∧ (PT 1).length = 560 ∧ (PT 2).length = 84 ∧
    (PT 3).length = 60 := by decide +kernel

theorem fixed0_in : ∀ x ∈ FAData.sFixed[0]!, x ∈ PT 0 ∨ x ∈ PT 1 ∨ x ∈ PT 2 := by decide +kernel

theorem img1 {t : ℕ} (ht : t < 3) :
    ∀ l < 8, ∀ i < (PT t).length,
      gi (C1J l) (HNX.lget (PT t) i) = HNX.lget (PT t) (HNX.lget (JL1 t l) i) := by
  intro l hl
  obtain ⟨-, -, -, hpts, hJ, -⟩ := data1 t ht
  have hP : ∀ i < (PT t).length, HNX.lget (PT t) i < nPts := fun i hi => (hpts i hi).1
  have hJ' := hJ l hl
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := t_C1
  interval_cases t
  · obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := tr_0
    interval_cases l
    · exact img_of (C1_mat (by norm_num)) c0 b0 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c1 b1 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c2 b2 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c3 b3 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c4 b4 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c5 b5 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c6 b6 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c7 b7 hP hJ'
  · obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := tr_1
    interval_cases l
    · exact img_of (C1_mat (by norm_num)) c0 b0 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c1 b1 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c2 b2 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c3 b3 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c4 b4 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c5 b5 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c6 b6 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c7 b7 hP hJ'
  · obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := tr_2
    interval_cases l
    · exact img_of (C1_mat (by norm_num)) c0 b0 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c1 b1 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c2 b2 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c3 b3 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c4 b4 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c5 b5 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c6 b6 hP hJ'
    · exact img_of (C1_mat (by norm_num)) c7 b7 hP hJ'

theorem img3 :
    ∀ l < 7, ∀ i < (PT 3).length,
      gi (C3J l) (HNX.lget (PT 3) i) = HNX.lget (PT 3) (HNX.lget (JL3 l) i) := by
  intro l hl
  obtain ⟨-, -, -, hpts, hJ, -⟩ := data3
  have hP : ∀ i < (PT 3).length, HNX.lget (PT 3) i < nPts := fun i hi => (hpts i hi).1
  have hJ' := hJ l hl
  obtain ⟨d0, d1, d2, d3, d4, d5, d6⟩ := t_C3
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := tr_3
  interval_cases l
  · exact img_of (C3_mat (by norm_num)) d0 b0 hP hJ'
  · exact img_of (C3_mat (by norm_num)) d1 b1 hP hJ'
  · exact img_of (C3_mat (by norm_num)) d2 b2 hP hJ'
  · exact img_of (C3_mat (by norm_num)) d3 b3 hP hJ'
  · exact img_of (C3_mat (by norm_num)) d4 b4 hP hJ'
  · exact img_of (C3_mat (by norm_num)) d5 b5 hP hJ'
  · exact img_of (C3_mat (by norm_num)) d6 b6 hP hJ'

noncomputable abbrev L1T : Array Table := (Array.ofFn (n := 8) fun j => arrJ (C1J j)).map toTable

noncomputable abbrev L3T : Array Table := (Array.ofFn (n := 7) fun j => arrJ (C3J j)).map toTable

theorem tree1 {t : ℕ} (ht : t < 3) :
    CFSG.KC.VecK.BFSSpec nPts (rootT t) L1T (Array.range L1T.size)
        (treeBFS nPts (rootT t) L1T (Array.range L1T.size)) ∧
      (treeBFS nPts (rootT t) L1T (Array.range L1T.size)).pts.size = (PT t).length ∧
      ∀ q, (∃ i < (PT t).length, HNX.lget (PT t) i = q) ↔
        ∃ i < (treeBFS nPts (rootT t) L1T (Array.range L1T.size)).pts.size,
          ap (treeBFS nPts (rootT t) L1T (Array.range L1T.size)).pts i = q := by
  obtain ⟨h0, hr, hrn, hpts, hJ, hpar⟩ := data1 t ht
  refine tree_spec (gens := C1J) (nl := 8) (JL := JL1 t) (PU := PUT t) (PL := PLT t) le_rfl
    (by rw [Array.size_map, Array.size_ofFn]) (fun l hl => ?_) (img1 ht) h0 hr hrn hpts hJ hpar
  rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map, Array.getElem_ofFn]

theorem tree3 :
    CFSG.KC.VecK.BFSSpec nPts (rootT 3) L3T (Array.range L3T.size)
        (treeBFS nPts (rootT 3) L3T (Array.range L3T.size)) ∧
      (treeBFS nPts (rootT 3) L3T (Array.range L3T.size)).pts.size = (PT 3).length := by
  obtain ⟨h0, hr, hrn, hpts, hJ, hpar⟩ := data3
  have hget : ∀ l < 7, L3T[l]! = toTable (arrJ (C3J l)) := fun l hl => by
    rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map, Array.getElem_ofFn]
  obtain ⟨a, b, -⟩ := tree_spec (gens := C3J) (nl := 7) (JL := JL3) (PU := PUT 3) (PL := PLT 3)
    (by norm_num) (by rw [Array.size_map, Array.size_ofFn]) hget img3 h0 hr hrn hpts hJ hpar
  exact ⟨a, b⟩

open CFSG.KD.HNPt2109 in
theorem fx_data : FX0 = FAData.sFixed[0]! ∧ FX1 = FAData.sFixed[1]! ∧ FX2 = FAData.sFixed[2]! ∧
    FX3 = FAData.sFixed[3]! ∧ (∀ k < 4, ∀ x ∈ FAData.sFixed[k]!, x < nPts) ∧
    (∀ k < 4, ((FAData.sFixed[k]!).zip (FAData.sFixed[k]!).tail).all
      (fun p => decide (p.1 < p.2)) = true) ∧
    FX0.length = 645 ∧ FX1.length = 645 ∧ FX2.length = 60 ∧ FX3.length = 645 := by
  decide +kernel

open CFSG.KD.HNPt2109 CFSG.KD.HNXK in
theorem tot_S : (∑ b ∈ Finset.range 17813, fixLeaf TX 464 CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M [GS0] b
      (hnxC b) = FX0.length) ∧
    (∑ b ∈ Finset.range 17813, fixLeaf TX 464 CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M [GS1] b
      (hnxC b) = FX1.length) ∧
    (∑ b ∈ Finset.range 17813, fixLeaf TX 464 CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M [GS2] b
      (hnxC b) = FX2.length) ∧
    ∑ b ∈ Finset.range 17813, fixLeaf TX 464 CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M [GS3] b
      (hnxC b) = FX3.length := by
  obtain ⟨-, -, -, -, -, -, l0, l1, l2, l3⟩ := fx_data
  rw [l0, l1, l2, l3]
  refine ⟨(sum8 (fixSum_of F2109_0.c0 (lo' := 0) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_0.c1 (lo' := 2227) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_0.c2 (lo' := 4454) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_0.c3 (lo' := 6681) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_0.c4 (lo' := 8908) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_0.c5 (lo' := 11135) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_0.c6 (lo' := 13362) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_0.c7 (lo' := 15589) (n' := 2224) (by decide) (by decide))).trans
      (by decide +kernel),
    (sum8 (fixSum_of F2109_1.c0 (lo' := 0) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_1.c1 (lo' := 2227) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_1.c2 (lo' := 4454) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_1.c3 (lo' := 6681) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_1.c4 (lo' := 8908) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_1.c5 (lo' := 11135) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_1.c6 (lo' := 13362) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_1.c7 (lo' := 15589) (n' := 2224) (by decide) (by decide))).trans
      (by decide +kernel),
    (sum8 (fixSum_of F2109_2.c0 (lo' := 0) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_2.c1 (lo' := 2227) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_2.c2 (lo' := 4454) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_2.c3 (lo' := 6681) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_2.c4 (lo' := 8908) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_2.c5 (lo' := 11135) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_2.c6 (lo' := 13362) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_2.c7 (lo' := 15589) (n' := 2224) (by decide) (by decide))).trans
      (by decide +kernel),
    (sum8 (fixSum_of F2109_3.c0 (lo' := 0) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_3.c1 (lo' := 2227) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_3.c2 (lo' := 4454) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_3.c3 (lo' := 6681) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_3.c4 (lo' := 8908) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_3.c5 (lo' := 11135) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_3.c6 (lo' := 13362) (n' := 2227) (by decide) (by decide))
    (fixSum_of F2109_3.c7 (lo' := 15589) (n' := 2224) (by decide) (by decide))).trans
      (by decide +kernel)⟩

open CFSG.KD.HNPt2109 in
theorem fix_S {k : ℕ} (hk : k < 4) :
    fixListOK nPts (arrJ (SJk k)) FAData.sFixed[k]! = true := by
  obtain ⟨e0, e1, e2, e3, hlt, hsort, -⟩ := fx_data
  obtain ⟨t0, t1, t2, t3⟩ := t_S
  obtain ⟨g0, g1, g2, g3⟩ := g_S
  obtain ⟨n0, n1, n2, n3⟩ := tot_S
  have hm := S_mat hk
  have hl := hlt k hk
  have hs := hsort k hk
  interval_cases k
  · rw [← e0] at hl hs ⊢
    have h := fx_0
    rw [← t0] at h
    exact fixList_of (W := S0) hm.1 hm.2 h hl hs (card_fix_of (W := S0) hm.1 hm.2 g0 n0)
  · rw [← e1] at hl hs ⊢
    have h := fx_1
    rw [← t1] at h
    exact fixList_of (W := S1) hm.1 hm.2 h hl hs (card_fix_of (W := S1) hm.1 hm.2 g1 n1)
  · rw [← e2] at hl hs ⊢
    have h := fx_2
    rw [← t2] at h
    exact fixList_of (W := S2) hm.1 hm.2 h hl hs (card_fix_of (W := S2) hm.1 hm.2 g2 n2)
  · rw [← e3] at hl hs ⊢
    have h := fx_3
    rw [← t3] at h
    exact fixList_of (W := S3) hm.1 hm.2 h hl hs (card_fix_of (W := S3) hm.1 hm.2 g3 n3)

theorem inTree_of {T : Tree} {r : ℕ} {letters : Array Table} {lv : Array ℕ} {x : ℕ}
    (hB : CFSG.KC.VecK.BFSSpec nPts r letters lv T) (hx : ∃ i < T.pts.size, ap T.pts i = x) :
    inTree T x = true := by
  obtain ⟨i, hi, rfl⟩ := hx
  unfold inTree
  rw [hB.facts.ix_pt i hi]
  simp [hi]

theorem seedWordArr_arrJ :
    ∀ w : List ℕ, (∀ l ∈ w, l = 1 ∨ l = 2) →
      seedWordArr nPts (arrJ aJ) (arrJ bJ) w = arrJ (seedJ w)
  | [], _ => pid_arrJ
  | l :: w, hw => by
    change pcomp nPts (if l = 1 then arrJ aJ else arrJ bJ) (seedWordArr nPts (arrJ aJ) (arrJ bJ) w) = _
    rw [seedWordArr_arrJ w fun z hz => hw z (List.mem_cons_of_mem l hz), seedJ]
    rcases hw l List.mem_cons_self with rfl | rfl
    · rw [if_pos rfl, if_pos rfl, pcomp_arrJ]
    · rw [if_neg (by omega), if_neg (by omega), pcomp_arrJ]

theorem c1_eq : FAData.c1Words.map (fun w => pword nPts SJ (pinvs nPts SJ) w) =
    Array.ofFn (n := 8) fun j => arrJ (C1J j) := by
  have hs : FAData.c1Words.size = 8 := by decide
  refine Array.ext (by rw [Array.size_map, Array.size_ofFn, hs]) fun j h1 h2 => ?_
  have hj : j < 8 := by simpa using h2
  rw [Array.getElem_map, Array.getElem_ofFn, ← getElem!_pos FAData.c1Words j (by rw [hs]; exact hj),
    pword_arrJ SJ_arrs _ (letters_ok.2.1 j hj)]

theorem c3_eq :
    (FAData.c3Words.map (fun w => pword nPts SJ (pinvs nPts SJ) w)).push
      (pcomp nPts (seedWordArr nPts (arrJ aJ) (arrJ bJ) FAData.g3Root)
        (pword nPts SJ (pinvs nPts SJ) FAData.g3H)) =
    Array.ofFn (n := 7) fun j => arrJ (C3J j) := by
  have hs : FAData.c3Words.size = 6 := by decide
  rw [seedWordArr_arrJ _ letters_ok.2.2.2.2, pword_arrJ SJ_arrs _ letters_ok.2.2.2.1, pcomp_arrJ]
  refine Array.ext (by simp [hs]) fun j h1 h2 => ?_
  have hj : j < 7 := by simpa using h2
  rw [Array.getElem_ofFn]
  rcases Nat.lt_or_ge j 6 with h | h
  · rw [Array.getElem_push_lt (by simpa [hs] using h), Array.getElem_map,
      ← getElem!_pos FAData.c3Words j (by rw [hs]; exact h), pword_arrJ SJ_arrs _ (letters_ok.2.2.1 j h)]
    unfold C3J
    rw [if_pos h]
  · have e : j = 6 := by omega
    subst e
    rw [Array.getElem_push, dif_neg (by simp [hs])]
    rfl

theorem ofFn_get8 {f : ℕ → Array ℕ} {j : ℕ} (hj : j < 8) :
    (Array.ofFn (n := 8) fun i => f i.val)[j]! = f j := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem ofFn_get7 {f : ℕ → Array ℕ} {j : ℕ} (hj : j < 7) :
    (Array.ofFn (n := 7) fun i => f i.val)[j]! = f j := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem all_size {k : ℕ} (f : ℕ → JH) :
    ((Array.ofFn (n := k) fun j => arrJ (f j)).map toTable).all (fun t => t.size == nPts) = true := by
  rw [Array.all_eq_true]
  intro i hi
  rw [Array.getElem_map, Array.getElem_ofFn, toTable_size, arrJ_size]
  exact beq_self_eq_true _

theorem small_ok : FAData.sWords.size = 4 ∧ FAData.sFixed.size = 4 ∧ FAData.c1Words.size = 8 ∧
    FAData.c3Words.size = 6 ∧ (FAData.g3Root.all fun l => l == 1 || l == 2) = true ∧
    rootT 0 = 0 ∧ rootT 1 = 1047 ∧ rootT 2 = 119497 ∧ rootT 3 = 0 := by decide +kernel

theorem threeChecks_ok : threeChecks (hnsData.orbit ()) = true := by
  obtain ⟨z1, z2, z3, z4, z5, r0, r1, r2, r3⟩ := small_ok
  obtain ⟨p0, p1, p2, p3⟩ := sizes_PT
  obtain ⟨hl1, hl2, hl3, hl4, -⟩ := letters_ok
  have hreg := (progRegs_arrJ _ _ _ prog_lt (initRegs_get rfl rfl).1 (initRegs_get rfl rfl).2).1
  have T0 := tree1 (t := 0) (by norm_num)
  have T1 := tree1 (t := 1) (by norm_num)
  have T2 := tree1 (t := 2) (by norm_num)
  have T3 := tree3
  rw [r0] at T0
  rw [r1] at T1
  rw [r2] at T2
  rw [r3] at T3
  unfold threeChecks
  try dsimp only
  rw [hns_n, natTab_alpha, natTab_beta, hreg, regs_get (k := 1) (by omega),
    regs_get (k := 2) (by omega), hS_eq, c3_eq, c1_eq]
  rw [pword_arrJ SJ_arrs _ (hl1 0 (by norm_num)), pword_arrJ SJ_arrs _ (hl1 2 (by norm_num))]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  refine ⟨trivial, strongOK_arrJ HNStrong.strong_parts.1 (by omega) words_lt, z1, z2, ?_, z3, z4, ?_,
    ?_, plettersOK_iff.2 hl4, z5, ?_, by simp, by simp, all_size _, all_size _, T0.1.ok, T1.1.ok,
    T2.1.ok, T3.1.ok, T0.2.1.trans p0, T1.2.1.trans p1, T2.2.1.trans p2, T3.2.trans p3, ?_⟩
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun k hk => ?_
    rw [pword_arrJ SJ_arrs _ (hl1 k hk), plettersOK_iff.2 (hl1 k hk), fix_S hk]
    rfl
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun j hj => ?_
    rw [plettersOK_iff.2 (hl2 j hj), ofFn_get8 (f := fun j => arrJ (C1J j)) hj, pcomp_arrJ,
      pcomp_arrJ, comm1 hj, peq_refl]
    rfl
  · exact CFSG.ONSchreier.allBelowN_iff.2 fun j hj => plettersOK_iff.2 (hl3 j hj)
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun j hj => ?_
    rw [ofFn_get7 (f := fun j => arrJ (C3J j)) hj, pcomp_arrJ, pcomp_arrJ, comm3 hj, peq_refl]
  · rw [List.all_eq_true]
    intro x hx
    rcases fixed0_in x hx with h | h | h
    · obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
      have := inTree_of T0.1 ((T0.2.2 x).1 ⟨i, hi, by rw [← e]; exact List.getD_eq_getElem _ _ hi⟩)
      rw [Bool.or_eq_true, Bool.or_eq_true]
      exact Or.inl (Or.inl this)
    · obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
      have := inTree_of T1.1 ((T1.2.2 x).1 ⟨i, hi, by rw [← e]; exact List.getD_eq_getElem _ _ hi⟩)
      rw [Bool.or_eq_true, Bool.or_eq_true]
      exact Or.inl (Or.inr this)
    · obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
      have := inTree_of T2.1 ((T2.2.2 x).1 ⟨i, hi, by rw [← e]; exact List.getD_eq_getElem _ _ hi⟩)
      rw [Bool.or_eq_true, Bool.or_eq_true]
      exact Or.inr this

end CertificateChecks.KernelSporSch.HNPt2109

end
