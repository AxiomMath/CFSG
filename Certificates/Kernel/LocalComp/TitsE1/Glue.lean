module

public import Certificates.Kernel.LocalComp.TitsE1.Checks
public import Certificates.Kernel.Sporadic.Tits.Words2264
public import CFSG.Certificates.Kernel.LocalCompPinSound
public import CFSG.Certificates.Kernel.MaxD2.Sound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
import Init.Data.Range.Basic
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.TitsE1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.PSL3Four.Native
open Certificates.CoreE1Perm CertificateChecks.KernelLC
open Certificates.FusD2Perm (powT wordT)

local notation "DT" => titsE1Data ()

theorem nB_eq (b : Bool) : nB b = !b := by cases b <;> rfl

theorem bor_eq (a b : Bool) : bIf(a, true, b) = (a || b) := by cases a <;> rfl

theorem bnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem exists_of_nB_allN {n : Nat} {f : Nat → Bool} (h : nB (allN n fun i => nB (f i)) = true) :
    ∃ i < n, f i = true := by
  rw [nB_eq, Bool.not_eq_true'] at h
  by_contra hc
  push Not at hc
  have : allN n (fun i => nB (f i)) = true :=
    PK.allN_iff.2 fun i hi => by rw [nB_eq, Bool.eq_false_iff.2 (hc i hi)]; rfl
  rw [this] at h
  exact absurd h (by decide)

theorem hn : szOK 1755 11 = true := by decide +kernel

theorem cId : Cn 1755 11 (pidn 1755 11) := pidn_canon hn

theorem canon3 : (∀ k < 13, Cn 1755 11 (W k)) ∧ (∀ k < 39, Cn 1755 11 (ZX k)) ∧
    ∀ k < 12, Cn 1755 11 (HC k) := by
  have h := ckCanon
  simp only [CFSG.KS.bAnd_iff] at h
  exact ⟨PK.allN_iff.1 h.1, PK.allN_iff.1 h.2.1, PK.allN_iff.1 h.2.2⟩

theorem cW {k : Nat} (hk : k < 13) : Cn 1755 11 (W k) := canon3.1 k hk

theorem cZX {k : Nat} (hk : k < 39) : Cn 1755 11 (ZX k) := canon3.2.1 k hk

theorem cHC {k : Nat} (hk : k < 12) : Cn 1755 11 (HC k) := canon3.2.2 k hk

theorem c0 : Cn 1755 11 (W 0) := cW (by norm_num)

theorem cX {i : Nat} (hi : i < 4) : Cn 1755 11 (W (i + 1)) := cW (by omega)

theorem hDn : (DT).n = 1755 := rfl

theorem zx_facts : (∀ k < 36, Nat.beq (pc (pw 1755 11 (W 0) (Nat.div (Nat.mod k 9) 3))
      (pw 1755 11 (W (Nat.add 1 (Nat.div k 9))) (Nat.mod k 3))) (ZX k) = true) ∧
    ∀ a < 3, Nat.beq (pw 1755 11 (W 0) a) (ZX (Nat.add 36 a)) = true := by
  have h := ckZX
  simp only [CFSG.KS.bAnd_iff] at h
  exact ⟨PK.allN_iff.1 h.1, PK.allN_iff.1 h.2⟩

theorem k_sng : TitsE1S.ng = 3 := by decide +kernel

theorem k_sN : TitsE1S.N = 27 := by decide +kernel

theorem cSG {k : Nat} (hk : k < 3) : Cn 1755 11 (TitsE1S.G k) := by
  have h := TitsE1S.ok
  unfold CFSG.KC.BfsPin.bfsK at h
  simp only [CFSG.KS.bAnd_iff] at h
  exact PK.allN_iff.1 h.2.1 k (by rw [k_sng]; exact hk)

theorem cT {i : Nat} (hi : i < 27) : Cn 1755 11 (TitsE1S.T i) := by
  have h := TitsE1S.ok
  unfold CFSG.KC.BfsPin.bfsK at h
  simp only [CFSG.KS.bAnd_iff] at h
  exact PK.allN_iff.1 h.2.2.1 i (by rw [k_sN]; exact hi)

theorem gs_size : (gsT DT).size = 2 := rfl

theorem gs_get : ∀ j < 2, (gsT DT)[j]! = unpack 1755 11 (GA j) := by
  intro j hj
  have hd := PK.allN_iff.1 CertificateChecks.KernelSpor.Tits2264.dOK j hj
  have hg := (band_e (PK.allN_iff.1 ckGens j hj)).1
  have e : (gsT DT)[j]! = CFSG.Sporadic.Schreier.Tits.titsDArr j := by
    interval_cases j <;> simp [gsT, titsE1Data]
  rw [e, CertificateChecks.KernelSpor.Tits2264.titsDArr_eq hj, Nat.eq_of_beq_eq_true hd,
    Nat.eq_of_beq_eq_true hg]

theorem gperm : allN 2 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (GA j) (GI j)) = true :=
  PK.allN_iff.2 fun j hj => (band_e (PK.allN_iff.1 ckGens j hj)).2

theorem wT_eq {w : List Int} {r : Nat} (h : wordEqK 1755 11 (mask 11) IDN GA GI 2 w r = true) :
    wT DT w = unpack 1755 11 r :=
  wordT_u (S := gsT DT) ⟨gs_size, gs_get⟩ gperm h

theorem zT_eq : zT DT = unpack 1755 11 (W 0) := by
  have h := PK.allN_iff.1 ckWords0 0 (by norm_num)
  have e : wd 0 = (DT).zW := by simp [wd]
  rw [e] at h
  exact wT_eq h

theorem xT_eq {i : Nat} (hi : i < 4) : xT DT i = unpack 1755 11 (W (i + 1)) := by
  have h := PK.allN_iff.1 ckWords0 (i + 1) (by omega)
  have e : wd (i + 1) = (DT).xWs.getD i [] := by
    unfold wd
    rw [if_neg (by omega), if_pos (by omega)]
    rfl
  rw [e] at h
  exact wT_eq h

theorem sW_len : (DT).sW.length = 3 := rfl

theorem sg_get {k : Nat} (hk : k < 3) : (sGens DT)[k]! = unpack 1755 11 (TitsE1S.G k) := by
  unfold sGens
  rw [map_get _ (by rw [sW_len]; exact hk)]
  have h := PK.allN_iff.1 ckS k hk
  have e : (DT).sW.getD k [] = (DT).sW[k]! := by
    rw [List.getD_eq_getElem?_getD, getElem!_pos (DT).sW k (by rw [sW_len]; exact hk),
      List.getElem?_eq_getElem (by rw [sW_len]; exact hk), Option.getD_some]
  rw [e] at h
  exact wT_eq h

theorem sg_size : (sGens DT).size = 3 := rfl

theorem s_pin : enumOK 1755 (sGens DT) (enumBFS 1755 (sGens DT) 27) = true ∧
    (enumBFS 1755 (sGens DT) 27).tabs =
      Array.ofFn (n := TitsE1S.N) fun i => unpack 1755 11 (TitsE1S.T i.val) := by
  have hs : (sGens DT).size = TitsE1S.ng := by rw [k_sng]; exact sg_size
  have hg : ∀ k < TitsE1S.ng, (sGens DT)[k]! = unpack 1755 11 (TitsE1S.G k) := by
    intro k hk
    rw [k_sng] at hk
    exact sg_get hk
  exact CFSG.KC.LocalComp.Pin.enumBFS_of_bfsK hs hg TitsE1S.ok (by rw [k_sN])

theorem s_tabs : (sEnum DT).tabs =
    Array.ofFn (n := TitsE1S.N) fun i => unpack 1755 11 (TitsE1S.T i.val) := s_pin.2

theorem tabs_get {i : Nat} (hi : i < (sEnum DT).tabs.size) :
    (sEnum DT).tabs[i] = unpack 1755 11 (TitsE1S.T i) := by
  simp [s_tabs]

theorem tabs_size : (sEnum DT).tabs.size = 27 := by
  rw [s_tabs, Array.size_ofFn, k_sN]

theorem mem_tabs {p : Nat} (h : ∃ i < 27, TitsE1S.T i = p) :
    (sEnum DT).tabs.contains (unpack 1755 11 p) = true := by
  obtain ⟨i, hi, rfl⟩ := h
  rw [Array.contains_eq_any_beq, Array.any_eq_true]
  exact ⟨i, by rw [tabs_size]; exact hi, by rw [tabs_get]; simp⟩

theorem tabs_all {f : Tab → Bool}
    (h : ∀ i < 27, f (unpack 1755 11 (TitsE1S.T i)) = true) : (sEnum DT).tabs.all f = true := by
  rw [Array.all_eq_true]
  intro i hi
  rw [tabs_get]
  exact h i (by rw [tabs_size] at hi; exact hi)

theorem eqI {p : Nat} (hp : Cn 1755 11 p) :
    (unpack 1755 11 p == idTab 1755) = Nat.beq p IDN := by
  rw [id_u hn, eq_u hp cId]
  rfl

theorem pw_eq {p : Nat} (hp : Cn 1755 11 p) (e : Nat) :
    powT 1755 (unpack 1755 11 p) e = unpack 1755 11 (pw 1755 11 p e) := powT_u hn hp e

theorem cpw {p : Nat} (hp : Cn 1755 11 p) (e : Nat) : Cn 1755 11 (pw 1755 11 p e) :=
  pw_canon hn hp e

theorem pc_eq {p q : Nat} (hp : Cn 1755 11 p) (hq : Cn 1755 11 q) :
    comp 1755 (unpack 1755 11 p) (unpack 1755 11 q) = unpack 1755 11 (pc p q) := comp_u hp hq

theorem cpc {p q : Nat} (hp : Cn 1755 11 p) (hq : Cn 1755 11 q) : Cn 1755 11 (pc p q) := cc hp hq

theorem zpow_eq {a : Nat} (ha : a < 3) : pw 1755 11 (W 0) a = ZX (36 + a) := by
  exact Nat.eq_of_beq_eq_true (zx_facts.2 a ha)

theorem zx_eq {i a b : Nat} (hi : i < 4) (ha : a < 3) (hb : b < 3) :
    zx DT i a b = unpack 1755 11 (ZX (9 * i + 3 * a + b)) := by
  have h := zx_facts.1 (9 * i + 3 * a + b) (by omega)
  have e1 : Nat.div (Nat.mod (9 * i + 3 * a + b) 9) 3 = a := by
    change (9 * i + 3 * a + b) % 9 / 3 = a
    omega
  have e2 : Nat.add 1 (Nat.div (9 * i + 3 * a + b) 9) = i + 1 := by
    change 1 + (9 * i + 3 * a + b) / 9 = i + 1
    omega
  have e3 : Nat.mod (9 * i + 3 * a + b) 3 = b := by
    change (9 * i + 3 * a + b) % 3 = b
    omega
  rw [e1, e2, e3] at h
  unfold zx
  rw [hDn, zT_eq, xT_eq hi, pw_eq c0, pw_eq (cX hi), pc_eq (cpw c0 a) (cpw (cX hi) b),
    Nat.eq_of_beq_eq_true h]

theorem sGens_eq : sGens DT = #[unpack 1755 11 (TitsE1S.G 0), unpack 1755 11 (TitsE1S.G 1),
    unpack 1755 11 (TitsE1S.G 2)] := by
  apply Array.ext
  · rw [sg_size]
    rfl
  · intro k h1 h2
    rw [sg_size] at h1
    rw [← getElem!_pos (sGens DT) k (by rw [sg_size]; exact h1), sg_get h1]
    interval_cases k <;> rfl

theorem central_eq {p : Nat} (hp : Cn 1755 11 p) : central DT (unpack 1755 11 p) = cenP p := by
  unfold central
  rw [sGens_eq, hDn]
  simp only [Array.all_toList.symm, List.all_cons, List.all_nil, Bool.and_true]
  have s0 := cSG (k := 0) (by norm_num)
  have s1 := cSG (k := 1) (by norm_num)
  have s2 := cSG (k := 2) (by norm_num)
  rw [pc_eq hp s0, pc_eq s0 hp, pc_eq hp s1, pc_eq s1 hp, pc_eq hp s2, pc_eq s2 hp,
    eq_u (cpc hp s0) (cpc s0 hp), eq_u (cpc hp s1) (cpc s1 hp), eq_u (cpc hp s2) (cpc s2 hp)]
  unfold cenP
  rw [bnd_eq, bnd_eq]

theorem inZ_eq {p : Nat} (hp : Cn 1755 11 p) : inZ DT (unpack 1755 11 p) = inZP p := by
  unfold inZ anyBelow
  rw [zT_eq, hDn]
  have e : List.range 3 = [0, 1, 2] := rfl
  rw [e]
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [pw_eq c0, pw_eq c0, pw_eq c0,
    zpow_eq (by norm_num), zpow_eq (by norm_num), zpow_eq (by norm_num),
    eq_u hp (cZX (by norm_num)), eq_u hp (cZX (by norm_num)), eq_u hp (cZX (by norm_num))]
  unfold inZP
  rw [bor_eq, bor_eq]

theorem inE_of {i p : Nat} (hi : i < 4) (h : inEP i p = true) : inE DT i (unpack 1755 11 p) = true := by
  obtain ⟨k, hk, hpk⟩ := exists_of_nB_allN h
  have e : p = ZX (9 * i + 3 * (k / 3) + k % 3) := by
    rw [Nat.eq_of_beq_eq_true hpk]
    congr 1
    change 9 * i + k = _
    omega
  unfold inE
  rw [anyBelow_iff]
  refine ⟨k / 3, by omega, ?_⟩
  rw [anyBelow_iff]
  refine ⟨k % 3, by omega, ?_⟩
  rw [zx_eq hi (by omega) (by omega), e]
  simp

theorem k_gens : gensOK DT = true := by
  unfold gensOK
  rw [allBelow_iff']
  intro j hj
  have hp := PK.allN_iff.1 gperm j hj
  have hgi : (giT DT)[j]! = unpack 1755 11 (GI j) := by
    unfold giT
    rw [getElem!_pos _ j (by simpa [gs_size] using hj), Array.getElem_map,
      ← getElem!_pos (gsT DT) j (by rw [gs_size]; exact hj), gs_get j hj]
    exact inv_u hp
  rw [hgi, gs_get j hj, hDn, inv_comp hp, size_u]
  simp

theorem k_sOK : sOK DT = true := by
  have s1 := cSG (k := 1) (by norm_num)
  have s2 := cSG (k := 2) (by norm_num)
  unfold sOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨s_pin.1, tabs_size⟩, ?_⟩
  rw [Array.any_eq_true]
  refine ⟨1, by rw [sg_size]; norm_num, ?_⟩
  rw [Array.any_eq_true]
  refine ⟨2, by rw [sg_size]; norm_num, ?_⟩
  rw [← getElem!_pos (sGens DT) 1 (by rw [sg_size]; norm_num),
    ← getElem!_pos (sGens DT) 2 (by rw [sg_size]; norm_num), sg_get (by norm_num),
    sg_get (by norm_num), hDn, pc_eq s1 s2, pc_eq s2 s1, eq_u (cpc s1 s2) (cpc s2 s1)]
  have h := ckNC
  rw [nB_eq] at h
  exact h

theorem k_zOK : zOK DT = true := by
  have hz := ckZ
  rw [bnd_eq, bnd_eq, bnd_eq] at hz
  simp only [Bool.and_eq_true] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  unfold zOK
  rw [hDn]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [zT_eq]
    obtain ⟨i, hi, e⟩ := exists_of_nB_allN h4
    exact mem_tabs ⟨i, hi, Nat.eq_of_beq_eq_true e⟩
  · rw [zT_eq, eqI c0]
    rw [nB_eq] at h1
    exact h1
  · rw [zT_eq, pw_eq c0, eqI (cpw c0 3)]
    exact h2
  · rw [zT_eq, central_eq c0]
    exact h3
  · refine tabs_all fun i hi => ?_
    have h := PK.allN_iff.1 ckZall i hi
    rw [bor_eq, nB_eq] at h
    rw [central_eq (cT hi), inZ_eq (cT hi)]
    exact h

theorem xWs_len : (DT).xWs.length = 4 := rfl

theorem k_xOK : xOK DT = true := by
  unfold xOK
  rw [hDn]
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [xWs_len, allBelow_iff']
    intro i hi
    have h := PK.allN_iff.1 ckX i hi
    rw [bnd_eq, bnd_eq, bnd_eq] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have e : Nat.add i 1 = i + 1 := rfl
    rw [e] at h1 h2 h3 h4
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [xT_eq hi]
      obtain ⟨t, ht, et⟩ := exists_of_nB_allN h1
      exact mem_tabs ⟨t, ht, Nat.eq_of_beq_eq_true et⟩
    · rw [xT_eq hi, pw_eq (cX hi), eqI (cpw (cX hi) 3)]
      exact h2
    · rw [xT_eq hi, zT_eq, pc_eq (cX hi) c0, pc_eq c0 (cX hi), eq_u (cpc (cX hi) c0) (cpc c0 (cX hi))]
      exact h3
    · rw [xT_eq hi, inZ_eq (cX hi)]
      rw [nB_eq] at h4
      exact h4
  · refine tabs_all fun t ht => ?_
    rw [xWs_len, anyBelow_iff]
    obtain ⟨i, hi, e⟩ := exists_of_nB_allN (PK.allN_iff.1 ckXall t ht)
    exact ⟨i, hi, inE_of hi e⟩

theorem k_len : ((DT).es.length == (DT).xWs.length) = true := rfl

theorem ent_shape : ∀ i < 4, ((DT).es.getD i default).move = true ∧ ((DT).es.getD i default).m = 4 ∧
    ((DT).es.getD i default).hW = [1, 2] ∧ ((DT).es.getD i default).gWs.length = 2 ∧
    ((DT).es.getD i default).nd.length = 2 ∧ ∀ j < 2,
      (((DT).es.getD i default).nd.getD j default).two = false ∧
      (((DT).es.getD i default).nd.getD j default).a < 3 ∧
      (((DT).es.getD i default).nd.getD j default).b < 3 := by
  decide +kernel

theorem gT_get {i j : Nat} (hi : i < 4) (hj : j < 2) :
    (gT DT ((DT).es.getD i default))[j]! = unpack 1755 11 (W (5 + 2 * i + j)) := by
  obtain ⟨-, -, -, hl, -⟩ := ent_shape i hi
  unfold gT
  rw [map_get _ (by rw [hl]; exact hj)]
  have h := PK.allN_iff.1 ckWords1 (2 * i + j) (by omega)
  have e1 : Nat.add 5 (2 * i + j) = 5 + 2 * i + j := by
    change 5 + (2 * i + j) = _
    omega
  have e2 : wd (5 + 2 * i + j) = ((DT).es.getD i default).gWs[j]! := by
    unfold wd
    rw [if_neg (by omega), if_neg (by omega)]
    have e3 : (5 + 2 * i + j - 5) / 2 = i := by omega
    have e4 : (5 + 2 * i + j - 5) % 2 = j := by omega
    rw [e3, e4, List.getD_eq_getElem?_getD,
      getElem!_pos ((DT).es.getD i default).gWs j (by rw [hl]; exact hj),
      List.getElem?_eq_getElem (by rw [hl]; exact hj), Option.getD_some]
  rw [e1, e2] at h
  exact wT_eq h

theorem gT_size {i : Nat} (hi : i < 4) : (gT DT ((DT).es.getD i default)).size = 2 := by
  obtain ⟨-, -, -, hl, -⟩ := ent_shape i hi
  simp only [gT, List.size_toArray, List.length_map, hl]

theorem gperm_i {i : Nat} (hi : i < 4) : ∀ j < 2, permOK 1755 11 (mask 11) (1755 * 11)
    (W (5 + 2 * i + j)) (WI (2 * i + j)) = true := by
  intro j hj
  have h := PK.allN_iff.1 ckGI (2 * i + j) (by omega)
  have e1 : Nat.add 5 (2 * i + j) = 5 + 2 * i + j := by
    change 5 + (2 * i + j) = _
    omega
  rw [e1] at h
  exact h

theorem gTi_get {i j : Nat} (hi : i < 4) (hj : j < 2) :
    (gTi DT ((DT).es.getD i default))[j]! = unpack 1755 11 (WI (2 * i + j)) := by
  unfold gTi
  rw [getElem!_pos _ j (by rw [Array.size_map, gT_size hi]; exact hj), Array.getElem_map,
    ← getElem!_pos _ j (by rw [gT_size hi]; exact hj), gT_get hi hj]
  exact inv_u (gperm_i hi j hj)

theorem nrm_ok {i j : Nat} (hi : i < 4) (hj : j < 2) :
    nrmOK DT i (gT DT ((DT).es.getD i default))[j]! (((DT).es.getD i default).nd.getD j default) =
      true := by
  obtain ⟨-, -, -, -, -, hnd⟩ := ent_shape i hi
  obtain ⟨h2, ha, hb⟩ := hnd j hj
  set f := ((DT).es.getD i default).nd.getD j default with hf
  have hE := (band_e (PK.allN_iff.1 ckEnt i hi)).1
  have hJ := PK.allN_iff.1 hE j hj
  rw [PK.strictB_eq, ← hf] at hJ
  have e1 : Nat.add (Nat.add (Nat.mul 9 i) (Nat.mul 3 f.a)) f.b = 9 * i + 3 * f.a + f.b := rfl
  have e2 : Nat.add (Nat.add 5 (Nat.mul 2 i)) j = 5 + 2 * i + j := rfl
  rw [e1, e2, bnd_eq, nB_eq] at hJ
  have cu := cZX (k := 9 * i + 3 * f.a + f.b) (by omega)
  have cg := cW (k := 5 + 2 * i + j) (by omega)
  unfold nrmOK
  rw [hDn, if_neg (by rw [h2]; decide), gT_get hi hj, zx_eq hi ha hb, eqI cu, pw_eq cu,
    pc_eq cg cu, pc_eq (cpw cu _) cg, eq_u (cpc cg cu) (cpc (cpw cu _) cg)]
  exact hJ

theorem move_ok {i : Nat} (hi : i < 4) : moveOK DT ((DT).es.getD i default) = true := by
  obtain ⟨-, hm, hw, hl, -⟩ := ent_shape i hi
  have hC := PK.allN_iff.1 ckHC i hi
  have e3 : Nat.mul 3 i = 3 * i := rfl
  have e5 : ∀ j, Nat.add (Nat.add 5 (Nat.mul 2 i)) j = 5 + 2 * i + j := fun _ => rfl
  have e6 : ∀ j, Nat.add (Nat.mul 2 i) j = 2 * i + j := fun _ => rfl
  have e7 : Nat.add (3 * i) 1 = 3 * i + 1 := rfl
  have e8 : Nat.add (3 * i) 2 = 3 * i + 2 := rfl
  simp only [e3, e5, e6, e7, e8] at hC
  obtain ⟨hw1, hC⟩ := band_e hC
  obtain ⟨hp, hc⟩ := band_e hC
  have hh : wordT 1755 (gT DT ((DT).es.getD i default)) (gTi DT ((DT).es.getD i default))
      ((DT).es.getD i default).hW = unpack 1755 11 (HC (3 * i)) := by
    rw [hw]
    exact wordT_u (k := 2) ⟨gT_size hi, fun j hj => gT_get hi hj⟩
      (PK.allN_iff.2 (gperm_i hi)) hw1
  have hE := (band_e (PK.allN_iff.1 ckEnt i hi)).2
  rw [e3, e8] at hE
  obtain ⟨hne, hpow⟩ := band_e hE
  rw [nB_eq] at hne
  have c0 := cHC (k := 3 * i) (by omega)
  have c1 := cHC (k := 3 * i + 1) (by omega)
  have c2 := cHC (k := 3 * i + 2) (by omega)
  have cz := cW (k := 0) (by norm_num)
  have hcv : comp 1755 (zT DT) (comp 1755 (comp 1755 (unpack 1755 11 (HC (3 * i))) (zT DT))
      (unpack 1755 11 (HC (3 * i + 1)))) = unpack 1755 11 (HC (3 * i + 2)) := by
    rw [zT_eq, pc_eq c0 cz, pc_eq (cpc c0 cz) c1, pc_eq cz (cpc (cpc c0 cz) c1),
      ← Nat.eq_of_beq_eq_true hc]
  unfold moveOK
  simp only
  rw [hDn, hh, inv_u hp, hcv, size_u, inv_comp hp, eqI c2, hm, pw_eq c2, eqI (cpw c2 4)]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
  refine ⟨⟨hne, hpow⟩, ?_⟩
  decide

theorem k_ent {i : Nat} (hi : i < 4) : entryOK DT i ((DT).es.getD i default) = true := by
  obtain ⟨hmv, -, -, hl, hnl, -⟩ := ent_shape i hi
  unfold entryOK
  rw [hDn, if_pos hmv, move_ok hi, hl, hnl, gT_size hi]
  simp only [Bool.and_true, beq_self_eq_true, Bool.and_eq_true]
  rw [allBelow_iff']
  intro j hj
  rw [gTi_get hi hj, gT_get hi hj, size_u, inv_comp (gperm_i hi j hj), ← gT_get hi hj, nrm_ok hi hj]
  simp

theorem tits_e1 : check DT = true := by
  unfold check
  rw [k_gens, k_sOK, k_zOK, k_xOK, k_len]
  simp only [Bool.true_and]
  rw [allBelow_iff']
  intro i hi
  have e : (DT).es.length = 4 := rfl
  rw [e] at hi
  exact k_ent hi

end CertificateChecks.KernelLC.TitsE1

end
