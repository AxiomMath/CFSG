
module

public import Certificates.Kernel.SporSch.Ru.C2253
public import Certificates.Kernel.SporSch.Ru.RFacts
public import CFSG.Certificates.Kernel.SporSch.RuImgSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuCe

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuLines CertificateChecks.KernelSporSch.RuG CFSG.KC.Misc.RuInv

theorem sb_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem eqA_unpack_self (n w P : Nat) : eqA n (unpack n w P) (unpack n w P) = true :=
  eqK_sound (Nat.beq_refl P)

theorem field4060_get {f j : Nat} (hj : j < (ruLines4060.getD f (0, 0)).2) :
    (ruField4060 f)[j]! = ruArr4060 ((ruLines4060.getD f (0, 0)).1 + j) := by
  rw [ruField4060, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem f4060 {f j : Nat} (s l L : Nat) (hs : ruLines4060.getD f (0, 0) = (s, l)) (hj : j < l)
    (hsj : s + j = L) (hL : L < 45) : (ruField4060 f)[j]! = unpack 4060 12 (RuT4060.L L) := by
  have hj' : j < (ruLines4060.getD f (0, 0)).2 := by
    rw [hs]
    exact hj
  have h1 : (ruLines4060.getD f (0, 0)).1 = s := by rw [hs]
  rw [field4060_get hj', h1, hsj]
  exact row4060 hL

theorem fld4060 {f j L : Nat} (s l : Nat) {P : Nat} {a : Array Nat}
    (hs : ruLines4060.getD f (0, 0) = (s, l)) (hj : j < l) (hsj : s + j = L) (hL : L < 45)
    (ha : a = unpack 4060 12 P) (hb : Nat.beq (RuT4060.L L) P = true) :
    eqA 4060 (ruField4060 f)[j]! a = true := by
  rw [f4060 s l _ hs hj hsj hL, ha, Nat.eq_of_beq_eq_true hb]
  exact eqA_unpack_self _ _ _

theorem f1920 {f j : Nat} (s l L : Nat) (hs : ruLines1920.getD f (0, 0) = (s, l)) (hj : j < l)
    (hsj : s + j = L) (hL : L < 41) : (ruField1920 f)[j]! = unpack 1920 11 (RuT1920.L L) := by
  have hj' : j < (ruLines1920.getD f (0, 0)).2 := by
    rw [hs]
    exact hj
  have h1 : (ruLines1920.getD f (0, 0)).1 = s := by rw [hs]
  rw [RuR.field_get hj', h1, hsj]
  exact row1920 hL

theorem word_get {D : List (List Int)} {S SI : Array (Array Nat)} {i : Nat} (hi : i < D.length)
    {P : Nat} (h : wordA 4060 S SI (D.getD i []) = unpack 4060 12 P) :
    (D.map (wordA 4060 S SI)).toArray[i]! = unpack 4060 12 P := by
  rw [← h, getElem!_pos _ i (by simpa using hi)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem kok_spec {i : Nat} (hi : i < 8) :
    wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 Ns0 Ns1) (gen2 Ns0I Ns1I) 2
      (dword ruKWords 0 i) (KG i) = true ∧ canonK 4060 12 (mask 12) (4060 * 12) (KG i) = true := by
  have h := KC.all i hi
  unfold kok at h
  exact (bAnd_iff _ _).1 h

theorem jok_spec {i : Nat} (hi : i < 6) :
    wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 C0 C1) (gen2 C0I C1I) 2
      (dword ruJWords 0 i) (JG i) = true ∧ canonK 4060 12 (mask 12) (4060 * 12) (JG i) = true := by
  have h := JC.all i hi
  unfold jok at h
  exact (bAnd_iff _ _).1 h

theorem rok_spec {i : Nat} (hi : i < 5) :
    wordEqK 4060 12 (mask 12) (pidn 4060 12) SG SGI 4 (dword ruRWords 0 i) (RG i) = true ∧
      canonK 4060 12 (mask 12) (4060 * 12) (RG i) = true := by
  have h := RC.all i hi
  unfold rok at h
  exact (bAnd_iff _ _).1 h

theorem kg_eq {i : Nat} (hi : i < 8) : ruKGensA[i]! = unpack 4060 12 (KG i) := by
  have h := (wordEqK_sound (binds2 ns0_eq ns1_eq) (perms2 pNs0 pNs1) (kok_spec hi).1).1
  rw [← invs2, dword_zero] at h
  exact word_get (by simp [ruKWords]; omega) h

theorem jg_eq {i : Nat} (hi : i < 6) : ruJGensA[i]! = unpack 4060 12 (JG i) := by
  have h := (wordEqK_sound (binds2 c0_eq c1_eq) (perms2 pC0 pC1) (jok_spec hi).1).1
  rw [← invs2, dword_zero] at h
  exact word_get (by simp [ruJWords]; omega) h

theorem sgBinds : ruSGensA.size = 4 ∧ ∀ j < 4, ruSGensA[j]! = unpack 4060 12 (SG j) :=
  ⟨by simp [ruSGensA, ruSWords], fun _ hj => sg_eq hj⟩

theorem rg_eq {i : Nat} (hi : i < 5) : ruRGensA[i]! = unpack 4060 12 (RG i) := by
  have h := (wordEqK_sound sgBinds pSG (rok_spec hi).1).1
  rw [dword_zero] at h
  exact word_get (by simp [ruRWords]; omega) h

theorem fLt' : ∀ i < 1920, pg 12 (mask 12) RuF.F i < 4060 :=
  fun i hi => by simpa [Nat.blt_eq] using allN_spec RuF.fLt i hi

theorem yLt' : ∀ i < 80, pg 12 (mask 12) Y i < 4060 :=
  fun i hi => by simpa [Nat.blt_eq] using allN_spec yLt i hi

theorem y_eq : ruY = unpack 80 12 Y := by
  have h := hexPackK_sound (by norm_num) (by norm_num) yK
  rw [← RuPts.eq] at h
  apply Array.ext
  · simp [ruY, ruPtList, ruPtsOffsets, unpack]
  · intro i h1 h2
    have hi : i < 80 := by simpa [unpack] using h2
    simp only [ruY, ruPtList, unpack, Array.getElem_ofFn]
    have e := h i hi
    have e3 : 3 * (10040 + i) = 3 * ((ruPtsOffsets.getD 8 (0, 0)).1 + i) := rfl
    rw [e3] at e
    exact e

theorem ypos_eq : ruYPos = unpack 4060 12 YPOS := by
  rw [ruYPos, y_eq]
  exact posK_sound posY

theorem resF_eq {G L : Nat} (hG : canonK 4060 12 (mask 12) (4060 * 12) G = true)
    (h : resF G L = true) :
    resA ruF ruFPos (unpack 4060 12 G) = unpack 1920 11 (RuT1920.L L) := by
  rw [RuF.f_eq, RuF.fpos_eq]
  exact resK_sound fLt' hG h

theorem res_tuple {f s l j : Nat} (hs : ruLines1920.getD f (0, 0) = (s, l)) (hj : j < l)
    (hL : s + j < 41) {G : Nat} {a : Array Nat} (ha : a = unpack 4060 12 G)
    (hG : canonK 4060 12 (mask 12) (4060 * 12) G = true) (h : resF G (s + j) = true) :
    eqA 1920 (ruField1920 f)[j]! (resA ruF ruFPos a) = true := by
  rw [f1920 s l (s + j) hs hj rfl hL, ha, resF_eq hG h]
  exact eqA_unpack_self _ _ _

theorem field80_get {j : Nat} (hj : j < 8) : ruField80[j]! = unpack 80 7 (RuT80.L j) := by
  rw [ruField80, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact row80 hj

theorem res80_eq {G L : Nat} (hG : canonK 4060 12 (mask 12) (4060 * 12) G = true)
    (h : resK 80 12 7 Y YPOS G (RuT80.L L) = true) :
    resA ruY ruYPos (unpack 4060 12 G) = unpack 80 7 (RuT80.L L) := by
  rw [y_eq, ypos_eq]
  exact resK_sound yLt' hG h

theorem ic_h {i g : Nat} (hi : i < 6) (hg : g < 2) :
    sortImgK 4060 12 (gen2 C0 C1 g) (ruCBlockList i) (ruCBlockList (ruCBlockPerms.getD g #[])[i]!) =
      true := by
  have hj : 2 * i + g < 12 := by omega
  have h := IC.all (2 * i + g) hj
  unfold imgCj at h
  rw [sb_eq, sb_eq] at h
  have e1 : Nat.div (2 * i + g) 2 = i := by
    change (2 * i + g) / 2 = i
    omega
  have e2 : Nat.mod (2 * i + g) 2 = g := by
    change (2 * i + g) % 2 = g
    omega
  rw [e1, e2] at h
  exact h

theorem in_h {i g : Nat} (hi : i < 7) (hg : g < 2) :
    sortImgK 4060 12 (gen2 Ns0 Ns1 g) (ruNBlockList i) (ruNBlockList (ruNBlockPerms.getD g #[])[i]!) =
      true := by
  have hj : 2 * i + g < 14 := by omega
  have h := IN.all (2 * i + g) hj
  unfold imgNj at h
  rw [sb_eq, sb_eq] at h
  have e1 : Nat.div (2 * i + g) 2 = i := by
    change (2 * i + g) / 2 = i
    omega
  have e2 : Nat.mod (2 * i + g) 2 = g := by
    change (2 * i + g) % 2 = g
    omega
  rw [e1, e2] at h
  exact h

theorem ij_h {i k : Nat} (hi : i < 6) (hk : k < 6) :
    sortImgK 4060 12 (JG k) (ruCBlockList i) (ruCBlockList i) = true := by
  have hj : 6 * i + k < 36 := by omega
  have h := IJ.all (6 * i + k) hj
  unfold imgJj at h
  rw [sb_eq, sb_eq] at h
  have e1 : Nat.div (6 * i + k) 6 = i := by
    change (6 * i + k) / 6 = i
    omega
  have e2 : Nat.mod (6 * i + k) 6 = k := by
    change (6 * i + k) % 6 = k
    omega
  rw [e1, e2] at h
  exact h

theorem ik_h {i k : Nat} (hi : i < 7) (hk : k < 8) :
    sortImgK 4060 12 (KG k) (ruNBlockList i) (ruNBlockList i) = true := by
  have hj : 8 * i + k < 56 := by omega
  have h := IK.all (8 * i + k) hj
  unfold imgKj at h
  rw [sb_eq, sb_eq] at h
  have e1 : Nat.div (8 * i + k) 8 = i := by
    change (8 * i + k) / 8 = i
    omega
  have e2 : Nat.mod (8 * i + k) 8 = k := by
    change (8 * i + k) % 8 = k
    omega
  rw [e1, e2] at h
  exact h

theorem nodup_of_heads {m : Nat} {B : Nat → List Nat}
    (h : incNL ((List.range m).map fun i => (B i).headD 0) = true) :
    ((List.range m).map B).Nodup := by
  refine List.Nodup.of_map (fun l => l.headD 0) ?_
  rw [List.map_map]
  exact (incNL_spec h).imp Nat.ne_of_lt

theorem facts : (eqA 4060 (ruField4060 1)[0]! ruC0A = true ∧
      eqA 4060 (ruField4060 1)[1]! ruC1A = true ∧
      eqA 4060 (ruField4060 2)[0]! ruNs0A = true ∧ eqA 4060 (ruField4060 2)[1]! ruNs1A = true ∧
      eqA 4060 (ruField4060 3)[0]! ruC0A = true ∧ eqA 4060 (ruField4060 3)[1]! ruC1A = true ∧
      eqA 4060 (ruField4060 3)[2]! ruNs0A = true ∧ eqA 4060 (ruField4060 3)[3]! ruNs1A = true ∧
      eqA 1920 (ruField1920 0)[0]! (resA ruF ruFPos ruC0A) = true ∧
      eqA 1920 (ruField1920 0)[1]! (resA ruF ruFPos ruC1A) = true ∧
      (∀ i < 4, eqA 1920 (ruField1920 1)[i]! (resA ruF ruFPos ruSGensA[i]!) = true) ∧
      (∀ i < 8, eqA 1920 (ruField1920 2)[i]! (resA ruF ruFPos ruKGensA[i]!) = true) ∧
      (∀ i < 6, eqA 1920 (ruField1920 3)[i]! (resA ruF ruFPos ruJGensA[i]!) = true) ∧
      (∀ i < 5, eqA 1920 (ruField1920 4)[i]! (resA ruF ruFPos ruRGensA[i]!) = true) ∧
      eqA 80 ruField80[0]! (resA ruY ruYPos ruC0A) = true ∧
      eqA 80 ruField80[1]! (resA ruY ruYPos ruC1A) = true)
    ∧ (eqA 4060 ruZA (idA 4060) = false ∧ eqA 4060 (compA 4060 ruZA ruZA) (idA 4060) = true ∧
      eqA 4060 (compA 4060 ruZA ruC0A) (compA 4060 ruC0A ruZA) = true ∧
      eqA 4060 (compA 4060 ruZA ruC1A) (compA 4060 ruC1A ruZA) = true ∧
      (∀ i < 80, ruZA[ruY[i]!]! = ruY[i]!))
    ∧ ((∀ i < 6, ∀ g < 2, imgSorted #[ruC0A, ruC1A][g]! (ruCBlockList i) =
        ruCBlockList (ruCBlockPerms.getD g #[])[i]!) ∧
      (∀ i < 7, ∀ g < 2, imgSorted #[ruNs0A, ruNs1A][g]! (ruNBlockList i) =
        ruNBlockList (ruNBlockPerms.getD g #[])[i]!) ∧
      (∀ i < 6, ∀ j < 6, imgSorted ruJGensA[j]! (ruCBlockList i) = ruCBlockList i) ∧
      (∀ i < 7, ∀ j < 8, imgSorted ruKGensA[j]! (ruNBlockList i) = ruNBlockList i) ∧
      (∀ i < 6, (ruCBlockList i).Pairwise (· < ·) ∧ ∀ x ∈ ruCBlockList i, x < 4060) ∧
      (∀ i < 7, (ruNBlockList i).Pairwise (· < ·) ∧ ∀ x ∈ ruNBlockList i, x < 4060) ∧
      ((List.range 6).map ruCBlockList).Nodup ∧ ((List.range 7).map ruNBlockList).Nodup ∧
      (∀ g < 2, ∀ i < 6, (ruCBlockPerms.getD g #[])[i]! < 6) ∧
      (∀ g < 2, ∀ i < 7, (ruNBlockPerms.getD g #[])[i]! < 7) ∧
      ruCBlockStrong[0]! = ruCBlockPerms.getD 0 #[] ∧ ruCBlockStrong[1]! = ruCBlockPerms.getD 1 #[] ∧
      ruNBlockStrong[0]! = ruNBlockPerms.getD 0 #[] ∧
      ruNBlockStrong[1]! = ruNBlockPerms.getD 1 #[]) := by
  refine ⟨⟨fld4060 (f := 1) (j := 0) (L := 2) 2 7 rfl (by omega) rfl (by omega) c0_eq l2,
    fld4060 (f := 1) (j := 1) (L := 3) 2 7 rfl (by omega) rfl (by omega) c1_eq l3,
    fld4060 (f := 2) (j := 0) (L := 9) 9 6 rfl (by omega) rfl (by omega) ns0_eq l9,
    fld4060 (f := 2) (j := 1) (L := 10) 9 6 rfl (by omega) rfl (by omega) ns1_eq l10,
    fld4060 (f := 3) (j := 0) (L := 15) 15 18 rfl (by omega) rfl (by omega) c0_eq l15,
    fld4060 (f := 3) (j := 1) (L := 16) 15 18 rfl (by omega) rfl (by omega) c1_eq l16,
    fld4060 (f := 3) (j := 2) (L := 17) 15 18 rfl (by omega) rfl (by omega) ns0_eq l17,
    fld4060 (f := 3) (j := 3) (L := 18) 15 18 rfl (by omega) rfl (by omega) ns1_eq l18,
    res_tuple (s := 0) (l := 7) rfl (by omega) (by omega) c0_eq cC0 resC0,
    res_tuple (s := 0) (l := 7) rfl (by omega) (by omega) c1_eq cC1 resC1,
    fun i hi => res_tuple (s := 7) (l := 7) rfl (by omega) (by omega) (sg_eq hi)
      (allN_spec cSG i hi) (RSj.all i hi),
    fun i hi => res_tuple (s := 14) (l := 10) rfl (by omega) (by omega) (kg_eq hi)
      (kok_spec hi).2 (RKj.all i hi),
    fun i hi => res_tuple (s := 24) (l := 10) rfl (by omega) (by omega) (jg_eq hi)
      (jok_spec hi).2 (RJj.all i hi),
    fun i hi => res_tuple (s := 34) (l := 7) rfl (by omega) (by omega) (rg_eq hi)
      (rok_spec hi).2 (RRj.all i hi), ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
    ⟨fun i hi g hg => ?_, fun i hi g hg => ?_, fun i hi j hj => ?_, fun i hi j hj => ?_,
    fun i hi => ⟨imgK_inc (ij_h hi (k := 0) (by omega)), imgK_lt (ij_h hi (k := 0) (by omega))⟩,
    fun i hi => ⟨imgK_inc (ik_h hi (k := 0) (by omega)), imgK_lt (ik_h hi (k := 0) (by omega))⟩,
    nodup_of_heads hdC, nodup_of_heads hdN,
    fun g hg i hi => by simpa [Nat.blt_eq] using allN_spec (allN_spec pbC g hg) i hi,
    fun g hg i hi => by simpa [Nat.blt_eq] using allN_spec (allN_spec pbN g hg) i hi,
    rfl, rfl, rfl, rfl⟩⟩
  · rw [field80_get (by omega), c0_eq, res80_eq cC0 res80C0]
    exact eqA_unpack_self _ _ _
  · rw [field80_get (by omega), c1_eq, res80_eq cC1 res80C1]
    exact eqA_unpack_self _ _ _
  · rw [z_eq, ← idK_sound idOK]
    exact neIdK_sound zNe
  · rw [z_eq]
    exact sqIdK_sound zSq
  · rw [z_eq, c0_eq]
    exact commK_sound zC0
  · rw [z_eq, c1_eq]
    exact commK_sound zC1
  · intro i hi
    have hy := yLt' i hi
    have e1 : ruY[i]! = pg 12 (mask 12) Y i := by
      rw [y_eq, unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
    have e2 : ruZA[pg 12 (mask 12) Y i]! = pg 12 (mask 12) Z (pg 12 (mask 12) Y i) := by
      rw [z_eq, unpack, getElem!_pos _ _ (by simpa using hy), Array.getElem_ofFn]
    rw [e1, e2]
    exact Nat.eq_of_beq_eq_true (allN_spec zY i hi)
  · rw [(binds2 c0_eq c1_eq).2 g hg]
    exact imgK_sound (ic_h hi hg)
  · rw [(binds2 ns0_eq ns1_eq).2 g hg]
    exact imgK_sound (in_h hi hg)
  · rw [jg_eq hj]
    exact imgK_sound (ij_h hi hj)
  · rw [kg_eq hj]
    exact imgK_sound (ik_h hi hj)

end CertificateChecks.KernelSporSch.RuCe

end
