module

public import Certificates.Kernel.SporSch.Tits.Disp260140K
public import Certificates.Kernel.SporSch.Tits.Inv2266
public import Certificates.Kernel.EvenBN.K27580P
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawSiftK
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsDisp

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Quasithin.B42Tits
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsAbel

theorem okV_spec {wd : List Int} (h : okV wd = true) :
    wordArr 1755 titsDerivedArrs wd = unpack 1755 11 (wK wd) ∧ C (wK wd) ∧ C (pinv (wK wd)) ∧
      invCand 1755 (unpack 1755 11 (wK wd)) = unpack 1755 11 (pinv (wK wd)) := by
  unfold okV at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
  exact ⟨wa_eq h1, h2, h3, invCand_unpack h4⟩

theorem cj_eq {wd : List Int} {x : Nat} (hv : okV wd = true) (hx : C x) :
    conjArr (wordArr 1755 titsDerivedArrs wd) (unpack 1755 11 x) = unpack 1755 11 (cj wd x) ∧
      C (cj wd x) := by
  obtain ⟨e1, c1, c2, e2⟩ := okV_spec hv
  unfold conjArr
  rw [e1, e2, cu c1 hx, cu (cc c1 hx) c2]
  exact ⟨rfl, cc (cc c1 hx) c2⟩

theorem ct_eq : titsCtArr = unpack 1755 11 ctK ∧ C ctK := by
  obtain ⟨e, c⟩ := cj_eq kVT TitsInv.cT
  unfold titsCtArr
  rw [TitsInv.t_eq, e, cu TitsInv.cT c]
  exact ⟨rfl, cc TitsInv.cT c⟩

theorem cz_eq : titsCzArr = unpack 1755 11 czK ∧ C czK := by
  obtain ⟨e2, c2⟩ := cj_eq kVZ2 canonZ
  obtain ⟨e3, c3⟩ := cj_eq kVZ3 canonZ
  unfold titsCzArr
  rw [z_eq, e2, e3, cu canonZ c2, cu (cc canonZ c2) c3]
  exact ⟨rfl, cc (cc canonZ c2) c3⟩

theorem pow_eq {p : Nat} (hp : C p) :
    ∀ k, titsPowArr (unpack 1755 11 p) k = unpack 1755 11 (pw p k) ∧ C (pw p k)
  | 0 => by
    rw [titsPowArr]
    exact ⟨TitsCentral.id_eq, canId⟩
  | k + 1 => by
    obtain ⟨e, c⟩ := pow_eq hp k
    rw [titsPowArr, e, cu hp c]
    exact ⟨rfl, cc hp c⟩

theorem ord_ok {x : Array Nat} {p : Nat} (hx : x = unpack 1755 11 p ∧ C p)
    (hne : neIdK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) p = true)
    (h13 : Nat.beq (pw p 13) (pidn 1755 11) = true) :
    eqA 1755 x (idA 1755) = false ∧ eqA 1755 (titsPowArr x 13) (idA 1755) = true := by
  rw [hx.1, (pow_eq hx.2 13).1, TitsCentral.id_eq, eqA_unpack (pow_eq hx.2 13).2 canId, h13,
    ← TitsCentral.id_eq, neIdK_sound hne]
  exact ⟨rfl, rfl⟩

theorem order : titsOrderCheck = true := by
  obtain ⟨t1, t2⟩ := ord_ok ct_eq kCtNe kCt13
  obtain ⟨z1, z2⟩ := ord_ok cz_eq kCzNe kCz13
  unfold titsOrderCheck
  rw [lettersK_sound kLT, lettersK_sound kLZ2, lettersK_sound kLZ3, TitsInv.isInvW kLT,
    TitsInv.isInvW kLZ2, TitsInv.isInvW kLZ3, t1, t2, z1, z2]
  rfl

theorem ndS : (baseArr 1755 titsSBase).toList.Nodup := by decide

theorem repS {A : Nat} (hA : A ∈ CertificateChecks.KernelEvenBN.E32.SI.L) :
    siftA 1755 (rawLevels 1755 titsSArrs (baseArr 1755 titsSBase)) (baseArr 1755 titsSBase) 0
      (unpack 1755 11 A) = true ∧ ∃ σ, Rep 1755 (unpack 1755 11 A) σ := by
  have k := List.all_eq_true.1 CertificateChecks.KernelEvenBN.E32.lK A hA
  rw [Bool.and_eq_true] at k
  obtain ⟨cA, sA⟩ := k
  have hs := siftK_soundR bindsS permS TitsS.hl rfl (hi_of cA) (range_of_canonK cA) sA
  obtain ⟨-, -, -, r⟩ := canonK_facts cA
  exact ⟨hs, rep_of_siftA bindsS permS TitsS.hl 5 0 rfl _
    (fun i hi => by rw [unpack_getT hi]; exact r i hi) hs⟩

theorem commS_eq {A B : Nat} (hA : A ∈ CertificateChecks.KernelEvenBN.E32.SI.L)
    (hB : B ∈ CertificateChecks.KernelEvenBN.E32.SI.L) :
    commS A B = commA (unpack 1755 11 A) (unpack 1755 11 B) := by
  obtain ⟨G, hmem, hsep⟩ := chain_group bindsS TitsS.head TitsS.hl (NS := 220) (CH := 8)
    (by norm_num) TitsS.hs ndS
  have hbl := CFSG.KS.Raw.Orb.base_lt_of_levels bindsS TitsS.hl
  obtain ⟨hA, σ, rA⟩ := repS hA
  obtain ⟨hB, τ, rB⟩ := repS hB
  exact baseComm_of_sep hsep hbl (fun t ht => bindsS.2.2.2.2.2.2 t ht) rA rB
    ((hmem _ _ rA).1 hA) ((hmem _ _ rB).1 hB)
    (fun i hi => by rw [pgR_eq, unpack_getT hi]) (fun i hi => by rw [pgR_eq, unpack_getT hi])

theorem len : TitsIC.length = 143 := Nat.eq_of_beq_eq_true kLen

theorem mem {i : Nat} (hi : i < 143) : TitsIC[i]! ∈ TitsIC := by
  rw [getElem!_pos TitsIC i (by rw [len]; exact hi)]
  exact List.getElem_mem _

theorem cX {i : Nat} (hi : i < 143) : C TitsIC[i]! := allL_spec TitsInv.kICc _ (mem hi)

theorem sX {i : Nat} (hi : i < 143) : TitsIC[i]! ∈ CertificateChecks.KernelEvenBN.E32.SI.L :=
  memN_spec (allL_spec kInS _ (mem hi))

theorem getU {i : Nat} (hi : i < 143) : titsInvConj[i]! = unpack 1755 11 TitsIC[i]! := by
  rw [TitsInv.ic_eq, getElem!_pos (TitsIC.map (unpack 1755 11)) i (by rw [List.length_map, len]; exact hi),
    getElem!_pos TitsIC i (by rw [len]; exact hi), List.getElem_map]

theorem commU {i j : Nat} (hi : i < 143) (hj : j < 143) :
    commA titsInvConj[i]! titsInvConj[j]! = commS TitsIC[i]! TitsIC[j]! := by
  rw [getU hi, getU hj, commS_eq (sX hi) (sX hj)]

theorem colour : titsColourCheck = true := by
  have e : (allLt 143 fun i => allLt 143 fun j => i == j || titsInvColour[i]! != titsInvColour[j]! ||
      !commA titsInvConj[i]! titsInvConj[j]!) = colK titsInvColour := by
    unfold colK
    exact allLt_eq_allN fun i hi => allLt_eq_allN fun j hj => by rw [commU hi hj]
  unfold titsColourCheck
  rw [e, kCol]
  decide

theorem zOutU {i j : Nat} (hi : i < 143) (hj : j < 143) :
    (allLt 143 fun k => !titsInvCert[k]!.1 ||
      !eqA 1755 (compA 1755 titsInvConj[i]! titsInvConj[j]!) titsInvConj[k]!) =
      zOut (pc TitsIC[i]! TitsIC[j]!) := by
  unfold zOut
  refine allLt_eq_allN fun k hk => ?_
  rw [getU hi, getU hj, getU hk, cu (cX hi) (cX hj), eqA_unpack (cc (cX hi) (cX hj)) (cX hk)]

theorem colourA : titsColourACheck = true := by
  have e : (allLt 143 fun i => allLt 143 fun j => !(titsInvCert[i]!.1 && titsInvCert[j]!.1) ||
      i == j || titsInvColourA[i]! != titsInvColourA[j]! ||
      !commA titsInvConj[i]! titsInvConj[j]! ||
      allLt 143 fun k => !titsInvCert[k]!.1 ||
        !eqA 1755 (compA 1755 titsInvConj[i]! titsInvConj[j]!) titsInvConj[k]!) =
      colAK titsInvColourA := by
    unfold colAK
    exact allLt_eq_allN fun i hi => allLt_eq_allN fun j hj => by rw [commU hi hj, zOutU hi hj]
  unfold titsColourACheck
  rw [e, kColA]
  decide

theorem facts : titsOrderCheck = true ∧ titsColourCheck = true ∧ titsColourACheck = true :=
  ⟨order, colour, colourA⟩

end CertificateChecks.KernelSporSch.TitsDisp

end
