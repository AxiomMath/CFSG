module

public import Certificates.Kernel.SporSch.Mathieu.GenOddPt
public import Certificates.Kernel.LocalQT.He4148.Glue
public import Certificates.Data.SolMaxHeGen
public meta import Certificates.Data.SolMaxHeGen
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Range.Basic
import all Init.Data.Nat.Fold
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CertificateChecks.KernelSchreierFam

open CFSG.KS.SporSch.MOCG CFSG.ComponentClassification.SolMax.HeGen

meta def SK23330 : Array (Array Nat) := strongOf 240 (wK.map kA).toArray kWords

meta def baseK23330 : Array Nat := #[0, 1, 2]

meta def sig23330 : Array (Array Nat) := sigArrs

end CertificateChecks.KernelSchreierFam

end

#ks_rawchain CertificateChecks.KernelSchreierFam.KQ 240 8 16
  CertificateChecks.KernelSchreierFam.SK23330 CertificateChecks.KernelSchreierFam.baseK23330 3
  CFSG.ComponentClassification.SolMax.HeGen.kWords

#kmisc_packarrs CertificateChecks.KernelSchreierFam.TS23330
  CertificateChecks.KernelSchreierFam.sig23330 8

public section

namespace CertificateChecks.KernelSchreierFam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Sporadic.HeldB CertificateChecks.KernelLQT.He4148
open CFSG.ComponentClassification.SolMax.HeGen CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Sporadic.Schreier

@[expose] noncomputable def iS (j : Nat) : Nat := TS23330 j

@[expose] noncomputable def iID : Nat := pidn 240 8

@[expose] noncomputable def ipc (p q : Nat) : Nat := pcomp 240 8 (mask 8) p q

@[expose] noncomputable def ipi (p : Nat) : Nat := pinvS 240 8 (mask 8) p

@[expose] noncomputable def icK (p : Nat) : Bool := canonK 240 8 (mask 8) (240 * 8) p

@[expose] noncomputable def ipO (p q : Nat) : Bool := permOK 240 8 (mask 8) (240 * 8) p q

@[expose] noncomputable def iQ1 : Nat := ipc (iS 3) iID

@[expose] noncomputable def iQ2 : Nat := ipc (iS 8) iQ1

@[expose] noncomputable def iQ3 : Nat := ipc (iS 4) iQ2

@[expose] noncomputable def iX5 : Nat := ipc (iS 1) iQ3

@[expose] noncomputable def iP2 : Nat := ipc iX5 iX5

@[expose] noncomputable def iP3 : Nat := ipc iX5 iP2

@[expose] noncomputable def iP4 : Nat := ipc iX5 iP3

@[expose] noncomputable def iV (j : Nat) : Nat := [iID, ipc (iS 1) iID, ipc (iS 5) iID].getD j 0

@[expose] noncomputable def iK (j : Nat) : Nat := ipc (iV j) (ipc iX5 (ipi (iV j)))

@[expose] noncomputable def bSK (j : Nat) : Bool := bindArrK sigArrs[j]! 240 8 (iS j)

@[expose] noncomputable def cSK (j : Nat) : Bool := icK (iS j)

@[expose] noncomputable def pSK (j : Nat) : Bool := ipO (iS j) (ipi (iS j))

@[expose] noncomputable def pSIK (j : Nat) : Bool := ipO (ipi (iS j)) (iS j)

@[expose] noncomputable def cVK (j : Nat) : Bool := icK (iV j)

@[expose] noncomputable def pVK (j : Nat) : Bool := ipO (iV j) (ipi (iV j))

@[expose] noncomputable def pVIK (j : Nat) : Bool := ipO (ipi (iV j)) (iV j)

@[expose] noncomputable def cVIK (j : Nat) : Bool := icK (ipi (iV j))

@[expose] noncomputable def cXVK (j : Nat) : Bool := icK (ipc iX5 (ipi (iV j)))

@[expose] noncomputable def eKK (j : Nat) : Bool := Nat.beq (iK j) (KQ.S j) && true

@[expose] noncomputable def qIK (j : Nat) : Bool := ipO (KQ.S j) (KQ.SI j)

@[expose] noncomputable def qIIK (j : Nat) : Bool := ipO (KQ.SI j) (KQ.S j)

@[expose] noncomputable def cPK (j : Nat) : Bool :=
  icK ([iID, iQ1, iQ2, iQ3, iX5, iP2, iP3, iP4, ipc iX5 iP4].getD j 0)

@[expose] noncomputable def idK23330 (_ : Nat) : Bool := bindArrK (idA 240) 240 8 iID

@[expose] noncomputable def pXK (_ : Nat) : Bool := ipO iX5 (ipi iX5)

@[expose] noncomputable def pXIK (_ : Nat) : Bool := ipO (ipi iX5) iX5

@[expose] noncomputable def x5K (_ : Nat) : Bool :=
  Nat.beq (ipc iX5 (ipc iX5 (ipc iX5 (ipc iX5 iX5)))) iID && true

@[expose] noncomputable def x1K (_ : Nat) : Bool := !Nat.beq iX5 iID

@[expose] noncomputable def x4K (_ : Nat) : Bool := !Nat.beq (ipc iX5 (ipc iX5 (ipc iX5 iX5))) iID

@[expose] noncomputable def oKK (_ : Nat) : Bool := Nat.beq (ordK KQ.LR 3) 40320 && true

end CertificateChecks.KernelSchreierFam

end

#kss_each CertificateChecks.KernelSchreierFam.KBS23330 CertificateChecks.KernelSchreierFam.bSK 9
#kss_each CertificateChecks.KernelSchreierFam.KCS23330 CertificateChecks.KernelSchreierFam.cSK 9
#kss_each CertificateChecks.KernelSchreierFam.KPS23330 CertificateChecks.KernelSchreierFam.pSK 9
#kss_each CertificateChecks.KernelSchreierFam.KPSI23330 CertificateChecks.KernelSchreierFam.pSIK 9
#kss_each CertificateChecks.KernelSchreierFam.KCV23330 CertificateChecks.KernelSchreierFam.cVK 3
#kss_each CertificateChecks.KernelSchreierFam.KPV23330 CertificateChecks.KernelSchreierFam.pVK 3
#kss_each CertificateChecks.KernelSchreierFam.KPVI23330 CertificateChecks.KernelSchreierFam.pVIK 3
#kss_each CertificateChecks.KernelSchreierFam.KCVI23330 CertificateChecks.KernelSchreierFam.cVIK 3
#kss_each CertificateChecks.KernelSchreierFam.KCXV23330 CertificateChecks.KernelSchreierFam.cXVK 3
#kss_each CertificateChecks.KernelSchreierFam.KEK23330 CertificateChecks.KernelSchreierFam.eKK 3
#kss_each CertificateChecks.KernelSchreierFam.KQI23330 CertificateChecks.KernelSchreierFam.qIK 3
#kss_each CertificateChecks.KernelSchreierFam.KQII23330 CertificateChecks.KernelSchreierFam.qIIK 3
#kss_each CertificateChecks.KernelSchreierFam.KCP23330 CertificateChecks.KernelSchreierFam.cPK 9
#kss_each CertificateChecks.KernelSchreierFam.KID23330 CertificateChecks.KernelSchreierFam.idK23330 1
#kss_each CertificateChecks.KernelSchreierFam.KPX23330 CertificateChecks.KernelSchreierFam.pXK 1
#kss_each CertificateChecks.KernelSchreierFam.KPXI23330 CertificateChecks.KernelSchreierFam.pXIK 1
#kss_each CertificateChecks.KernelSchreierFam.KX523330 CertificateChecks.KernelSchreierFam.x5K 1
#kss_each CertificateChecks.KernelSchreierFam.KX123330 CertificateChecks.KernelSchreierFam.x1K 1
#kss_each CertificateChecks.KernelSchreierFam.KX423330 CertificateChecks.KernelSchreierFam.x4K 1
#kss_each CertificateChecks.KernelSchreierFam.KO23330 CertificateChecks.KernelSchreierFam.oKK 1

public section

namespace CertificateChecks.KernelSchreierFam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Sporadic.HeldB CertificateChecks.KernelLQT.He4148
open CFSG.ComponentClassification.SolMax.HeGen CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Sporadic.Schreier

theorem ofAndT23330 {a : Bool} (h : (a && true) = true) : a = true := by
  rwa [Bool.and_true] at h

theorem andT23330 {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem cmp23330 {p q : Nat} (hp : icK p = true) (hq : icK q = true) :
    compA 240 (unpack 240 8 p) (unpack 240 8 q) = unpack 240 8 (ipc p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

theorem inv23330 {p : Nat} (h : ipO p (ipi p) = true) :
    invCand 240 (unpack 240 8 p) = unpack 240 8 (ipi p) :=
  CFSG.KC.BfsPin.invCand_unpack h

theorem eqU23330 {p q : Nat} (hp : icK p = true) (hq : icK q = true) :
    eqA 240 (unpack 240 8 p) (unpack 240 8 q) = Nat.beq p q :=
  CFSG.KC.BfsPin.eqA_unpack hp hq

theorem pchk23330 {p q : Nat} (h1 : ipO p q = true) (h2 : ipO q p = true) :
    permChk 240 (unpack 240 8 p) = true :=
  (unpack_facts rfl h1 h2).1

theorem sig23330_eq {j : Nat} (hj : j < 9) : sigArrs[j]! = unpack 240 8 (iS j) :=
  unpack_eq_of_bindArrK (KBS23330.all j hj)

theorem id23330_eq : idA 240 = unpack 240 8 iID := unpack_eq_of_bindArrK KID23330.c0

theorem letter23330 (k : Nat) :
    letterA sigArrs (sigArrs.map (invCand 240)) ((k : Int) + 1) = sigArrs[k]! := by
  unfold letterA
  split
  · congr 1
  · omega

theorem x5_eq : x5A = unpack 240 8 iX5 := by
  have e : x5A = compA 240 (letterA sigArrs (sigArrs.map (invCand 240)) ((1 : Nat) + 1 : Int))
      (compA 240 (letterA sigArrs (sigArrs.map (invCand 240)) ((4 : Nat) + 1 : Int))
      (compA 240 (letterA sigArrs (sigArrs.map (invCand 240)) ((8 : Nat) + 1 : Int))
      (compA 240 (letterA sigArrs (sigArrs.map (invCand 240)) ((3 : Nat) + 1 : Int))
      (idA 240)))) := rfl
  rw [e, letter23330 1, letter23330 4, letter23330 8, letter23330 3,
    sig23330_eq (j := 1) (by decide), sig23330_eq (j := 4) (by decide),
    sig23330_eq (j := 8) (by decide), sig23330_eq (j := 3) (by decide), id23330_eq,
    cmp23330 (q := iID) (KCS23330.all 3 (by decide)) KCP23330.c0,
    cmp23330 (q := ipc (iS 3) iID) (KCS23330.all 8 (by decide)) KCP23330.c1,
    cmp23330 (q := ipc (iS 8) (ipc (iS 3) iID)) (KCS23330.all 4 (by decide)) KCP23330.c2,
    cmp23330 (q := ipc (iS 4) (ipc (iS 8) (ipc (iS 3) iID))) (KCS23330.all 1 (by decide))
      KCP23330.c3]
  rfl

theorem sw0_eq : sWord (wK.getD 0 []) = unpack 240 8 (iV 0) := id23330_eq

theorem sw1_eq : sWord (wK.getD 1 []) = unpack 240 8 (iV 1) := by
  have e : sWord (wK.getD 1 []) =
      compA 240 (letterA sigArrs (sigArrs.map (invCand 240)) ((1 : Nat) + 1 : Int)) (idA 240) := rfl
  rw [e, letter23330 1, sig23330_eq (j := 1) (by decide), id23330_eq,
    cmp23330 (q := iID) (KCS23330.all 1 (by decide)) KCP23330.c0]
  rfl

theorem sw2_eq : sWord (wK.getD 2 []) = unpack 240 8 (iV 2) := by
  have e : sWord (wK.getD 2 []) =
      compA 240 (letterA sigArrs (sigArrs.map (invCand 240)) ((5 : Nat) + 1 : Int)) (idA 240) := rfl
  rw [e, letter23330 5, sig23330_eq (j := 5) (by decide), id23330_eq,
    cmp23330 (q := iID) (KCS23330.all 5 (by decide)) KCP23330.c0]
  rfl

theorem sw_eq {j : Nat} (hj : j < 3) : sWord (wK.getD j []) = unpack 240 8 (iV j) := by
  match j, hj with
  | 0, _ => exact sw0_eq
  | 1, _ => exact sw1_eq
  | 2, _ => exact sw2_eq

theorem kA_eq {j : Nat} (hj : j < 3) : kA (wK.getD j []) = unpack 240 8 (KQ.S j) := by
  have e : kA (wK.getD j []) = compA 240 (sWord (wK.getD j []))
      (compA 240 x5A (invCand 240 (sWord (wK.getD j [])))) := rfl
  rw [e, sw_eq hj, x5_eq, inv23330 (KPV23330.all j hj),
    cmp23330 (p := iX5) KCP23330.c4 (KCVI23330.all j hj),
    cmp23330 (KCV23330.all j hj) (KCXV23330.all j hj)]
  have h := Nat.eq_of_beq_eq_true (ofAndT23330 (KEK23330.all j hj))
  rw [← h]
  rfl

theorem atK23330 {j : Nat} (hj : j < 3) :
    CFSG.Monster.B.Mathieu.imageList (permOrId 240 ((wK.map kA).getD j #[])) =
      (unpack 240 8 (KQ.S j)).toList := by
  have hl : wK.length = 3 := rfl
  have hjl : j < wK.length := hl ▸ hj
  have hj' : j < (wK.map kA).length := by rw [List.length_map]; exact hjl
  have e : (wK.map kA).getD j #[] = kA (wK.getD j []) := by
    rw [List.getD_eq_getElem _ _ hj', List.getElem_map, List.getD_eq_getElem _ _ hjl]
  rw [e, kA_eq hj]
  exact imageList_of_rep (unpack_size' 240 8 _)
    (unpack_facts rfl (KQI23330.all j hj) (KQII23330.all j hj)).2.1

theorem chainK23330 : ChainK 240 8 ((wK.map kA).map (permOrId 240)) kWords
    (#v[0, 1, 2] : Vector (Fin 240) 3) KQ.S KQ.SI KQ.LR KQ.TR KQ.TRI 6 KQ.BP 15 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, KQ.head, KQ.hl,
    by norm_num, .inl KQ.hs⟩
  have hj' : j < (wK.map kA).length := by simpa using hj
  rw [getD_map_lt _ #[] _ hj']
  have hl : wK.length = 3 := rfl
  exact atK23330 (hl ▸ hj)

theorem heGenK_check : heGenK.check = true ∧ heGenK.orderCertificate = 40320 := by
  have e : heGenK = certificate (by decide) ((wK.map kA).map (permOrId 240)) kWords
      (#v[0, 1, 2] : Vector (Fin 240) 3) (by decide) := by
    rw [heGenK, List.map_map]
    rfl
  rw [e]
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainK23330
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true (ofAndT23330 KO23330.c0))⟩

theorem sigma_all : heInnerSigma0.all (permChk 240) = true := by
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem ht
  have hl : heInnerSigma0.length = 9 := rfl
  have h9 : i < 9 := hl ▸ hi
  have e : t = sigArrs[i]! := by
    rw [← he, sigArrs, getElem!_pos heInnerSigma0.toArray i (by simpa using hi),
      List.getElem_toArray]
  rw [e, sig23330_eq h9]
  exact pchk23330 (KPS23330.all i h9) (KPSI23330.all i h9)

theorem words_all : wK.all (fun w => permChk 240 (sWord w) && permChk 240 (kA w)) = true := by
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem ht
  have hl : wK.length = 3 := rfl
  have h3 : j < 3 := hl ▸ hj
  have e : t = wK.getD j [] := by
    rw [← he]
    exact (List.getD_eq_getElem _ _ hj).symm
  rw [e, sw_eq h3, kA_eq h3]
  exact andT23330 (pchk23330 (KPV23330.all j h3) (KPVI23330.all j h3))
    (pchk23330 (KQI23330.all j h3) (KQII23330.all j h3))

theorem x5_pow : eqA 240 (compA 240 x5A (compA 240 x5A (compA 240 x5A (compA 240 x5A x5A))))
    (idA 240) = true := by
  rw [x5_eq, id23330_eq, cmp23330 (p := iX5) (q := iX5) KCP23330.c4 KCP23330.c4,
    cmp23330 (p := iX5) (q := ipc iX5 iX5) KCP23330.c4 KCP23330.c5,
    cmp23330 (p := iX5) (q := ipc iX5 (ipc iX5 iX5)) KCP23330.c4 KCP23330.c6,
    cmp23330 (p := iX5) (q := ipc iX5 (ipc iX5 (ipc iX5 iX5))) KCP23330.c4 KCP23330.c7,
    eqU23330 (p := ipc iX5 (ipc iX5 (ipc iX5 (ipc iX5 iX5)))) (q := iID)
      KCP23330.c8 KCP23330.c0]
  exact ofAndT23330 KX523330.c0

theorem x5_ne : (!eqA 240 x5A (idA 240)) = true := by
  rw [x5_eq, id23330_eq, eqU23330 (p := iX5) (q := iID) KCP23330.c4 KCP23330.c0]
  exact KX123330.c0

theorem innerArr_23330K : (heInnerSigma0.all (permChk 240) && lettersOK 9 wX5 &&
    wK.all (lettersOK 9) && permChk 240 x5A &&
    wK.all (fun w => permChk 240 (sWord w) && permChk 240 (kA w)) &&
    eqA 240 (compA 240 x5A (compA 240 x5A (compA 240 x5A (compA 240 x5A x5A)))) (idA 240) &&
    !eqA 240 x5A (idA 240)) = true := by
  have hx : permChk 240 x5A = true := by
    rw [x5_eq]
    exact pchk23330 KPX23330.c0 KPXI23330.c0
  exact andT23330 (andT23330 (andT23330 (andT23330 (andT23330 (andT23330 sigma_all
    (by decide +kernel)) (by decide +kernel)) hx) words_all) x5_pow) x5_ne

theorem innerNeg_23330K :
    eqA 240 (compA 240 x5A (compA 240 x5A (compA 240 x5A x5A))) (idA 240) = false := by
  rw [x5_eq, id23330_eq, cmp23330 (p := iX5) (q := iX5) KCP23330.c4 KCP23330.c4,
    cmp23330 (p := iX5) (q := ipc iX5 iX5) KCP23330.c4 KCP23330.c5,
    cmp23330 (p := iX5) (q := ipc iX5 (ipc iX5 iX5)) KCP23330.c4 KCP23330.c6,
    eqU23330 (p := ipc iX5 (ipc iX5 (ipc iX5 iX5))) (q := iID)
      KCP23330.c7 KCP23330.c0]
  have h : (!Nat.beq (ipc iX5 (ipc iX5 (ipc iX5 iX5))) iID) = true := KX423330.c0
  simpa using h

theorem heGenInner_23330 : heGenInnerCheck = true := by
  rw [heGenInnerCheck, heGenK_check.1, heGenK_check.2]
  simpa using innerArr_23330K

end CertificateChecks.KernelSchreierFam
