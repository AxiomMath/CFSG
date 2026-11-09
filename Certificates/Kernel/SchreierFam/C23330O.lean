module

public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.Sporadic.He.Stab2110
public import Certificates.Data.SolMaxHeGen
public meta import Certificates.Data.SolMaxHeGen
public meta import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PK.Basic
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CertificateChecks.KernelSchreierFam.He23330

open CFSG.Sporadic.HeldB CFSG.ComponentClassification.SolMax.HeGen CFSG.Monster.B.Co2.Native

meta def arrC : Array (Array Nat) := heCArrs ++ heCArrs.map (invCand 8330)

meta def arrD : Array (Array Nat) := dArrs ++ dArrs.map (invCand 8330)

meta def arrF : Array (Array Nat) := #[f1A, f2A, cA, g0A, invCand 8330 g0A]

meta def arrSI : Array (Array Nat) := (Array.range 9).map fun k => invCand 8330 (heStrong k)

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Certificates.Native in
meta def arrW : Array (Array Nat) :=
  let wa := wordA 8330 heLetterArrs (heLetterArrs.map (invCand 8330))
  let blk := fun (w : List Int) (k : Nat) =>
    #[wa (w.take 26), wa ((w.take 26).drop 12)] ++
      ((List.range (k + 1)).map fun j => wa (w.drop ((k - j) * 26))).toArray
  blk heCentW1 7 ++ blk heCentW2 10

end CertificateChecks.KernelSchreierFam.He23330

end

#kmisc_packarrs CertificateChecks.KernelSchreierFam.He23330.TC
  CertificateChecks.KernelSchreierFam.He23330.arrC 14
#kmisc_packarrs CertificateChecks.KernelSchreierFam.He23330.TD
  CertificateChecks.KernelSchreierFam.He23330.arrD 14
#kmisc_packarrs CertificateChecks.KernelSchreierFam.He23330.TF
  CertificateChecks.KernelSchreierFam.He23330.arrF 14
#kmisc_packarrs CertificateChecks.KernelSchreierFam.He23330.TSI
  CertificateChecks.KernelSchreierFam.He23330.arrSI 14
#kmisc_packarrs CertificateChecks.KernelSchreierFam.He23330.TW
  CertificateChecks.KernelSchreierFam.He23330.arrW 14

public section

namespace CertificateChecks.KernelSchreierFam.He23330

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Sporadic.HeldB
  CFSG.ComponentClassification.SolMax.HeGen CertificateChecks.KernelLC.HeFix
  CertificateChecks.KernelSpor

@[expose] noncomputable def ID : Nat := pidn 8330 14

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 8330 14 (mask 14) p q

@[expose] noncomputable def wv (S SI : Nat → Nat) (wd : List Int) : Nat :=
  wordK 8330 14 (mask 14) (pidn 8330 14) S SI wd

@[expose] noncomputable def cnK (p : Nat) : Bool := canonK 8330 14 (mask 14) (8330 * 14) p

@[expose] noncomputable def invK (p q : Nat) : Bool :=
  bAnd(permOK 8330 14 (mask 14) (8330 * 14) p q, bAnd(permOK 8330 14 (mask 14) (8330 * 14) q p,
    bAnd(cnK p, cnK q)))

@[expose] def WC (i : Nat) : List Int := [heCentW1, heCentW2].getD i []

@[expose] def WT1 : List Int := [-2, 2, 2, -2, -2, -2, -2, 2, 2, 2, 1, 2]

@[expose] def WR1 : List Int := [3, -2, -1, -2, -2, -2, 2, 2, 2, 2, -2, -2, 2, 3]

@[expose] def WT2 : List Int := [-2, 2, 1, 1, 1, -2, 1, 2, -2, 1, -2, -2]

@[expose] def WR2 : List Int := [3, 2, 2, -1, 2, -2, -1, 2, -1, -1, -1, -2, 2, 3]

@[expose] def WTw (i : Nat) : List Int := [WT1, WT2].getD i []

@[expose] def WRw (i : Nat) : List Int := [WR1, WR2].getD i []

@[expose] def WKk (i : Nat) : Nat := [7, 10].getD i 0

@[expose] noncomputable def WZv (i : Nat) : Nat := TW (Nat.mul i 10)

@[expose] noncomputable def WRv (i : Nat) : Nat := TW (Nat.add (Nat.mul i 10) 1)

@[expose] noncomputable def WP (i j : Nat) : Nat := TW (Nat.add (Nat.add (Nat.mul i 10) 2) j)

@[expose] noncomputable def CW (i : Nat) : Nat := TC i

@[expose] noncomputable def CWI (i : Nat) : Nat := TC (2 + i)

@[expose] noncomputable def DW (j : Nat) : Nat := TD j

@[expose] noncomputable def DWI (j : Nat) : Nat := TD (3 + j)

@[expose] noncomputable def F1 : Nat := TF 0

@[expose] noncomputable def F2 : Nat := TF 1

@[expose] noncomputable def CC : Nat := TF 2

@[expose] noncomputable def G0 : Nat := TF 3

@[expose] noncomputable def G0I : Nat := TF 4

@[expose] noncomputable def cj (x : Nat) : Nat := pc G0I (pc x G0)

@[expose] noncomputable def FP : List Nat := [cj F1, cj F2, cj (pc F1 F2)]

@[expose] noncomputable def SG (k : Nat) : Nat := HeText.F k

@[expose] noncomputable def SGI (k : Nat) : Nat := TSI k

@[expose] noncomputable def stabK (s si x : Nat) : Bool :=
  FP.any fun y => Nat.beq (pc s (pc x si)) y

@[expose] noncomputable def cuK (j : Nat) : Bool := bAnd(cnK (LU j), cnK (LUI j))

@[expose] noncomputable def ttK (i : Nat) : Bool := Nat.beq (wv LU LUI (WTw i)) (WP i 0)

@[expose] noncomputable def rrK (i : Nat) : Bool := Nat.beq (wv LU LUI (WRw i)) (WRv i)

@[expose] noncomputable def zzK (i : Nat) : Bool := Nat.beq (pc (WP i 0) (WRv i)) (WZv i)

@[expose] noncomputable def st0K (j : Nat) : Bool := Nat.beq (pc (WZv 0) (WP 0 j)) (WP 0 (Nat.succ j))

@[expose] noncomputable def st1K (j : Nat) : Bool := Nat.beq (pc (WZv 1) (WP 1 j)) (WP 1 (Nat.succ j))

@[expose] noncomputable def lK (i : Nat) : Bool :=
  bAnd(szOK 8330 14, bAnd(lettersK 3 (WC i), Nat.beq (WP i (WKk i)) (CW i)))

@[expose] noncomputable def sK (k : Nat) : Bool :=
  bAnd(invK (SG k) (SGI k),
    (!Nat.beq (pg 14 (mask 14) (SG k) 0) 0 || FP.all fun x => stabK (SG k) (SGI k) x))

@[expose] noncomputable def ciK (i : Nat) : Bool := invK (CW i) (CWI i)

@[expose] noncomputable def diK (j : Nat) : Bool := invK (DW j) (DWI j)

@[expose] noncomputable def dwK (j : Nat) : Bool :=
  wordEqK 8330 14 (mask 14) (pidn 8330 14) CW CWI 2 (heDerivedV.getD j []) (DW j)

@[expose] noncomputable def f0K (_ : Nat) : Bool :=
  wordEqK 8330 14 (mask 14) (pidn 8330 14) DW DWI 3 wF1 F1

@[expose] noncomputable def f1K (_ : Nat) : Bool :=
  wordEqK 8330 14 (mask 14) (pidn 8330 14) DW DWI 3 wF2 F2

@[expose] noncomputable def f2K (_ : Nat) : Bool :=
  wordEqK 8330 14 (mask 14) (pidn 8330 14) DW DWI 3 wC CC

@[expose] noncomputable def f3K (_ : Nat) : Bool :=
  wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 wG0 G0

@[expose] noncomputable def f4K (_ : Nat) : Bool :=
  invK G0 G0I

@[expose] noncomputable def f5K (_ : Nat) : Bool :=
  cnK F1

@[expose] noncomputable def f6K (_ : Nat) : Bool :=
  cnK F2

@[expose] noncomputable def f7K (_ : Nat) : Bool :=
  cnK CC

@[expose] noncomputable def f8K (_ : Nat) : Bool :=
  cnK ID

@[expose] noncomputable def e0K (_ : Nat) : Bool :=
  Nat.beq (pc F1 F1) ID && true

@[expose] noncomputable def e1K (_ : Nat) : Bool :=
  !Nat.beq F1 ID

@[expose] noncomputable def e2K (_ : Nat) : Bool :=
  Nat.beq (pc F2 F2) ID && true

@[expose] noncomputable def e3K (_ : Nat) : Bool :=
  !Nat.beq F2 ID

@[expose] noncomputable def e4K (_ : Nat) : Bool :=
  !Nat.beq F1 F2

@[expose] noncomputable def e5K (_ : Nat) : Bool :=
  Nat.beq (pc F1 F2) (pc F2 F1) && true

@[expose] noncomputable def e6K (_ : Nat) : Bool :=
  Nat.beq (pc CC (pc CC CC)) ID && true

@[expose] noncomputable def e7K (_ : Nat) : Bool :=
  !Nat.beq CC ID

@[expose] noncomputable def e8K (_ : Nat) : Bool :=
  Nat.beq (pc CC F1) (pc F1 CC) && true

@[expose] noncomputable def e9K (_ : Nat) : Bool :=
  Nat.beq (pc CC F2) (pc F2 CC) && true

@[expose] noncomputable def e10K (_ : Nat) : Bool :=
  !Nat.beq (pc CC (DW 0)) (pc (DW 0) CC)

@[expose] noncomputable def e11K (_ : Nat) : Bool :=
  Nat.beq (pg 14 (mask 14) G0 0) 4065 && true

@[expose] noncomputable def e12K (_ : Nat) : Bool :=
  !Nat.beq (pg 14 (mask 14) (DW 2) 4065) 4065

@[expose] noncomputable def nK (_ : Nat) : Bool :=
  !(Nat.beq F1 CC || Nat.beq (pc CC CC) ID)

end CertificateChecks.KernelSchreierFam.He23330

end

#kss_each CertificateChecks.KernelSchreierFam.He23330.KCU CertificateChecks.KernelSchreierFam.He23330.cuK 4
#kss_each CertificateChecks.KernelSchreierFam.He23330.KT CertificateChecks.KernelSchreierFam.He23330.ttK 2
#kss_each CertificateChecks.KernelSchreierFam.He23330.KR CertificateChecks.KernelSchreierFam.He23330.rrK 2
#kss_each CertificateChecks.KernelSchreierFam.He23330.KZ CertificateChecks.KernelSchreierFam.He23330.zzK 2
#kss_each CertificateChecks.KernelSchreierFam.He23330.KP0 CertificateChecks.KernelSchreierFam.He23330.st0K 7
#kss_each CertificateChecks.KernelSchreierFam.He23330.KP1 CertificateChecks.KernelSchreierFam.He23330.st1K 10
#kss_each CertificateChecks.KernelSchreierFam.He23330.KL CertificateChecks.KernelSchreierFam.He23330.lK 2
#kss_each CertificateChecks.KernelSchreierFam.He23330.KS CertificateChecks.KernelSchreierFam.He23330.sK 9
#kss_each CertificateChecks.KernelSchreierFam.He23330.KCI CertificateChecks.KernelSchreierFam.He23330.ciK 2
#kss_each CertificateChecks.KernelSchreierFam.He23330.KDI CertificateChecks.KernelSchreierFam.He23330.diK 3
#kss_each CertificateChecks.KernelSchreierFam.He23330.KD CertificateChecks.KernelSchreierFam.He23330.dwK 3
#kss_each CertificateChecks.KernelSchreierFam.He23330.KF0 CertificateChecks.KernelSchreierFam.He23330.f0K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KF1 CertificateChecks.KernelSchreierFam.He23330.f1K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KF2 CertificateChecks.KernelSchreierFam.He23330.f2K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KF3 CertificateChecks.KernelSchreierFam.He23330.f3K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KF4 CertificateChecks.KernelSchreierFam.He23330.f4K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KF5 CertificateChecks.KernelSchreierFam.He23330.f5K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KF6 CertificateChecks.KernelSchreierFam.He23330.f6K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KF7 CertificateChecks.KernelSchreierFam.He23330.f7K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KF8 CertificateChecks.KernelSchreierFam.He23330.f8K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KE0 CertificateChecks.KernelSchreierFam.He23330.e0K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KE1 CertificateChecks.KernelSchreierFam.He23330.e1K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KE2 CertificateChecks.KernelSchreierFam.He23330.e2K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KE3 CertificateChecks.KernelSchreierFam.He23330.e3K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KE4 CertificateChecks.KernelSchreierFam.He23330.e4K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KE5 CertificateChecks.KernelSchreierFam.He23330.e5K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KE6 CertificateChecks.KernelSchreierFam.He23330.e6K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KE7 CertificateChecks.KernelSchreierFam.He23330.e7K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KE8 CertificateChecks.KernelSchreierFam.He23330.e8K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KE9 CertificateChecks.KernelSchreierFam.He23330.e9K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KE10 CertificateChecks.KernelSchreierFam.He23330.e10K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KE11 CertificateChecks.KernelSchreierFam.He23330.e11K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KE12 CertificateChecks.KernelSchreierFam.He23330.e12K 1
#kss_each CertificateChecks.KernelSchreierFam.He23330.KN CertificateChecks.KernelSchreierFam.He23330.nK 1

public section

namespace CertificateChecks.KernelSchreierFam.He23330

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Sporadic.HeldB
  CFSG.ComponentClassification.SolMax.HeGen CertificateChecks.KernelLC.HeFix
  CertificateChecks.KernelSpor

theorem kCnU : allN 4 (fun j => bAnd(cnK (LU j), cnK (LUI j))) = true := by
  have h : allN 4 cuK = true := PK.allN_iff.2 KCU.all
  delta cuK at h
  exact h

theorem kWT {i : Nat} (hi : i < 2) : wv LU LUI (WTw i) = WP i 0 :=
  Nat.eq_of_beq_eq_true (KT.all i hi)

theorem kWR {i : Nat} (hi : i < 2) : wv LU LUI (WRw i) = WRv i :=
  Nat.eq_of_beq_eq_true (KR.all i hi)

theorem kWZ {i : Nat} (hi : i < 2) : pc (WP i 0) (WRv i) = WZv i :=
  Nat.eq_of_beq_eq_true (KZ.all i hi)

theorem kP0 {j : Nat} (hj : j < 7) : pc (WZv 0) (WP 0 j) = WP 0 (j + 1) :=
  Nat.eq_of_beq_eq_true (KP0.all j hj)

theorem kP1 {j : Nat} (hj : j < 10) : pc (WZv 1) (WP 1 j) = WP 1 (j + 1) :=
  Nat.eq_of_beq_eq_true (KP1.all j hj)

theorem kL {i : Nat} (hi : i < 2) :
    bAnd(szOK 8330 14, bAnd(lettersK 3 (WC i), Nat.beq (WP i (WKk i)) (CW i))) = true :=
  KL.all i hi

theorem andT {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem ofAndT {a : Bool} (h : (a && true) = true) : a = true := by
  rwa [Bool.and_true] at h

theorem kCI : allN 2 (fun i => invK (CW i) (CWI i)) = true := PK.allN_iff.2 KCI.all

theorem kD0 : wordEqK 8330 14 (mask 14) (pidn 8330 14) CW CWI 2 (heDerivedV.getD 0 []) (DW 0) =
    true := KD.c0

theorem kD1 : wordEqK 8330 14 (mask 14) (pidn 8330 14) CW CWI 2 (heDerivedV.getD 1 []) (DW 1) =
    true := KD.c1

theorem kD2 : wordEqK 8330 14 (mask 14) (pidn 8330 14) CW CWI 2 (heDerivedV.getD 2 []) (DW 2) =
    true := KD.c2

theorem kDI : allN 3 (fun j => invK (DW j) (DWI j)) = true := PK.allN_iff.2 KDI.all

theorem kF : bAnd(wordEqK 8330 14 (mask 14) (pidn 8330 14) DW DWI 3 wF1 F1,
    bAnd(wordEqK 8330 14 (mask 14) (pidn 8330 14) DW DWI 3 wF2 F2,
    bAnd(wordEqK 8330 14 (mask 14) (pidn 8330 14) DW DWI 3 wC CC,
    bAnd(wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 wG0 G0,
    bAnd(invK G0 G0I, bAnd(cnK F1, bAnd(cnK F2, bAnd(cnK CC, cnK ID)))))))) = true := by
  simp only [PK.bAnd_eq, Bool.and_eq_true]
  exact ⟨KF0.c0, KF1.c0, KF2.c0, KF3.c0, KF4.c0, KF5.c0, KF6.c0, KF7.c0, KF8.c0⟩

theorem kE : (Nat.beq (pc F1 F1) ID && !Nat.beq F1 ID && Nat.beq (pc F2 F2) ID &&
    !Nat.beq F2 ID && !Nat.beq F1 F2 && Nat.beq (pc F1 F2) (pc F2 F1) &&
    Nat.beq (pc CC (pc CC CC)) ID && !Nat.beq CC ID && Nat.beq (pc CC F1) (pc F1 CC) &&
    Nat.beq (pc CC F2) (pc F2 CC) && !Nat.beq (pc CC (DW 0)) (pc (DW 0) CC) &&
    Nat.beq (pg 14 (mask 14) G0 0) 4065 && !Nat.beq (pg 14 (mask 14) (DW 2) 4065) 4065) = true :=
  andT (andT (andT (andT (andT (andT (andT (andT (andT (andT (andT (andT (ofAndT KE0.c0) KE1.c0)
    (ofAndT KE2.c0)) KE3.c0) KE4.c0) (ofAndT KE5.c0)) (ofAndT KE6.c0)) KE7.c0) (ofAndT KE8.c0))
    (ofAndT KE9.c0)) KE10.c0) (ofAndT KE11.c0)) KE12.c0

theorem kS : allN 9 (fun k => bAnd(invK (SG k) (SGI k),
    (!Nat.beq (pg 14 (mask 14) (SG k) 0) 0 || FP.all fun x => stabK (SG k) (SGI k) x))) =
    true := by
  have h : allN 9 sK = true := PK.allN_iff.2 KS.all
  delta sK at h
  exact h

theorem kNeg : (Nat.beq F1 CC || Nat.beq (pc CC CC) ID) = false :=
  Bool.eq_false_iff.2 fun h => by
    have h0 : nK 0 = true := KN.c0
    rw [nK, h] at h0
    exact absurd h0 (by decide)

end CertificateChecks.KernelSchreierFam.He23330
