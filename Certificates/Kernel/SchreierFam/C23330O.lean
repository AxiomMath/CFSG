module

public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.Sporadic.He.Stab2110
public import Certificates.Data.SolMaxHeGen
public meta import Certificates.Data.SolMaxHeGen
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSchreierFam.He23330

open CFSG.Sporadic.HeldB CFSG.ComponentClassification.SolMax.HeGen CFSG.Monster.B.Co2.Native

meta def arrC : Array (Array Nat) := heCArrs ++ heCArrs.map (invCand 8330)

meta def arrD : Array (Array Nat) := dArrs ++ dArrs.map (invCand 8330)

meta def arrF : Array (Array Nat) := #[f1A, f2A, cA, g0A, invCand 8330 g0A]

end CertificateChecks.KernelSchreierFam.He23330

end

#kmisc_packarrs CertificateChecks.KernelSchreierFam.He23330.TC
  CertificateChecks.KernelSchreierFam.He23330.arrC 14
#kmisc_packarrs CertificateChecks.KernelSchreierFam.He23330.TD
  CertificateChecks.KernelSchreierFam.He23330.arrD 14
#kmisc_packarrs CertificateChecks.KernelSchreierFam.He23330.TF
  CertificateChecks.KernelSchreierFam.He23330.arrF 14

public section

namespace CertificateChecks.KernelSchreierFam.He23330

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Sporadic.HeldB
  CFSG.ComponentClassification.SolMax.HeGen CertificateChecks.KernelLC.HeFix
  CertificateChecks.KernelSpor

@[expose] noncomputable def ID : Nat := pidn 8330 14

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 8330 14 (mask 14) p q

@[expose] noncomputable def pi (p : Nat) : Nat := pinvS 8330 14 (mask 14) p

@[expose] noncomputable def wv (S SI : Nat → Nat) (wd : List Int) : Nat :=
  wordK 8330 14 (mask 14) (pidn 8330 14) S SI wd

@[expose] noncomputable def cnK (p : Nat) : Bool := canonK 8330 14 (mask 14) (8330 * 14) p

@[expose] noncomputable def invK (p q : Nat) : Bool :=
  bAnd(permOK 8330 14 (mask 14) (8330 * 14) p q, bAnd(permOK 8330 14 (mask 14) (8330 * 14) q p,
    bAnd(cnK p, cnK q)))

@[expose] def WC (i : Nat) : List Int := [heCentW1, heCentW2].getD i []

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

@[expose] noncomputable def stabK (s x : Nat) : Bool :=
  FP.any fun y => Nat.beq (pc s (pc x (pi s))) y

theorem kC0 : wordEqK 8330 14 (mask 14) (pidn 8330 14) LU LUI 3 (WC 0) (CW 0) = true := by
  quickRfl

theorem kC1 : wordEqK 8330 14 (mask 14) (pidn 8330 14) LU LUI 3 (WC 1) (CW 1) = true := by
  quickRfl

theorem kCI : allN 2 (fun i => invK (CW i) (CWI i)) = true := by quickRfl

theorem kD0 : wordEqK 8330 14 (mask 14) (pidn 8330 14) CW CWI 2 (heDerivedV.getD 0 []) (DW 0) =
    true := by
  quickRfl

theorem kD1 : wordEqK 8330 14 (mask 14) (pidn 8330 14) CW CWI 2 (heDerivedV.getD 1 []) (DW 1) =
    true := by
  quickRfl

theorem kD2 : wordEqK 8330 14 (mask 14) (pidn 8330 14) CW CWI 2 (heDerivedV.getD 2 []) (DW 2) =
    true := by
  quickRfl

theorem kDI : allN 3 (fun j => invK (DW j) (DWI j)) = true := by quickRfl

theorem kF : bAnd(wordEqK 8330 14 (mask 14) (pidn 8330 14) DW DWI 3 wF1 F1,
    bAnd(wordEqK 8330 14 (mask 14) (pidn 8330 14) DW DWI 3 wF2 F2,
    bAnd(wordEqK 8330 14 (mask 14) (pidn 8330 14) DW DWI 3 wC CC,
    bAnd(wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 wG0 G0,
    bAnd(invK G0 G0I, bAnd(cnK F1, bAnd(cnK F2, bAnd(cnK CC, cnK ID)))))))) = true := by
  quickRfl

theorem kE : (Nat.beq (pc F1 F1) ID && !Nat.beq F1 ID && Nat.beq (pc F2 F2) ID &&
    !Nat.beq F2 ID && !Nat.beq F1 F2 && Nat.beq (pc F1 F2) (pc F2 F1) &&
    Nat.beq (pc CC (pc CC CC)) ID && !Nat.beq CC ID && Nat.beq (pc CC F1) (pc F1 CC) &&
    Nat.beq (pc CC F2) (pc F2 CC) && !Nat.beq (pc CC (DW 0)) (pc (DW 0) CC) &&
    Nat.beq (pg 14 (mask 14) G0 0) 4065 && !Nat.beq (pg 14 (mask 14) (DW 2) 4065) 4065) = true := by
  decide +kernel

theorem kS : allN 9 (fun k => bAnd(invK (SG k) (pi (SG k)),
    (!Nat.beq (pg 14 (mask 14) (SG k) 0) 0 || FP.all fun x => stabK (SG k) x))) = true := by
  quickRfl

theorem kNeg : (Nat.beq F1 CC || Nat.beq (pc CC CC) ID) = false := by decide +kernel

end CertificateChecks.KernelSchreierFam.He23330
