module

public import Certificates.Kernel.Sporadic.OddCore.Suz1379101
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each

public section

#kc_repo #kc_ktree_gz CertificateChecks.KernelSpor.S1379101 CW
  "Certificates/Kernel/Sporadic/OddCore/data1379101/CW.bin.gz" 2451 4 14706 14811029822122032292
#kc_repo #kc_ktree_gz CertificateChecks.KernelSpor.S1379101 TRI
  "Certificates/Kernel/Sporadic/OddCore/data1379101/TRI.bin.gz" 2451 4 7353 13064891601533556731
#kc_repo #kc_ktree_gz CertificateChecks.KernelSpor.S1379101 TRII
  "Certificates/Kernel/Sporadic/OddCore/data1379101/TRII.bin.gz" 2451 4 7353 10655682379573407829
#kc_repo #kc_json_gz CertificateChecks.KernelSpor.S1379101.WD
  "Certificates/Kernel/Sporadic/OddCore/data1379101/W.json.gz" 18833 17913779928114083853
  (rw : List (List Nat)) (g2u : List (List Nat)) (g2v : List (List Nat)) (g3u : List (List Nat))
  (g3v : List (List Nat)) (q : List (List Nat)) (c : List (List Nat)) (wa : List Nat) (wb : List Nat)

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S1379101

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

@[expose] def dec (c : Nat) : Int := if c % 2 = 0 then Int.ofNat (c / 2) else -Int.ofNat (c / 2)

@[expose] def decW (l : List Nat) : List Int := l.map dec

@[expose] noncomputable def RW : Array (List Int) := (WD.rw.map decW).toArray
@[expose] noncomputable def G2U : Array (List Int) := (WD.g2u.map decW).toArray
@[expose] noncomputable def G2V : Array (List Int) := (WD.g2v.map decW).toArray
@[expose] noncomputable def G3U : Array (List Int) := (WD.g3u.map decW).toArray
@[expose] noncomputable def G3V : Array (List Int) := (WD.g3v.map decW).toArray
@[expose] noncomputable def QW : Array (List Int) := (WD.q.map decW).toArray
@[expose] noncomputable def CWd : Array (List Int) := (WD.c.map decW).toArray
@[expose] noncomputable def WA : List Int := decW WD.wa
@[expose] noncomputable def WB : List Int := decW WD.wb

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1782 11 (mask 11) p q

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS 1782 11 (mask 11) p

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 1782 11 (mask 11) (1782 * 11) p

@[expose] noncomputable def e : Nat := pidn 1782 11

@[expose] noncomputable def ok (p : Nat) : Bool :=
  cn p && (cn (pinv p) && permOK 1782 11 (mask 11) (1782 * 11) p (pinv p))

@[expose] noncomputable def W3 (w : List Int) : Nat := wordK 1782 11 (mask 11) e TRI TRII w

@[expose] noncomputable def CA (u v : Nat) : Nat := pc (pc (pc u v) (pinv u)) (pinv v)

@[expose] noncomputable def fr (a : Nat) : Nat := RT (r32 FR a)

@[expose] noncomputable def f2 (a : Nat) : Nat := N2T (r32 F2 a)

@[expose] noncomputable def f3 (a : Nat) : Nat := N3T (r32 F3 a)

@[expose] noncomputable def wEq (wd : List Int) (X : Nat) : Bool :=
  lettersK 3 wd && (Nat.beq (W3 wd) X && ok X)

@[expose] noncomputable def kTri (j : Nat) : Bool :=
  cn (TRI j) && (cn (TRII j) && permOK 1782 11 (mask 11) (1782 * 11) (TRI j) (TRII j))
@[expose] noncomputable def kRW (j : Nat) : Bool := wEq RW[j]! (RG j)
@[expose] noncomputable def kU2 (j : Nat) : Bool := Nat.blt (r32 FR j) 8192 && wEq G2U[j]! (fr j)
@[expose] noncomputable def kV2 (j : Nat) : Bool :=
  Nat.blt (r32 FR (7 + j)) 8192 && wEq G2V[j]! (fr (7 + j))
@[expose] noncomputable def kU3 (k : Nat) : Bool :=
  Nat.blt (r32 FR (14 + k)) 8192 && wEq G3U[k]! (fr (14 + k))
@[expose] noncomputable def kQ (i : Nat) : Bool :=
  Nat.blt (r32 FR (19 + i)) 8192 && (wEq QW[i]! (QG i) && Nat.beq (QG i) (fr (19 + i)))
@[expose] noncomputable def kV3 (k : Nat) : Bool := Nat.blt (r32 F2 k) 512 && wEq G3V[k]! (f2 k)
@[expose] noncomputable def kCw (i : Nat) : Bool := wEq CWd[i]! (CW i)

#kc_each kTri 0 3
#kc_each kRW 0 4
#kc_each kU2 0 7
#kc_each kV2 0 7
#kc_each kU3 0 5
#kc_each kQ 0 3
#kc_each kV3 0 5
#kc_each kCw 0 6

@[expose] noncomputable def kG2 (j : Nat) : Bool := Nat.beq (CA (fr j) (fr (7 + j))) (N2G j) && ok (N2G j)

@[expose] noncomputable def kG3 (k : Nat) : Bool := Nat.beq (CA (fr (14 + k)) (f2 k)) (N3G k) && ok (N3G k)

#kc_each kG2 0 7
#kc_each kG3 0 5

@[expose] noncomputable def conjIn (M P : Nat → Nat) (cnt a g x : Nat) : Bool :=
  Nat.blt (r32 P a) cnt && (Nat.beq (M a) (pc (pc g x) (pinv g)) &&
    (Nat.blt (r32 P (a + 1)) cnt && Nat.beq (M (a + 1)) (pc (pc (pinv g) x) g)))

@[expose] noncomputable def kN2 (a : Nat) : Bool := conjIn f2 F2 512 (5 + 2 * a) (RG (a / 7)) (N2G (a % 7))

@[expose] noncomputable def kN3 (a : Nat) : Bool := conjIn f3 F3 64 (2 * a) (RG (a / 5)) (N3G (a % 5))

@[expose] noncomputable def kC2 (a : Nat) : Bool :=
  Nat.blt (r32 F2 (61 + a)) 512 && Nat.beq (f2 (61 + a)) (CA (RG (a / 4)) (RG (a % 4)))

@[expose] noncomputable def kC3 (a : Nat) : Bool :=
  Nat.blt (r32 F3 (40 + a)) 64 && Nat.beq (f3 (40 + a)) (CA (N2G (a / 4)) (RG (a % 4)))

@[expose] noncomputable def kRI (j : Nat) : Bool := Nat.beq (pc (pinv (RG j)) (RG j)) e

#kc_each kN2 0 28
#kc_each kN3 0 20
#kc_each kC2 0 16
#kc_each kC3 0 28
#kc_each kRI 0 4

@[expose] noncomputable def zc (t : Nat) : Bool := allN 5 fun k => Nat.beq (pc t (N3G k)) (pc (N3G k) t)

@[expose] noncomputable def zIdx : List Nat := (List.range 64).filter fun i => zc (N3T i)

@[expose] noncomputable def kOne (s : Nat) : Bool :=
  match s with
  | 0 => Nat.beq zIdx.length 16 && zIdx.all fun i => Nat.beq (pc (N3T i) (N3T i)) e
  | 1 => (allN 3 fun i => Nat.beq (pc (QG i) (QG i)) e) &&
      ((allN 3 fun i => allN 3 fun j => Nat.beq (pc (QG i) (QG j)) (pc (QG j) (QG i))) &&
      ((allN 8 fun t => Nat.beq (pc (QT t) (QT t)) e) &&
        (allN 6 fun i => allN 3 fun j => Nat.beq (pc (QG j) (CW i)) (pc (CW i) (QG j)))))
  | 2 => lettersK 10 WA && (lettersK 10 WB &&
      (Nat.beq (wordK 1782 11 (mask 11) e sel10 (fun j => pinv (sel10 j)) WA) (TRI 0) &&
        Nat.beq (wordK 1782 11 (mask 11) e sel10 (fun j => pinv (sel10 j)) WB) (TRI 1)))
  | 3 => penumHdK e 8192 8192 RT RPL && (penumHdK e 512 512 N2T N2PL &&
      (penumHdK e 64 64 N3T N3PL && penumHdK e 8 8 QT QPL))
  | _ => true
where
  sel10 (j : Nat) : Nat := nIf(Nat.blt j 4, RG j, CW (Nat.sub j 4))

#kc_each kOne 0 4

@[expose] noncomputable def kNeg (s : Nat) : Bool :=
  match s with
  | 0 => !Nat.beq (W3 RW[1]!) (RG 0)
  | 1 => !penumPtK 1782 11 (mask 11) (1782 * 11) false RG RG 4 8192 (fun i => RT (Nat.succ i)) RPL
      RPOS RSRT RSRI 1
  | 2 => !Nat.beq (W3 RW[0]!) (RG 1)
  | 3 => !Nat.beq zIdx.length 15
  | _ => true

#kc_each kNeg 0 4

end CertificateChecks.KernelSpor.S1379101

end
