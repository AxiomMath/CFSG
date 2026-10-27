module

public import Certificates.Kernel.MaxD2.HSU35.Data
public import Certificates.Kernel.MaxD2.HSW0.Data
public import Certificates.Kernel.MaxD2.HSP.Enum
public import Certificates.Kernel.MaxD2.HSP.Data
public import Certificates.Kernel.MaxD2.HSU.Enum
public import Certificates.Kernel.MaxD2.HSU.Data
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.HSFiveU35Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.HSU35

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.HSOver Certificates.HSU35

@[expose] noncomputable def uaL (l : Nat) : Nat :=
  nIf(Nat.blt l 2, HSU.RE.G l, nIf(Nat.blt l 4, HSP.NE.G l, HSW0.PW 2))

@[expose] noncomputable def uaLI (l : Nat) : Nat :=
  QT (Nat.add l 2)

@[expose] noncomputable def wdK : Bool :=
  wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverTW (HSU.TT 0) &&
  (wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverWW (HSU.REP 1) &&
  (wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverCW (QT 0) &&
  (wordEqK 100 7 (mask 7) (pidn 100 7) HSU.GP HSU.GPI 2 xyCW (QT 0) &&
  (permOK 100 7 (mask 7) (100 * 7) (QT 0) (QT 1) &&
  (wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverE1W (EE.G 0) &&
  (wordEqK 100 7 (mask 7) (pidn 100 7) HSU.GP HSU.GPI 2 xyE1W (EE.G 0) &&
  (wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverE2W (EE.G 1) &&
  (wordEqK 100 7 (mask 7) (pidn 100 7) HSU.GP HSU.GPI 2 xyE2W (EE.G 1) &&
  allN 2 (fun j => canonK 100 7 (mask 7) (100 * 7) (EE.G j))))))))))

@[expose] noncomputable def ordK : Bool :=
  Nat.beq (pw 100 7 (HSU.GP 0) 8) (pidn 100 7) &&
  (!(Nat.beq (pw 100 7 (HSU.GP 0) 4) (pidn 100 7)) &&
  (Nat.beq (pw 100 7 (HSU.GP 1) 3) (pidn 100 7) &&
  (!(Nat.beq (HSU.GP 1) (pidn 100 7)) &&
  (Nat.beq (pw 100 7 (pcomp 100 7 (mask 7) (HSU.GP 0) (HSU.GP 1)) 7) (pidn 100 7) &&
  (!(Nat.beq (pcomp 100 7 (mask 7) (HSU.GP 0) (HSU.GP 1)) (pidn 100 7)) &&
  (Nat.beq (pw 100 7 (HSU.TT 0) 8) (pidn 100 7) &&
  !(Nat.beq (pw 100 7 (HSU.TT 0) 4) (pidn 100 7))))))))

@[expose] noncomputable def tcK : Bool :=
  allN HSU.RE.cnt fun k =>
    !(Nat.beq (pcomp 100 7 (mask 7) (HSU.TT 0) (HSU.RE.T k))
      (pcomp 100 7 (mask 7) (HSU.RE.T k) (HSU.TT 0))) || Nat.beq (HSU.RE.T k) (pidn 100 7)

@[expose] noncomputable def wK : Bool :=
  notInK HSU.NE.cnt HSU.NE.T (HSU.REP 1) &&
  (Nat.blt (r32 QH 0) 8 &&
  Nat.beq (pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (HSU.REP 1) (HSU.TT 0)) (HSU.REPI 1))
    (pw 100 7 (HSU.TT 0) (r32 QH 0)))

@[expose] noncomputable def kerK : Bool :=
  allN HSU.NE.cnt fun k =>
    bIf(Nat.beq (Nat.land (r32 HSU.H (Nat.add (Nat.mul HSU.NE.cnt 1) k)) 1) 1,
      Nat.beq (HSU.NE.T k) (pidn 100 7) ||
        notInK HSU.NE.cnt HSU.NE.T
          (pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (QT 1) (HSU.NE.T k)) (QT 0)),
      true)

@[expose] noncomputable def e9K : Bool :=
  penumHdK (pidn 100 7) EE.cnt 9 EE.T EE.PL &&
  (penumSlK 100 7 (mask 7) (100 * 7) false EE.G EE.GI EE.k EE.cnt EE.T EE.PL EE.POS EE.SRT EE.SRI 0
    9 &&
  (Nat.beq EE.cnt 9 &&
  (allN 9 (fun i => allN 9 fun j => Nat.beq (pcomp 100 7 (mask 7) (EE.T i) (EE.T j))
    (pcomp 100 7 (mask 7) (EE.T j) (EE.T i))) &&
  allN 9 fun i => Nat.beq (pw 100 7 (EE.T i) 3) (pidn 100 7))))

@[expose] noncomputable def uaK : Bool :=
  allN 5 (fun l => permOK 100 7 (mask 7) (100 * 7) (uaL l) (uaLI l)) &&
  (wordEqK 100 7 (mask 7) (pidn 100 7) uaL uaLI 5 uaXW (HSU.GP 0) &&
  wordEqK 100 7 (mask 7) (pidn 100 7) uaL uaLI 5 uaYW (HSU.GP 1))

theorem k_wd : wdK = true := by quickRfl
theorem k_ord : ordK = true := by quickRfl
theorem k_tc : tcK = true := by quickRfl
theorem k_w : wK = true := by quickRfl
theorem k_ker : kerK = true := by quickRfl
theorem k_e9 : e9K = true := by quickRfl
theorem k_ua : uaK = true := by quickRfl

end CertificateChecks.KernelMaxD2.HSU35

end
