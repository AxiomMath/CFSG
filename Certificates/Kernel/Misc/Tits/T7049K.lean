
module

public import Certificates.Kernel.Misc.Tits.Cls7050D
public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.SporSch.Tits.Common
public import Certificates.Kernel.SporSch.Tits.Action2262
public import Certificates.Data.Kernel.Misc.ClosK
public import CFSG.Quasithin.Recognition.RuRank3Tits13Inputs
public meta import CFSG.Quasithin.Recognition.RuRank3Tits13Inputs
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.TP3 CFSG.Quasithin.RuRank3.titsP3Text
#kmisc_hexflat CertificateChecks.KernelMisc.TP3 CFSG.Quasithin.RuRank3.titsP3Text 3 1755 11 3
#ks_chars CertificateChecks.KernelMisc.TP5 CFSG.Quasithin.RuRank3.titsP5Text
#kmisc_hexflat CertificateChecks.KernelMisc.TP5 CFSG.Quasithin.RuRank3.titsP5Text 3 1755 11 2

namespace CertificateChecks.KernelMisc.T7049

meta def baseM : Array Nat := CFSG.Sporadic.RuSchreier.ruBaseArr 1755 [0]

meta def cl3M : Array (Array Nat) :=
  CFSG.Quasithin.RuRank3.closureList 1755 CFSG.Quasithin.RuRank3.titsP3Gens 30
meta def cl5M : Array (Array Nat) :=
  CFSG.Quasithin.RuRank3.closureList 1755 CFSG.Quasithin.RuRank3.titsP5Gens 30

@[expose] public def noWords : List (List Int) := []

end CertificateChecks.KernelMisc.T7049

#ks_rawchain_sl2 CertificateChecks.KernelMisc.T7049P3C 1755 11 2 8 0
  CFSG.Quasithin.RuRank3.titsP3Gens CertificateChecks.KernelMisc.T7049.baseM 3
  CertificateChecks.KernelMisc.T7049.noWords
#ks_rawchain_sl2 CertificateChecks.KernelMisc.T7049P5C 1755 11 2 8 0
  CFSG.Quasithin.RuRank3.titsP5Gens CertificateChecks.KernelMisc.T7049.baseM 2
  CertificateChecks.KernelMisc.T7049.noWords
#ks_perm CertificateChecks.KernelMisc.T7049LP 11 CFSG.Sporadic.Schreier.Tits.titsLinePtArr
#kmisc_packarrs CertificateChecks.KernelMisc.T7049CL3 CertificateChecks.KernelMisc.T7049.cl3M 11
#kmisc_packarrs CertificateChecks.KernelMisc.T7049CL5 CertificateChecks.KernelMisc.T7049.cl5M 11

public section

namespace CertificateChecks.KernelMisc.T7049

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.ClosK CertificateChecks.KernelMisc
  CertificateChecks.KernelMisc.Tits7050 CertificateChecks.KernelSpor.Tits2264
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsAction

@[expose] noncomputable def pt (P i : Nat) : Nat := pg 11 (mask 11) P i

@[expose] noncomputable def LPf (i : Nat) : Nat := pg 11 (mask 11) T7049LP i

@[expose] noncomputable def lfixK (P v : Nat) : Bool :=
  (List.range 3).all fun k =>
    Nat.beq (pt P (LPf (3 * v + k))) (LPf (3 * v)) ||
      Nat.beq (pt P (LPf (3 * v + k))) (LPf (3 * v + 1)) ||
      Nat.beq (pt P (LPf (3 * v + k))) (LPf (3 * v + 2))

@[expose] noncomputable def lfc (P : Nat) : Nat := (List.range 2925).countP (lfixK P)

@[expose] noncomputable def pfc (P : Nat) : Nat := (List.range 1755).countP fun x => Nat.beq (pt P x) x

@[expose] noncomputable def lmem (T : Nat → Nat) (m x : Nat) : Bool :=
  (List.range m).any fun j => Nat.beq (T j) x

@[expose] noncomputable def closedK (T G : Nat → Nat) (ng m : Nat) : Bool :=
  bAnd(lmem T m (pidn 1755 11), allN ng fun k => allN m fun i =>
    bAnd(lmem T m (pc (G k) (T i)), lmem T m (pc (pinvS 1755 11 (mask 11) (G k)) (T i))))

theorem kLP : allN 8775 (fun i => Nat.beq (LPf i) (lpK i)) = true := by quickRfl

theorem sOK3 : allN 3 (fun j => Nat.beq (T7049P3C.S j) (TP3.F j)) = true := by quickRfl
theorem sOK5 : allN 2 (fun j => Nat.beq (T7049P5C.S j) (TP5.F j)) = true := by quickRfl
theorem baseOK : bAnd(Nat.beq (pg 11 (mask 11) T7049P3C.BP 0) 0,
    Nat.beq (pg 11 (mask 11) T7049P5C.BP 0) 0) = true := by quickRfl

theorem kPerm : bAnd(allN 3 (fun j => permC (TP3.F j)), allN 2 (fun j => permC (TP5.F j))) = true := by
  quickRfl

theorem kSift : bAnd(siftD X, bAnd(allN 3 (fun j => siftD (TP3.F j)),
    allN 2 (fun j => siftD (TP5.F j)))) = true := by
  quickRfl

theorem kX : bAnd(Nat.beq (pw X 13) (pidn 1755 11), bAnd(bIf(Nat.beq X (pidn 1755 11), false, true),
    bAnd(Nat.beq (pfc X) 0, Nat.beq (lfc X) 0))) = true := by
  quickRfl

theorem kCnt : bAnd(Nat.beq (rcnt (T7049P3C.LR 0)) 27, Nat.beq (rcnt (T7049P5C.LR 0)) 25) = true := by
  quickRfl

theorem kZT : bAnd(Nat.beq (lfc TitsZ) 45, Nat.beq (lfc TitsT) 61) = true := by quickRfl

theorem kCl3 : lEq T7049CL3 (closK pc TP3.F 3 30 ([pidn 1755 11], 0)).1 0 27 = true := by quickRfl

theorem kCl5 : lEq T7049CL5 (closK pc TP5.F 2 30 ([pidn 1755 11], 0)).1 0 25 = true := by quickRfl

theorem kClosed3 : closedK T7049CL3 TP3.F 3 27 = true := by quickRfl

theorem kClosed5 : closedK T7049CL5 TP5.F 2 25 = true := by quickRfl

theorem kLines3 : allN 27 (fun j => bIf(Nat.beq (T7049CL3 j) (pidn 1755 11), true,
    Nat.beq (lfc (T7049CL3 j)) 9)) = true := by
  quickRfl

theorem kPts5 : allN 25 (fun j => bIf(Nat.beq (T7049CL5 j) (pidn 1755 11), true,
    Nat.beq (pfc (T7049CL5 j)) 5)) = true := by
  quickRfl

theorem neg : bAnd(bIf(Nat.beq (lfc (TP3.F 0)) 8, false, true), bAnd(bIf(siftD Aux, false, true),
    bAnd(bIf(lEq T7049CL3 (closK pc TP3.F 1 30 ([pidn 1755 11], 0)).1 0 27, false, true),
      bIf(lEq (fun j => T7049CL5 (j + 1)) (closK pc TP5.F 2 30 ([pidn 1755 11], 0)).1 0 25, false,
        true)))) = true := by
  quickRfl

end CertificateChecks.KernelMisc.T7049

end
