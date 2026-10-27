module

public import Certificates.Kernel.SporSch.HN.PtC
public import Certificates.Kernel.SporSch.HN.Pt2086Data
public import Certificates.Kernel.SporSch.HN.Pt15020Data
public import Certificates.Kernel.Sporadic.OddCore.HNT4D
public import Certificates.Kernel.Sporadic.OddCore.HN2088D
public import Certificates.Kernel.LocalQT.Tc.Gen
public import Certificates.Data.Kernel.SporSch.HNXT4
public import Certificates.Data.Kernel.Spor.EnumBase
public import Certificates.Data.Kernel.Spor.HNAOrb
public import CFSG.Certificates.Kernel.Local.HN.X.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt15020

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KC.LL.HNXT4 CFSG.KS.SporSch CFSG.KS.HNA
open CFSG.KS.EnumBase CFSG.KD.HNPt15020 CFSG.KD.LgHNX CertificateChecks.KernelSpor

@[expose] noncomputable def at0 (l : List Nat) (i : Nat) : Nat := l.getD i (nat_lit 0)

@[expose] noncomputable def MX (m : Nat) : Nat :=
  nIf(Nat.blt m (nat_lit 14), CFSG.KD.HNPt2086.WT m,
    nIf(Nat.blt m (nat_lit 23), at0 CM (Nat.sub m (nat_lit 14)), at0 CIM (Nat.sub m (nat_lit 23))))

@[expose] noncomputable def codesAt (s L : Nat) : List Nat :=
  (listUp (fun t => HNT4T.QN (Nat.add s t)) L).map fun x => Nat.sub x (nat_lit 12)

@[expose] noncomputable def mt (f : Nat) : Bool :=
  strictB (HNT4T.QP f) fun s => strictB (HNT4T.QN s) fun l1 =>
  bAnd(eqNL (uc.getD f []) (codesAt (Nat.succ s) l1),
  bAnd(eqNL (vc.getD f []) (codesAt (Nat.add (Nat.add s (nat_lit 2)) l1)
      (HNT4T.QN (Nat.add (Nat.succ s) l1))),
  bAnd(Nat.beq (wordC CFSG.KD.HNPtC.GT (uc.getD f [])) (at0 UM f),
  bAnd(Nat.beq (wordC CFSG.KD.HNPtC.GT (vc.getD f [])) (at0 VM f),
  bAnd(validHN (at0 UIM f), bAnd(validHN (at0 VIM f), bAnd(validHN (at0 CIM f),
  bAnd(Nat.beq (HN.mm (at0 UM f) (at0 UIM f)) CFSG.KD.OrdHN.ONE,
  bAnd(Nat.beq (HN.mm (at0 VM f) (at0 VIM f)) CFSG.KD.OrdHN.ONE,
  bAnd(Nat.beq (HN.mm (HN.mm (HN.mm (at0 UM f) (at0 VM f)) (at0 UIM f)) (at0 VIM f)) (at0 CM f),
    Nat.beq (HN.mm (at0 CM f) (at0 CIM f)) CFSG.KD.OrdHN.ONE))))))))))

@[expose] noncomputable def ch (c : Nat) : Bool :=
  chunkK TX MS CM3 M MX (at0 FL) (at0 IL) (at0 MI) (at0 NC) c

@[expose] noncomputable def fc (s : Nat) : Bool :=
  sliceK 2620 64 (factK HPE.PL (at0 FL) (at0 IL) (at0 MI) (at0 NC) 63 FR FX FY FP FS) s

theorem faK : allN 135 (faithK (at0 FL) (at0 IL) (at0 MI) (at0 NC) 63 2620 FR FX FY AK AF AQ AS AB) =
    true := by quickRfl

theorem niK : allN 120 (noInvK 2620 FR FX FY NK NQ NB) = true := by quickRfl

@[expose] noncomputable def mp (s : Nat) : Bool :=
  sliceK 16384 64 (mapK HNT4T.WN HNT4T.WP 135 120 AK AF AQ NK NQ TK) s

theorem neg_mt : Bool.not (Nat.beq (wordC CFSG.KD.HNPtC.GT (uc.getD 1 [])) (at0 UM 0)) = true := by
  quickRfl
theorem neg_ch : Bool.not (chunkK TX MS CM3 M MX (at0 FL) (at0 FL) (at0 MI) (at0 NC) 0) = true := by
  quickRfl
theorem neg_fc : Bool.not (factK HPE.PL (at0 FL) (at0 IL) (at0 MI) (at0 NC) 63 FR FY FY FP FS 5) =
    true := by quickRfl
theorem neg_fa : Bool.not (faithK (at0 FL) (at0 IL) (at0 MI) (at0 NC) 63 2620 FR FX FY AK AF AQ AB AB
    0) = true := by quickRfl
theorem neg_ni : Bool.not (noInvK 2620 FR FX FY NK NQ AB 0) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNPt15020

set_option Elab.async false

#kqb_range CertificateChecks.KernelSporSch.HNPt15020.mtK CertificateChecks.KernelSporSch.HNPt15020.mt 0 9
#kqb_all CertificateChecks.KernelSporSch.HNPt15020.mtK CertificateChecks.KernelSporSch.HNPt15020.mt 9
#kqb_range CertificateChecks.KernelSporSch.HNPt15020.chK CertificateChecks.KernelSporSch.HNPt15020.ch 0 63
#kqb_all CertificateChecks.KernelSporSch.HNPt15020.chK CertificateChecks.KernelSporSch.HNPt15020.ch 63
#kqb_range CertificateChecks.KernelSporSch.HNPt15020.fcK CertificateChecks.KernelSporSch.HNPt15020.fc 0 41
#kqb_all CertificateChecks.KernelSporSch.HNPt15020.fcK CertificateChecks.KernelSporSch.HNPt15020.fc 41
#kqb_range CertificateChecks.KernelSporSch.HNPt15020.mpK CertificateChecks.KernelSporSch.HNPt15020.mp 0 256
#kqb_all CertificateChecks.KernelSporSch.HNPt15020.mpK CertificateChecks.KernelSporSch.HNPt15020.mp 256

end
