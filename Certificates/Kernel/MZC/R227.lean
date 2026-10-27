module

public import CFSG.Certificates.Kernel.Enum.ZCV
public import CFSG.Certificates.Kernel.Enum.ZCH
public import CFSG.Certificates.Kernel.Enum.ZChkI
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Kernel.MZC.Data
public import Certificates.Kernel.MZC.Acc
public import CFSG.Certificates.Kernel.Enum.ZChk

public section

namespace CertificateChecks.MZCK.M227

open CFSG.KC.Enum CFSG.KD.M227 CFSG.KD.MZC CFSG.KS

theorem idn_eq : Nat.beq IDN (pidn 22 5) = true := by decide +kernel
theorem l_all : lRange OT 0 0 0 RO 22 5 (mask 5) (22 * 5) (mask (22 * 5)) 15 32767 NL A AI B BI 0
    NL = true := by decide +kernel
theorem z_letters : allN ZL (fun k => Nat.blt (wl ZW k) 2) = true := by decide +kernel
theorem z_word : Nat.beq (g1 Z 1) (wperm 22 5 (mask 5) A B AI BI ZW ZL) = true := by decide +kernel
theorem z_pow : zPowOK 22 5 (mask 5) (22 * 5) (g1 Z 1) (g1 Z) (g1 ZI) (7 + 1) = true := by
  decide +kernel
theorem z_p : Nat.beq (g1 Z 7) IDN = true := by decide +kernel
theorem z_ne : Nat.beq (pg 5 (mask 5) (g1 Z 1) ZP) ZP = false := by decide +kernel
theorem zp_lt : Nat.blt ZP 22 = true := by decide +kernel
theorem w_all : zRangeI OT 0 0 0 RO 22 5 (mask 5) (22 * 5) (mask (22 * 5)) 15 32767 ZW ZL (7 + 1) 0
    NX = true := by decide +kernel
theorem c_words : allN 1 (fun c =>
    bAnd(Nat.beq (g2 P1 c 1) (wperm 22 5 (mask 5) A B AI BI (g1 H1W c) (g1 H1L c)),
      Nat.beq (g2 P2 c 1) (wperm 22 5 (mask 5) A B AI BI (g1 H2W c) (g1 H2L c)))) = true := by
  decide +kernel
theorem c_pow1 : allN 1 (fun c => bAnd(Nat.blt 0 (g1 O1 c), bAnd(zPowOK 22 5 (mask 5) (22 * 5)
    (g2 P1 c 1) (g2 P1 c) (g2 P1I c) (Nat.succ (g1 O1 c)), Nat.beq (g2 P1 c (g1 O1 c)) IDN))) =
    true := by decide +kernel
theorem c_pow2 : allN 1 (fun c => bAnd(Nat.blt 0 (g1 O2 c), bAnd(zPowOK 22 5 (mask 5) (22 * 5)
    (g2 P2 c 1) (g2 P2 c) (g2 P2I c) (Nat.succ (g1 O2 c)), Nat.beq (g2 P2 c (g1 O2 c)) IDN))) =
    true := by decide +kernel
theorem c_comm : allN 1 (fun c => bIf(eq22 22 5 (mask 5) (g2 P1 c 1) (g2 P2 c 1) (g2 P2 c 1)
    (g2 P1 c 1), false, true)) = true := by decide +kernel
theorem c_enum : allN 1 (fun c => hRange (hTo HT HO c) 0 0 0 RH 22 5 (mask 5) (22 * 5)
    (mask (22 * 5)) (g1 NH c) IDN (g2 P1 c 1) (g2 P2 c 1) (len2 REPS c) (g2 REPS c) (g1 NH c)) =
    true := by decide +kernel
theorem c_nh : allN 1 (fun c => bAnd(Nat.blt 0 (g1 NH c), bAnd(Nat.blt (len2 REPS c) 15,
    allN (len2 REPS c) (fun i => Nat.blt (g2 REPS c i) (g1 NH c))))) = true := by decide +kernel
theorem c_nc : allN 1 (fun c => allN (len2 REPS c) (fun i =>
    bAnd(ncOK (hTo HT HO c) 0 0 0 RH 22 5 (mask 5) (22 * 5) (mask (22 * 5)) (g1 NH c) (g2 P1 c 1) i
      (g3 NC1 c i),
    ncOK (hTo HT HO c) 0 0 0 RH 22 5 (mask 5) (22 * 5) (mask (22 * 5)) (g1 NH c) (g2 P2 c 1) i
      (g3 NC2 c i)))) = true := by decide +kernel
theorem c_k3 : allN 1 (fun c => bAnd(Nat.blt (g1 K3 c) (g1 NH c), bAnd(Nat.blt (g1 K3P c) 22,
    bAnd(eq3 22 5 (mask 5) IDN (rperm (hTo HT HO c) 0 0 0 RH (mask (22 * 5)) (g1 K3 c))
      (rperm (hTo HT HO c) 0 0 0 RH (mask (22 * 5)) (g1 K3 c))
      (rperm (hTo HT HO c) 0 0 0 RH (mask (22 * 5)) (g1 K3 c)),
    bIf(Nat.beq (pg 5 (mask 5) (rperm (hTo HT HO c) 0 0 0 RH (mask (22 * 5)) (g1 K3 c))
      (g1 K3P c)) (g1 K3P c), false, true))))) = true := by decide +kernel
theorem c_kz : allN 1 (fun c => bAnd(Nat.blt (g1 KZ c) (g1 NH c),
    Nat.beq (rperm (hTo HT HO c) 0 0 0 RH (mask (22 * 5)) (g1 KZ c)) (g1 Z 1))) = true := by
  decide +kernel
theorem c_v : allN 1 (fun c => bAnd(
    vRangeS OT 0 0 0 RO 22 5 (mask 5) (mask (22 * 5)) (g1 Z) (g1 ZI) (g1 VP) (g1 VC1) (g2 P1 c 1)
      (g2 P1I c 1) 7 (g1 XC c) (Nat.add NX (g1 XC c)) (g1 XN c),
    vRangeS OT 0 0 0 RO 22 5 (mask 5) (mask (22 * 5)) (g1 Z) (g1 ZI) (g1 VP) (g1 VC2) (g2 P2 c 1)
      (g2 P2I c 1) 7 (g1 XC c) (Nat.add NX (g1 XC c)) (g1 XN c))) = true := by decide +kernel
theorem c_cov : allN (Nat.sub NL NX) (fun t => (List.range 1).any (fun c =>
    Nat.ble (g1 XC c) t && Nat.blt t (Nat.add (g1 XC c) (g1 XN c)))) = true := by decide +kernel
theorem syl_gens : allN 3 (fun j => Nat.beq (g1 G j)
    (wperm 22 5 (mask 5) A B AI BI (g1 SW j) (g1 SL j))) = true := by decide +kernel
theorem s_all : sRange ET 0 0 0 RE 22 5 (mask 5) (22 * 5) (mask (22 * 5)) 15 32767 NS IDN (g1 G) 3
    true OT 0 0 0 RO NL false 0 (fun _ => 0) 0 (fun _ => 0) 0 0 NS = true := by decide +kernel
theorem nS_eq : Nat.beq NS 128 = true := by decide +kernel

end CertificateChecks.MZCK.M227

end
