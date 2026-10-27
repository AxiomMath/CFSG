
module

public import Certificates.Kernel.SporSch.Ru.F1920
public import Certificates.Kernel.SporSch.Ru.Text1920
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Data.Kernel.SporSch.RuImg
public import CFSG.Sporadic.Schreier.RuArrays
meta import CFSG.Sporadic.Schreier.RuArrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuCe

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

meta def yM : Array Nat := ruY

meta def yposM : Array Nat := ruYPos

end CertificateChecks.KernelSporSch.RuCe

#kss_perms CertificateChecks.KernelSporSch.RuCe.KG 12 CFSG.Sporadic.RuSchreier.ruKGensA
#kss_perms CertificateChecks.KernelSporSch.RuCe.JG 12 CFSG.Sporadic.RuSchreier.ruJGensA
#kss_perms CertificateChecks.KernelSporSch.RuCe.RG 12 CFSG.Sporadic.RuSchreier.ruRGensA
#ks_perm CertificateChecks.KernelSporSch.RuCe.Y 12 CertificateChecks.KernelSporSch.RuCe.yM
#ks_perm CertificateChecks.KernelSporSch.RuCe.YPOS 12 CertificateChecks.KernelSporSch.RuCe.yposM

namespace CertificateChecks.KernelSporSch.RuCe

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def kok (i : Nat) : Bool :=
  bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 Ns0 Ns1) (gen2 Ns0I Ns1I) 2
    (dword ruKWords 0 i) (KG i), canonK 4060 12 (mask 12) (4060 * 12) (KG i))

@[expose] noncomputable def jok (i : Nat) : Bool :=
  bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 C0 C1) (gen2 C0I C1I) 2
    (dword ruJWords 0 i) (JG i), canonK 4060 12 (mask 12) (4060 * 12) (JG i))

@[expose] noncomputable def rok (i : Nat) : Bool :=
  bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) SG SGI 4 (dword ruRWords 0 i) (RG i),
    canonK 4060 12 (mask 12) (4060 * 12) (RG i))

@[expose] noncomputable def resF (G L : Nat) : Bool := resK 1920 12 11 RuF.F RuF.FPOS G (RuT1920.L L)

@[expose] noncomputable def resSj (i : Nat) : Bool := resF (SG i) (Nat.add 7 i)

@[expose] noncomputable def resKj (i : Nat) : Bool := resF (KG i) (Nat.add 14 i)

@[expose] noncomputable def resJj (i : Nat) : Bool := resF (JG i) (Nat.add 24 i)

@[expose] noncomputable def resRj (i : Nat) : Bool := resF (RG i) (Nat.add 34 i)

@[expose] noncomputable def imgCj (j : Nat) : Bool :=
  strictB (Nat.div j 2) (fun i => strictB (Nat.mod j 2) (fun g =>
    sortImgK 4060 12 (gen2 C0 C1 g) (ruCBlockList i) (ruCBlockList (ruCBlockPerms.getD g #[])[i]!)))

@[expose] noncomputable def imgNj (j : Nat) : Bool :=
  strictB (Nat.div j 2) (fun i => strictB (Nat.mod j 2) (fun g =>
    sortImgK 4060 12 (gen2 Ns0 Ns1 g) (ruNBlockList i) (ruNBlockList (ruNBlockPerms.getD g #[])[i]!)))

@[expose] noncomputable def imgJj (j : Nat) : Bool :=
  strictB (Nat.div j 6) (fun i => strictB (Nat.mod j 6) (fun k =>
    sortImgK 4060 12 (JG k) (ruCBlockList i) (ruCBlockList i)))

@[expose] noncomputable def imgKj (j : Nat) : Bool :=
  strictB (Nat.div j 8) (fun i => strictB (Nat.mod j 8) (fun k =>
    sortImgK 4060 12 (KG k) (ruNBlockList i) (ruNBlockList i)))

end CertificateChecks.KernelSporSch.RuCe

#kss_each CertificateChecks.KernelSporSch.RuCe.KC CertificateChecks.KernelSporSch.RuCe.kok 8
#kss_each CertificateChecks.KernelSporSch.RuCe.JC CertificateChecks.KernelSporSch.RuCe.jok 6
#kss_each CertificateChecks.KernelSporSch.RuCe.RC CertificateChecks.KernelSporSch.RuCe.rok 5
#kss_each CertificateChecks.KernelSporSch.RuCe.RSj CertificateChecks.KernelSporSch.RuCe.resSj 4
#kss_each CertificateChecks.KernelSporSch.RuCe.RKj CertificateChecks.KernelSporSch.RuCe.resKj 8
#kss_each CertificateChecks.KernelSporSch.RuCe.RJj CertificateChecks.KernelSporSch.RuCe.resJj 6
#kss_each CertificateChecks.KernelSporSch.RuCe.RRj CertificateChecks.KernelSporSch.RuCe.resRj 5
#kss_each CertificateChecks.KernelSporSch.RuCe.IC CertificateChecks.KernelSporSch.RuCe.imgCj 12
#kss_each CertificateChecks.KernelSporSch.RuCe.IN CertificateChecks.KernelSporSch.RuCe.imgNj 14
#kss_each CertificateChecks.KernelSporSch.RuCe.IJ CertificateChecks.KernelSporSch.RuCe.imgJj 36
#kss_each CertificateChecks.KernelSporSch.RuCe.IK CertificateChecks.KernelSporSch.RuCe.imgKj 56

namespace CertificateChecks.KernelSporSch.RuCe

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG

theorem l2 : Nat.beq (RuT4060.L 2) C0 = true := by quickRfl
theorem l3 : Nat.beq (RuT4060.L 3) C1 = true := by quickRfl
theorem l9 : Nat.beq (RuT4060.L 9) Ns0 = true := by quickRfl
theorem l10 : Nat.beq (RuT4060.L 10) Ns1 = true := by quickRfl
theorem l15 : Nat.beq (RuT4060.L 15) C0 = true := by quickRfl
theorem l16 : Nat.beq (RuT4060.L 16) C1 = true := by quickRfl
theorem l17 : Nat.beq (RuT4060.L 17) Ns0 = true := by quickRfl
theorem l18 : Nat.beq (RuT4060.L 18) Ns1 = true := by quickRfl

theorem cC0 : canonK 4060 12 (mask 12) (4060 * 12) C0 = true := by quickRfl
theorem cC1 : canonK 4060 12 (mask 12) (4060 * 12) C1 = true := by quickRfl
theorem cSG : allN 4 (fun i => canonK 4060 12 (mask 12) (4060 * 12) (SG i)) = true := by quickRfl

theorem resC0 : resF C0 0 = true := by quickRfl
theorem resC1 : resF C1 1 = true := by quickRfl

theorem yK : hexPackK 3 4060 10120 10040 80 12 Y RuPts.chars = true := by quickRfl
theorem posY : posK 4060 80 12 Y YPOS = true := by quickRfl
theorem yLt : allN 80 (fun i => Nat.blt (pg 12 (mask 12) Y i) 4060) = true := by quickRfl
theorem res80C0 : resK 80 12 7 Y YPOS C0 (RuT80.L 0) = true := by quickRfl
theorem res80C1 : resK 80 12 7 Y YPOS C1 (RuT80.L 1) = true := by quickRfl

theorem zNe : neIdK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) Z = true := by quickRfl
theorem zSq : sqIdK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) Z = true := by quickRfl
theorem zC0 : commK 4060 12 (mask 12) (4060 * 12) Z C0 = true := by quickRfl
theorem zC1 : commK 4060 12 (mask 12) (4060 * 12) Z C1 = true := by quickRfl
theorem hdC : incNL ((List.range 6).map fun i => (ruCBlockList i).headD 0) = true := by quickRfl
theorem hdN : incNL ((List.range 7).map fun i => (ruNBlockList i).headD 0) = true := by quickRfl
theorem pbC : allN 2 (fun g => allN 6 (fun i => Nat.blt (ruCBlockPerms.getD g #[])[i]! 6)) = true := by
  quickRfl
theorem pbN : allN 2 (fun g => allN 7 (fun i => Nat.blt (ruNBlockPerms.getD g #[])[i]! 7)) = true := by
  quickRfl

theorem zY : allN 80 (fun i => Nat.beq (pg 12 (mask 12) Z (pg 12 (mask 12) Y i))
    (pg 12 (mask 12) Y i)) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuCe

end
