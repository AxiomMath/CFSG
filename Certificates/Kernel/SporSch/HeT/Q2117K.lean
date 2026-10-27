module

public import Certificates.Kernel.SporSch.Mathieu.GenChainCls
public meta import Certificates.Kernel.SporSch.Mathieu.GenChainCls
public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.LocalQT.He4148.Glue
public import Certificates.Data.Kernel.HeFixK
public import CFSG.Sporadic.HeldB.OuterCentCheckInputs
public meta import CFSG.Sporadic.HeldB.OuterCentCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeQ17

open CFSG.KS.SporSch.MOCG CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB

meta def sigM : Array (Array Nat) := #[heSigma1, heSigma2]

meta def SQC : Array (Array Nat) := strongOf 98 sigM heQCWords

meta def baseQC : Array Nat := #[0, 1, 6, 3]

meta def tauM : Array (Array Nat) := #[heTauArr 0, heTauArr 1, heTauArr 2]

meta def SQD : Array (Array Nat) := strongOf 98 tauM heQDWords

meta def baseQD : Array Nat := #[0, 1, 3, 6]

meta def SQE : Array (Array Nat) := strongOf 98 #[heEpsArr 0, heEpsArr 1] heQEWords

meta def SQY : Array (Array Nat) := strongOf 35 heUpsilon.toArray heQYWords

meta def baseQY : Array Nat := #[0, 1, 3, 2]

meta def zM : Array (Array Nat) := #[heZ, invCand 98 heZ]

end CertificateChecks.KernelSporSch.HeQ17

#ks_rawchain CertificateChecks.KernelSporSch.HeQ17.QC 98 7 16 CertificateChecks.KernelSporSch.HeQ17.SQC
  CertificateChecks.KernelSporSch.HeQ17.baseQC 2 CFSG.Sporadic.HeldB.heQCWords

#ks_rawchain CertificateChecks.KernelSporSch.HeQ17.QD 98 7 16 CertificateChecks.KernelSporSch.HeQ17.SQD
  CertificateChecks.KernelSporSch.HeQ17.baseQD 3 CFSG.Sporadic.HeldB.heQDWords

#ks_rawchain CertificateChecks.KernelSporSch.HeQ17.QE 98 7 16 CertificateChecks.KernelSporSch.HeQ17.SQE
  CertificateChecks.KernelSporSch.HeQ17.baseQD 2 CFSG.Sporadic.HeldB.heQEWords

#ks_rawchain CertificateChecks.KernelSporSch.HeQ17.QY 35 6 16 CertificateChecks.KernelSporSch.HeQ17.SQY
  CertificateChecks.KernelSporSch.HeQ17.baseQY 3 CFSG.Sporadic.HeldB.heQYWords

#kss_perms CertificateChecks.KernelSporSch.HeQ17.ZP 7 CertificateChecks.KernelSporSch.HeQ17.zM

#kss_list CertificateChecks.KernelSporSch.HeQ17.FZ CFSG.Sporadic.HeldB.heFixZ

namespace CertificateChecks.KernelSporSch.HeQ17

meta def QDCsrc : Array Nat := CFSG.KS.SporSch.ChainClsG.commCounts 98 SQD baseQD tauM 2048

end CertificateChecks.KernelSporSch.HeQ17

#kss_list CertificateChecks.KernelSporSch.HeQ17.QDC.CS CertificateChecks.KernelSporSch.HeQ17.QDCsrc

namespace CertificateChecks.KernelSporSch.HeQ17

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CFSG.KS.SporSch.ChainCls

@[expose] noncomputable def QDC.cntB (s : Nat) : Bool :=
  Nat.beq (commCntK 98 7 (mask 7) (98 * 7) (pidn 98 7) QD.LR QD.TR 4 QD.S 3 (ordK QD.LR 4)
    (s * 2048) 2048) (QDC.CS.getD s 0)

end CertificateChecks.KernelSporSch.HeQ17

#kss_each CertificateChecks.KernelSporSch.HeQ17.QDC.E CertificateChecks.KernelSporSch.HeQ17.QDC.cntB 4

namespace CertificateChecks.KernelSporSch.HeQ17

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu CFSG.KS.SporSch.MOC
open CFSG.Sporadic.HeldB CertificateChecks.KernelLQT.He4148

@[expose] noncomputable def Z : Nat := ZP 0

noncomputable abbrev pc (p q : Nat) : Nat := pcomp 98 7 (mask 7) p q

@[expose] noncomputable def tauK (j : Nat) : Bool :=
  bAnd(wordEqK 98 7 (mask 7) (pidn 98 7) QC.S QC.SI 2 (heDerivedV.getD j []) (QD.S j),
  bAnd(invEqK 98 7 (mask 7) (98 * 7) (QD.S j) (QD.SI j),
  bAnd(invEqK 98 7 (mask 7) (98 * 7) (QD.SI j) (QD.S j),
  bAnd(canonK 98 7 (mask 7) (98 * 7) (QD.S j), canonK 98 7 (mask 7) (98 * 7) (QD.SI j)))))

@[expose] noncomputable def epsK (i : Nat) : Bool :=
  bAnd(Nat.beq (pc (QD.S i) (pc (QD.S 2) (pc (QD.SI i) (QD.SI 2)))) (QE.S i),
  bAnd(invEqK 98 7 (mask 7) (98 * 7) (QE.S i) (QE.SI i),
    invEqK 98 7 (mask 7) (98 * 7) (QE.SI i) (QE.S i)))

theorem bQC : bindsK 98 7 QC.S QC.SI [heSigma1, heSigma2] 0 = true := by quickRfl

theorem bQY : bindsK 35 6 QY.S QY.SI heUpsilon 0 = true := by quickRfl

theorem bZ : bindsK 98 7 ZP (fun _ => ZP 1) [heZ] 0 = true := by quickRfl

theorem kO : bAnd(Nat.beq (ordK QC.LR 4) 15120, bAnd(Nat.beq (ordK QD.LR 4) 7560,
    bAnd(Nat.beq (ordK QE.LR 4) 7560, Nat.beq (ordK QY.LR 4) 2520))) = true := by quickRfl

theorem kTau : allN 3 tauK = true := by quickRfl

theorem kEps : allN 2 epsK = true := by quickRfl

theorem kP : allN 2 (fun j => permOK 98 7 (mask 7) (98 * 7) (QC.S j) (QC.SI j)) = true := by
  quickRfl

theorem kZ : bAnd(siftK 98 7 (mask 7) (98 * 7) (pidn 98 7) QD.LR QD.TRI QD.BP 4 0 Z,
    bAnd(allN 3 (fun j => Nat.beq (pc Z (QD.S j)) (pc (QD.S j) Z)),
    bAnd(neIdK 98 7 (mask 7) (98 * 7) (pidn 98 7) Z,
    bAnd(Nat.beq (pc Z (pc Z Z)) (pidn 98 7),
    bAnd(idK 98 7 (mask 7),
    bAnd(canonK 98 7 (mask 7) (98 * 7) (pidn 98 7),
    bAnd(Nat.beq (CFSG.KC.HeFixK.fixK 98 7 Z) 35,
    allN 35 (fun k => Nat.beq (pg 7 (mask 7) Z (nget FZ k)) (nget FZ k))))))))) = true := by
  quickRfl

theorem kU : allN 3 (fun j => allN 35 (fun k => Nat.beq (pg 7 (mask 7) (QD.S j) (nget FZ k))
    (nget FZ (pg 6 (mask 6) (QY.S j) k)))) = true := by quickRfl

theorem kF : heFixZ.toList = FZ ∧ FZ.length = 35 ∧ (∀ x ∈ FZ, x < 98) ∧
    ∀ k < 35 - 1, nget FZ k < nget FZ (k + 1) := by decide +kernel

theorem kC : bAnd(Nat.ble (ordK QD.LR 4) (Nat.mul QDC.CS.length 2048), Nat.beq QDC.CS.sum 3) =
    true := by quickRfl

end CertificateChecks.KernelSporSch.HeQ17

end
