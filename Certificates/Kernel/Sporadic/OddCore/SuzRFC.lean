module

public import Certificates.Kernel.Sporadic.OddCore.SuzRFM
public import Certificates.Kernel.Sporadic.OddCore.SuzRFO3a
public import Certificates.Kernel.Sporadic.OddCore.SuzRFO3b
public import Certificates.Kernel.Sporadic.OddCore.SuzRFO3c
public import Certificates.Kernel.Sporadic.OddCore.SuzRFO3d
public import Certificates.Kernel.Sporadic.OddCore.SuzRFO3e
public import Certificates.Kernel.Sporadic.OddCore.SuzRFO3f
public import Certificates.Kernel.Sporadic.OddCore.SuzRFO3g
public import Certificates.Kernel.Sporadic.OddCore.SuzRFO3h
public import Certificates.Kernel.Sporadic.OddCore.SuzRFSa
public import Certificates.Kernel.Sporadic.OddCore.SuzRFSb
public import Certificates.Kernel.Sporadic.OddCore.SuzRFSc
public import Certificates.Kernel.Sporadic.OddCore.SuzRFSd
public import Certificates.Kernel.Sporadic.OddCore.SuzRFSe
public import Certificates.Kernel.Sporadic.OddCore.SuzRFSf
public import Certificates.Kernel.Sporadic.OddCore.SuzRFSg
public import Certificates.Kernel.Sporadic.OddCore.SuzRFSh
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.SuzRF.oSl0All CertificateChecks.KernelSpor.SuzRF.oSl0 1
#kon_join CertificateChecks.KernelSpor.SuzRF.oSl1All CertificateChecks.KernelSpor.SuzRF.oSl1 9
#kon_join CertificateChecks.KernelSpor.SuzRF.oSl2All CertificateChecks.KernelSpor.SuzRF.oSl2 60
#kon_join CertificateChecks.KernelSpor.SuzRF.oSl3All CertificateChecks.KernelSpor.SuzRF.oSl3 1080
#kon_join CertificateChecks.KernelSpor.SuzRF.sSlAll CertificateChecks.KernelSpor.SuzRF.sSl 1024
#kon_join CertificateChecks.KernelSpor.SuzRF.wSlAll CertificateChecks.KernelSpor.SuzRF.wSl 256
#kon_join CertificateChecks.KernelSpor.SuzRF.pSlAll CertificateChecks.KernelSpor.SuzRF.pSl 32
#kon_join CertificateChecks.KernelSpor.SuzRF.genKAll CertificateChecks.KernelSpor.SuzRF.genK 10

namespace CertificateChecks.KernelSpor.SuzRF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzMGF
  CertificateChecks.KernelSpor.SuzC1EG

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "Id" => pidn 1782 11
local notation "T1" => SuzInvT1.F 0

theorem kHd0 : penumHdK SuzRFO0.R SuzRFO0.cnt 1 SuzRFO0.T SuzRFO0.PL = true := by quickRfl

theorem kHd1 : penumHdK SuzRFO1.R SuzRFO1.cnt 54 SuzRFO1.T SuzRFO1.PL = true := by quickRfl

theorem kHd2 : penumHdK SuzRFO2.R SuzRFO2.cnt 360 SuzRFO2.T SuzRFO2.PL = true := by quickRfl

theorem kHd3 : penumHdK SuzRFO3.R SuzRFO3.cnt 6480 SuzRFO3.T SuzRFO3.PL = true := by quickRfl

theorem kHdS : penumHdK Id SuzRFS.cnt 8192 SuzRFS.T SuzRFS.PL = true := by quickRfl

theorem kB0 : bindO SuzRFO0.R SuzRFO0.G SuzRFO0.GI 0 = true := by quickRfl

theorem kB1 : bindO SuzRFO1.R SuzRFO1.G SuzRFO1.GI 1 = true := by quickRfl

theorem kB2 : bindO SuzRFO2.R SuzRFO2.G SuzRFO2.GI 2 = true := by quickRfl

theorem kB3 : bindO SuzRFO3.R SuzRFO3.G SuzRFO3.GI 3 = true := by quickRfl

theorem kInv0 : allN 2 (fun j => Nat.beq (pc (SuzRFO0.GI j) (SuzRFO0.G j)) Id) = true := by
  quickRfl

theorem kInv1 : allN 2 (fun j => Nat.beq (pc (SuzRFO1.GI j) (SuzRFO1.G j)) Id) = true := by
  quickRfl

theorem kInv2 : allN 2 (fun j => Nat.beq (pc (SuzRFO2.GI j) (SuzRFO2.G j)) Id) = true := by
  quickRfl

theorem kInv3 : allN 2 (fun j => Nat.beq (pc (SuzRFO3.GI j) (SuzRFO3.G j)) Id) = true := by
  quickRfl

theorem kBS : allN 4 (fun j => Nat.beq (SuzRFS.G j) (sK j)) = true := by quickRfl

theorem kCnt : SuzRFO0.cnt = 1 ∧ SuzRFO1.cnt = 54 ∧ SuzRFO2.cnt = 360 ∧ SuzRFO3.cnt = 6480 ∧
    SuzRFS.cnt = 8192 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem kSel : selFrom (fun k => Nat.beq (wg SuzRFWV k) 0) 8192 0 SuzRFV = true := by quickRfl

theorem kVLen : SuzRFV.length = 512 := by decide +kernel

theorem kAnyLt : Nat.blt (CFSG.KS.Mathieu.nget SuzRFA 0) 512 = true := by quickRfl

theorem kAny : Nat.beq (p4 (VT (CFSG.KS.Mathieu.nget SuzRFA 0))) T1 = true := by quickRfl

@[expose] noncomputable def fixN (i : Nat) : Nat := nIf(Nat.beq i 3, 42, 54)

theorem kReps : allN 4 (fun i => strictB (lamK i) fun X => bAnd(Nat.beq (pc X X) Id,
    bAnd(Bool.not (Nat.beq X Id), Nat.beq (OddCore.fixCntK 1782 11 (mask 11) X) (fixN i)))) =
    true := by
  quickRfl

theorem kQ1 : Nat.beq (pc (qProdK 4) (qProdK 4)) Id = true := by quickRfl

theorem kQ2 : Nat.beq (pc (qProdK 8) (qProdK 8)) Id = true := by quickRfl

theorem kQ3 : Nat.beq (pc (qProdK 4) (lamK 1)) (pc (lamK 1) (qProdK 4)) = true := by quickRfl

theorem kQ4 : Nat.beq (pc (qProdK 8) (lamK 1)) (pc (lamK 1) (qProdK 8)) = true := by quickRfl

theorem kQ5 : Nat.beq (pc (pc (pc (qProdK 4) (qProdK 8)) (qProdK 4)) (qProdK 8)) T1 = true := by
  quickRfl

theorem negO3 : Bool.not (penumPtK 1782 11 (mask 11) (1782 * 11) true SuzRFO3.G SuzRFO3.GI 2
    SuzRFO3.cnt (fun i => nIf(Nat.beq i 7, SuzRFO3.T 8, SuzRFO3.T i)) SuzRFO3.PL SuzRFO3.POS
    SuzRFO3.SRT SuzRFO3.SRI 7) = true := by quickRfl

theorem negS : Bool.not (penumPtK 1782 11 (mask 11) (1782 * 11) false SuzRFS.G SuzRFS.GI 4
    SuzRFS.cnt (fun i => nIf(Nat.beq i 9, SuzRFS.T 10, SuzRFS.T i)) SuzRFS.PL SuzRFS.POS
    SuzRFS.SRT SuzRFS.SRI 9) = true := by quickRfl

theorem negCov : bAnd(Bool.not (covK Id 1), Bool.not (covK (SuzRFS.T 1) 2048)) = true := by
  quickRfl

theorem negCom : Bool.not (comK L4 1) = true := by quickRfl

theorem negSel : Bool.not (selFrom (fun k => Nat.beq (wg SuzRFWV k) 0) 8192 0 SuzRFV.tail) =
    true := by quickRfl

theorem negGen : Bool.not (Nat.beq (oWK (CFSG.Sporadic.SuzRecog.LocalR.cBackWords.getD 0 []).tail)
    (SuzInvT1.F 18)) = true := by quickRfl

theorem negP4 : bAnd(Bool.not (Nat.beq (p4 (VT (CFSG.KS.Mathieu.nget SuzRFA 0))) Id),
    Bool.not (Nat.beq (OddCore.fixCntK 1782 11 (mask 11) L4) 54)) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzRF

end
