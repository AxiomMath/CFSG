module

public import Certificates.Kernel.Sporadic.OddCore.CU43Syl
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Multipliers.U43BChain
meta import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Data3
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSpor.CU43SylE

open CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor.CU43Syl

meta def siM : Array (Array Nat) := sM.map (CFSG.Monster.B.Co2.Native.invCand 820)

meta def recM : Array (Array Nat) := (bfs (fun j t => conjTab 820 idM sM[j]! t) 5 idM 256).tabs

meta def clM : Array (Array Nat) := (recM.map fun x => (sM ++ siM).map fun g => comp 820 x g).flatten

end CertificateChecks.KernelSpor.CU43SylE

#kmisc_packarrs CertificateChecks.KernelSpor.CU43SI CertificateChecks.KernelSpor.CU43SylE.siM 10
#kfind CertificateChecks.KernelSpor.CU43Cl CertificateChecks.KernelSpor.CU43SylE.recM
  CertificateChecks.KernelSpor.CU43SylE.clM

namespace CertificateChecks.KernelSpor.CU43SylE

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelU43B

@[expose] noncomputable def inPK (p : Nat) : Bool :=
  siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) C.LR C.TRI C.BP 3 0 p

theorem inv_ok : allN 5 (fun j => bAnd(CU43Syl.cK (CU43SI j),
    invEqK 820 10 (mask 10) (820 * 10) (CU43S.GI j) (CU43SI j))) = true := by
  quickRfl

theorem inP_ok : allN 5 (fun j => inPK (CU43S.GI j)) = true := by
  quickRfl

theorem sCl : slK (Nat.mul CU43S.cnt 10)
    (findPtK CU43S.cnt CU43S.T (prodQK 820 10 (mask 10) 10 CU43S.T (bothK 5 CU43S.GI CU43SI))
      CU43Cl) 0 (Nat.mul CU43S.cnt 10) = true := by quickRfl

theorem inv_neg : invEqK 820 10 (mask 10) (820 * 10) (CU43S.GI 0) (CU43SI 1) = false := by
  decide +kernel

end CertificateChecks.KernelSpor.CU43SylE

end
