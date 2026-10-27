module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Census.McLChain
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.GH74.McLSylowThree
meta import Certificates.Data.GH74.McLSylowThree
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.McLTwoH CFSG.Sporadic.Recognition.McLAS.sylTwoHex
#kmisc_hexflat CertificateChecks.KernelSpor.McLTwoH CFSG.Sporadic.Recognition.McLAS.sylTwoHex 3 275 9 7

namespace CertificateChecks.KernelSpor.McLTwo

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 275

meta def idsM : Array (Array Nat) := Array.replicate 7 idM

meta def sM : Array (Array Nat) := sylTwoGens.map natArr

meta def siM : Array (Array Nat) := sM.map (CFSG.Monster.B.Co2.Native.invCand 275)

meta def recM : Array (Array Nat) := (bfs (fun j t => conjTab 275 idM sM[j]! t) 7 idM 200).tabs

meta def eiM : Array (Array Nat) := recM.map (CFSG.Monster.B.Co2.Native.invCand 275)

meta def clM : Array (Array Nat) :=
  (recM.map fun x => (sM ++ siM).map fun g => comp 275 x g).flatten

end CertificateChecks.KernelSpor.McLTwo

#kmulh CertificateChecks.KernelSpor.McLTwoS 275 9 CertificateChecks.KernelSpor.McLTwo.idsM
  CertificateChecks.KernelSpor.McLTwo.sM CertificateChecks.KernelSpor.McLTwo.idM 200
#kmisc_packarrs CertificateChecks.KernelSpor.McLTwoSI CertificateChecks.KernelSpor.McLTwo.siM 9
#kmisc_packarrs CertificateChecks.KernelSpor.McLTwoEI CertificateChecks.KernelSpor.McLTwo.eiM 9
#kfind CertificateChecks.KernelSpor.McLTwoCl CertificateChecks.KernelSpor.McLTwo.recM
  CertificateChecks.KernelSpor.McLTwo.clM

namespace CertificateChecks.KernelSpor.McLTwo

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelCensus

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 275 9 (mask 9) (275 * 9) p

theorem base_ok : bAnd(szOK 275 9, bAnd(cK (pidn 275 9), bAnd(CFSG.KS.Prim.idK 275 9 (mask 9),
    bAnd(allN 7 (fun j => bAnd(cK (McLTwoH.F j), bAnd(Nat.beq (McLTwoS.GI j) (McLTwoH.F j),
      bAnd(Nat.beq (McLTwoS.G j) (pidn 275 9), bAnd(cK (McLTwoSI j),
        invEqK 275 9 (mask 9) (275 * 9) (McLTwoH.F j) (McLTwoSI j)))))),
    bAnd(Nat.beq McLTwoS.cnt 128, penumHdK (pidn 275 9) McLTwoS.cnt 200 McLTwoS.T McLTwoS.PL)))))
      = true := by
  quickRfl

theorem sift_ok : allN 7 (fun j => siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) McLC.LR McLC.TRI
    McLC.BP 5 0 (McLTwoH.F j)) = true := by
  quickRfl

theorem sE : penumSlK 275 9 (mask 9) (275 * 9) true McLTwoS.G McLTwoS.GI 7 McLTwoS.cnt McLTwoS.T
    McLTwoS.PL McLTwoS.POS McLTwoS.SRT McLTwoS.SRI 0 McLTwoS.cnt = true := by quickRfl

theorem sH : slK McLTwoS.cnt (hsortPtK 275 9 (mask 9) McLTwoS.cnt McLTwoS.T McLTwoS.HS McLTwoS.HSI)
    0 McLTwoS.cnt = true := by quickRfl

theorem sCl : slK (Nat.mul McLTwoS.cnt 14)
    (findPtK McLTwoS.cnt McLTwoS.T (prodQK 275 9 (mask 9) 14 McLTwoS.T (bothK 7 McLTwoS.GI McLTwoSI))
      McLTwoCl) 0 (Nat.mul McLTwoS.cnt 14) = true := by quickRfl

theorem sInv : allN 128 (fun i => bAnd(cK (McLTwoEI i),
    invEqK 275 9 (mask 9) (275 * 9) (McLTwoS.T i) (McLTwoEI i))) = true := by quickRfl

end CertificateChecks.KernelSpor.McLTwo

end
