module

public import Certificates.Kernel.Sporadic.OddCore.J3BetaA5
public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.PkPow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

namespace CertificateChecks.KernelSpor.B24603

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 6156

meta def idsM : Array (Array Nat) := Array.replicate 2 idM

meta def gM : Array (Array Nat) := #[natArr (j3BetaTbl 8), natArr (j3BetaTbl 9)]

meta def giM : Array (Array Nat) := (gM.push (natArr (j3BetaTbl 7))).map
  (CFSG.Monster.B.Co2.Native.invCand 6156)

meta def bfsM := bfs (fun j t => conjTab 6156 idM gM[j]! t) gM.size idM 1100

meta def recM : Array (Array Nat) := bfsM.tabs

meta def clM : Array (Array Nat) :=
  (recM.map fun x => (gM ++ (giM.extract 0 2)).map fun g => comp 6156 x g).flatten

meta def labM : Array (Array Nat) := Id.run do
  let E := bfsM
  let pg := piGens.map natArr
  let mut r : Array (Array Nat) := #[idTab 6]
  for k in [1:E.tabs.size] do
    r := r.push (comp 6 r[E.par[k]!]! pg[E.lab[k]!]!)
  return r

end CertificateChecks.KernelSpor.B24603

#kmisc_packarrs CertificateChecks.KernelSpor.B24603I CertificateChecks.KernelSpor.B24603.giM 13

#kmisc_packarrs CertificateChecks.KernelSpor.B24603L CertificateChecks.KernelSpor.B24603.labM 3

#kmulh CertificateChecks.KernelSpor.B24603R 6156 13 CertificateChecks.KernelSpor.B24603.idsM
  CertificateChecks.KernelSpor.B24603.gM CertificateChecks.KernelSpor.B24603.idM 1100

#kfind CertificateChecks.KernelSpor.B24603Cl CertificateChecks.KernelSpor.B24603.recM
  CertificateChecks.KernelSpor.B24603.clM

namespace CertificateChecks.KernelSpor.B24603

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def e24603 (i : Nat) : Bool :=
  penumSlK 6156 13 (mask 13) (6156 * 13) true B24603R.G B24603R.GI 2 B24603R.cnt B24603R.T
    B24603R.PL B24603R.POS B24603R.SRT B24603R.SRI (Nat.mul i 90) 90

@[expose] noncomputable def c24603 (i : Nat) : Bool :=
  slK (Nat.mul B24603R.cnt 4)
    (findPtK B24603R.cnt B24603R.T (prodQK 6156 13 (mask 13) 4 B24603R.T (bothK 2 B24603R.GI B24603I))
      B24603Cl) (Nat.mul i 180) 180

end CertificateChecks.KernelSpor.B24603

end
