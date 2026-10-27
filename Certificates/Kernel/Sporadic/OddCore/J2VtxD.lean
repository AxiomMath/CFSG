module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.Quasithin.Recognition.St84.J2VtxInputs
meta import CFSG.Quasithin.Recognition.St84.J2VtxInputs
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.SmallOddCore.LocalSpec
meta import CFSG.Sporadic.SmallOddCore.LocalSpec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2VtxD

open CFSG.Quasithin.F112R.St84.J2Model CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 315

meta def vM : Array (Array Nat) :=
  #[natArr (c2aT ()), natArr (c2bT ()), natArr (e1T ()), natArr (e2T ()), natArr (f1T ()),
    natArr (f2T ()), natArr (bmT ()), natArr (tmT ()), natArr (yT ()), natArr (rmT ())]

meta def viM : Array (Array Nat) := vM.map (CFSG.Monster.B.Co2.Native.invCand 315)

meta def kM : Array (Array Nat) := (κArr ()).map natArr

meta def gOf (ix : List Nat) : Array (Array Nat) := ix.toArray.map fun j => vM[j]!

meta def idsOf (ix : List Nat) : Array (Array Nat) := Array.replicate ix.length idM

meta def recOf (ix : List Nat) (cap : Nat) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 315 idM (gOf ix)[j]! t) (gOf ix).size idM cap).tabs

meta def clOf (ix : List Nat) (cap : Nat) : Array (Array Nat) :=
  let g := gOf ix
  let gi := g.map (CFSG.Monster.B.Co2.Native.invCand 315)
  ((recOf ix cap).map fun x => (g ++ gi).map fun h => comp 315 x h).flatten

meta def gA : Array (Array Nat) := gOf [0, 1]
meta def iA : Array (Array Nat) := idsOf [0, 1]
meta def rA : Array (Array Nat) := recOf [0, 1] 200
meta def cA : Array (Array Nat) := clOf [0, 1] 200
meta def gB : Array (Array Nat) := gOf [2, 3, 4, 5, 7]
meta def iB : Array (Array Nat) := idsOf [2, 3, 4, 5, 7]
meta def rB : Array (Array Nat) := recOf [2, 3, 4, 5, 7] 200
meta def cB : Array (Array Nat) := clOf [2, 3, 4, 5, 7] 200
meta def gC : Array (Array Nat) := gOf [9, 6, 7]
meta def iC : Array (Array Nat) := idsOf [9, 6, 7]
meta def rC : Array (Array Nat) := recOf [9, 6, 7] 100
meta def cC : Array (Array Nat) := clOf [9, 6, 7] 100
meta def gX : Array (Array Nat) := gOf [2, 3, 4, 5, 9, 6, 7]
meta def iX : Array (Array Nat) := idsOf [2, 3, 4, 5, 9, 6, 7]
meta def rX : Array (Array Nat) := recOf [2, 3, 4, 5, 9, 6, 7] 3000
meta def cX : Array (Array Nat) := clOf [2, 3, 4, 5, 9, 6, 7] 3000

end CertificateChecks.KernelSpor.J2VtxD

#kmisc_packarrs CertificateChecks.KernelSpor.VxT CertificateChecks.KernelSpor.J2VtxD.vM 9
#kmisc_packarrs CertificateChecks.KernelSpor.VxI CertificateChecks.KernelSpor.J2VtxD.viM 9
#kmisc_packarrs CertificateChecks.KernelSpor.VxK CertificateChecks.KernelSpor.J2VtxD.kM 9
#kmulh CertificateChecks.KernelSpor.VxA 315 9 CertificateChecks.KernelSpor.J2VtxD.iA
  CertificateChecks.KernelSpor.J2VtxD.gA CertificateChecks.KernelSpor.J2VtxD.idM 200
#kfind CertificateChecks.KernelSpor.VxACl CertificateChecks.KernelSpor.J2VtxD.rA
  CertificateChecks.KernelSpor.J2VtxD.cA
#kmulh CertificateChecks.KernelSpor.VxB 315 9 CertificateChecks.KernelSpor.J2VtxD.iB
  CertificateChecks.KernelSpor.J2VtxD.gB CertificateChecks.KernelSpor.J2VtxD.idM 200
#kfind CertificateChecks.KernelSpor.VxBCl CertificateChecks.KernelSpor.J2VtxD.rB
  CertificateChecks.KernelSpor.J2VtxD.cB
#kmulh CertificateChecks.KernelSpor.VxC 315 9 CertificateChecks.KernelSpor.J2VtxD.iC
  CertificateChecks.KernelSpor.J2VtxD.gC CertificateChecks.KernelSpor.J2VtxD.idM 100
#kfind CertificateChecks.KernelSpor.VxCCl CertificateChecks.KernelSpor.J2VtxD.rC
  CertificateChecks.KernelSpor.J2VtxD.cC
#kmulh CertificateChecks.KernelSpor.VxX 315 9 CertificateChecks.KernelSpor.J2VtxD.iX
  CertificateChecks.KernelSpor.J2VtxD.gX CertificateChecks.KernelSpor.J2VtxD.idM 3000
#kfind CertificateChecks.KernelSpor.VxXCl CertificateChecks.KernelSpor.J2VtxD.rX
  CertificateChecks.KernelSpor.J2VtxD.cX

end
