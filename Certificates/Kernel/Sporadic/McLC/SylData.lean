module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CertificateChecks.KernelSpor.McLCSyl

open CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 275

meta def idsM : Array (Array Nat) := Array.replicate 4 idM

meta def sM : Array (Array Nat) := CFSG.ClassicalInvolution.McLData.sgens.toArray.map natArr

meta def siM : Array (Array Nat) := sM.map (CFSG.Monster.B.Co2.Native.invCand 275)

meta def recM : Array (Array Nat) := (bfs (fun j t => conjTab 275 idM sM[j]! t) 4 idM 50000).tabs

meta def clM : Array (Array Nat) :=
  (recM.map fun x => (sM ++ siM).map fun g => comp 275 x g).flatten

meta def cjM : Array (Array Nat) := CFSG.ClassicalInvolution.McLData.conjTbls.toArray.map natArr

end CertificateChecks.KernelSpor.McLCSyl

#kmulh CertificateChecks.KernelSpor.McLCS 275 9 CertificateChecks.KernelSpor.McLCSyl.idsM
  CertificateChecks.KernelSpor.McLCSyl.sM CertificateChecks.KernelSpor.McLCSyl.idM 50000
#kmisc_packarrs CertificateChecks.KernelSpor.McLCSI CertificateChecks.KernelSpor.McLCSyl.siM 9
#kfind CertificateChecks.KernelSpor.McLCSCl CertificateChecks.KernelSpor.McLCSyl.recM
  CertificateChecks.KernelSpor.McLCSyl.clM
#kmisc_packarrs CertificateChecks.KernelSpor.McLCSJ CertificateChecks.KernelSpor.McLCSyl.cjM 9

end
