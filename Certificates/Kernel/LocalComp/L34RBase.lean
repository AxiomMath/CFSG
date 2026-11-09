module

public import Certificates.Kernel.LocalComp.L34RBW
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Certificates.Kernel.LocalComp.L34RBW
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34RB

meta def S : Array (Array Nat) := CFSG.KS.SporSch.MOCG.strongOf 42 CFSG.PSL3Four.Native.gTabs D

end CertificateChecks.KernelLC.L34RB

#ks_rawchain CertificateChecks.KernelLC.L34RB.C 42 6 42 CertificateChecks.KernelLC.L34RB.S
  CertificateChecks.KernelLC.L34RB.base 6 CertificateChecks.KernelLC.L34RB.D

end
