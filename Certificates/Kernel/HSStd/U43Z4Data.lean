module

public import Certificates.Kernel.HSStd.U43CaseGen
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.HSStd.U43CaseGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.U43Z4

open CFSG.EvenSporadicStandard.HSStd.U43 CertificateChecks.KernelHSStd.U43CaseGen

meta def inZ : Array (Array Nat) := inM dZ4
meta def inIZ : Array (Array Nat) := inIM dZ4
meta def cosZ : Array (Array Nat) := cosM dZ4
meta def cgZ : Array (Array Nat) := cgM dZ4
meta def cgIZ : Array (Array Nat) := cgIM dZ4
meta def ygZ : Array (Array Nat) := ygM dZ4
meta def gGZ : Array (Array Nat) := gGM dZ4
meta def gGIZ : Array (Array Nat) := gGIM dZ4
meta def idsC : Array (Array Nat) := idsOf cgZ
meta def idsY : Array (Array Nat) := idsOf ygZ
meta def recC : Array (Array Nat) := recOf cgZ
meta def clC : Array (Array Nat) := clOf cgZ
meta def recY : Array (Array Nat) := recOf ygZ
meta def clY : Array (Array Nat) := clOf ygZ
meta def tZ : Array Nat := CFSG.Sporadic.SmallOddCore.Native.natArr dZ4.Tt
meta def yZ : Array Nat := CFSG.Sporadic.SmallOddCore.Native.natArr dZ4.y0
meta def covZ : Array (Array Nat) := coverM dZ4

end CertificateChecks.KernelHSStd.U43Z4

#kmisc_packarrs CertificateChecks.KernelHSStd.Z4P CertificateChecks.KernelHSStd.U43Z4.inZ 10
#kmisc_packarrs CertificateChecks.KernelHSStd.Z4I CertificateChecks.KernelHSStd.U43Z4.inIZ 10
#kmisc_packarrs CertificateChecks.KernelHSStd.Z4K CertificateChecks.KernelHSStd.U43Z4.cosZ 8
#kmisc_packarrs CertificateChecks.KernelHSStd.Z4W CertificateChecks.KernelHSStd.U43Z4.covZ 16
#kmulh CertificateChecks.KernelHSStd.Z4C 820 10 CertificateChecks.KernelHSStd.U43Z4.idsC
  CertificateChecks.KernelHSStd.U43Z4.cgZ CertificateChecks.KernelHSStd.U43CaseGen.idM 50000
#kfind CertificateChecks.KernelHSStd.Z4CCl CertificateChecks.KernelHSStd.U43Z4.recC
  CertificateChecks.KernelHSStd.U43Z4.clC
#kmulh CertificateChecks.KernelHSStd.Z4Y 820 10 CertificateChecks.KernelHSStd.U43Z4.idsY
  CertificateChecks.KernelHSStd.U43Z4.ygZ CertificateChecks.KernelHSStd.U43CaseGen.idM 50000
#kfind CertificateChecks.KernelHSStd.Z4YCl CertificateChecks.KernelHSStd.U43Z4.recY
  CertificateChecks.KernelHSStd.U43Z4.clY
#kmulh CertificateChecks.KernelHSStd.Z4KT 820 10 CertificateChecks.KernelHSStd.U43Z4.gGZ
  CertificateChecks.KernelHSStd.U43Z4.gGIZ CertificateChecks.KernelHSStd.U43Z4.tZ 50000
#kmulh CertificateChecks.KernelHSStd.Z4KY 820 10 CertificateChecks.KernelHSStd.U43Z4.gGZ
  CertificateChecks.KernelHSStd.U43Z4.gGIZ CertificateChecks.KernelHSStd.U43Z4.yZ 50000
#kmulh CertificateChecks.KernelHSStd.Z4CY 820 10 CertificateChecks.KernelHSStd.U43Z4.cgZ
  CertificateChecks.KernelHSStd.U43Z4.cgIZ CertificateChecks.KernelHSStd.U43Z4.yZ 50000

end
