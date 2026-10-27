module

public import Certificates.Kernel.HSStd.U43CaseGen
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.HSStd.U43CaseGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.U43Vb

open CFSG.EvenSporadicStandard.HSStd.U43 CertificateChecks.KernelHSStd.U43CaseGen

meta def inV : Array (Array Nat) := inM dVb
meta def inIV : Array (Array Nat) := inIM dVb
meta def cosV : Array (Array Nat) := cosM dVb
meta def cgV : Array (Array Nat) := cgM dVb
meta def cgIV : Array (Array Nat) := cgIM dVb
meta def ygV : Array (Array Nat) := ygM dVb
meta def gGV : Array (Array Nat) := gGM dVb
meta def gGIV : Array (Array Nat) := gGIM dVb
meta def idsCV : Array (Array Nat) := idsOf cgV
meta def idsYV : Array (Array Nat) := idsOf ygV
meta def recCV : Array (Array Nat) := recOf cgV
meta def clCV : Array (Array Nat) := clOf cgV
meta def recYV : Array (Array Nat) := recOf ygV
meta def clYV : Array (Array Nat) := clOf ygV
meta def tV : Array Nat := CFSG.Sporadic.SmallOddCore.Native.natArr dVb.Tt
meta def yV : Array Nat := CFSG.Sporadic.SmallOddCore.Native.natArr dVb.y0
meta def covV : Array (Array Nat) := coverM dVb

end CertificateChecks.KernelHSStd.U43Vb

#kmisc_packarrs CertificateChecks.KernelHSStd.VbP CertificateChecks.KernelHSStd.U43Vb.inV 10
#kmisc_packarrs CertificateChecks.KernelHSStd.VbI CertificateChecks.KernelHSStd.U43Vb.inIV 10
#kmisc_packarrs CertificateChecks.KernelHSStd.VbK CertificateChecks.KernelHSStd.U43Vb.cosV 8
#kmisc_packarrs CertificateChecks.KernelHSStd.VbW CertificateChecks.KernelHSStd.U43Vb.covV 16
#kmulh CertificateChecks.KernelHSStd.VbC 820 10 CertificateChecks.KernelHSStd.U43Vb.idsCV
  CertificateChecks.KernelHSStd.U43Vb.cgV CertificateChecks.KernelHSStd.U43CaseGen.idM 50000
#kfind CertificateChecks.KernelHSStd.VbCCl CertificateChecks.KernelHSStd.U43Vb.recCV
  CertificateChecks.KernelHSStd.U43Vb.clCV
#kmulh CertificateChecks.KernelHSStd.VbY 820 10 CertificateChecks.KernelHSStd.U43Vb.idsYV
  CertificateChecks.KernelHSStd.U43Vb.ygV CertificateChecks.KernelHSStd.U43CaseGen.idM 50000
#kfind CertificateChecks.KernelHSStd.VbYCl CertificateChecks.KernelHSStd.U43Vb.recYV
  CertificateChecks.KernelHSStd.U43Vb.clYV
#kmulh CertificateChecks.KernelHSStd.VbKT 820 10 CertificateChecks.KernelHSStd.U43Vb.gGV
  CertificateChecks.KernelHSStd.U43Vb.gGIV CertificateChecks.KernelHSStd.U43Vb.tV 50000
#kmulh CertificateChecks.KernelHSStd.VbKY 820 10 CertificateChecks.KernelHSStd.U43Vb.gGV
  CertificateChecks.KernelHSStd.U43Vb.gGIV CertificateChecks.KernelHSStd.U43Vb.yV 50000
#kmulh CertificateChecks.KernelHSStd.VbCY 820 10 CertificateChecks.KernelHSStd.U43Vb.cgV
  CertificateChecks.KernelHSStd.U43Vb.cgIV CertificateChecks.KernelHSStd.U43Vb.yV 50000

end
