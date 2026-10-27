module

public import Certificates.Kernel.Fi22Cls.Each
public import Certificates.Kernel.Fi22Cls.Strs
public import Certificates.Data.Kernel.Fi22Cls.Words
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Cls

open CFSG.KD.LyS0 CFSG.KC.Fi22Cls

theorem ch13620pRep : parseOK rep RS.chars 126 = true := by quickRfl

theorem ch13620pCls : parseOK cls CS.chars 126 = true := by quickRfl

theorem ch13620pW : wordsOK wo wd 126 WS.chars = true := by quickRfl

end CertificateChecks.KernelFi22Cls

end
