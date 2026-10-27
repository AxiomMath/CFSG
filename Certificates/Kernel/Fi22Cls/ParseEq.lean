module

public import Certificates.Kernel.Fi22Cls.ParseChk
public import CFSG.Certificates.Kernel.Fi22Cls.Parse

public section

namespace CertificateChecks.KernelFi22Cls

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native (labRep labCls conjW)
open CFSG.KS.Fi22ClsParse

theorem labRep_eq : labRep () = Array.ofFn (n := 126) fun l => rep l.val :=
  labRep_of RS.eq ch13620pRep

theorem labCls_eq : labCls () = Array.ofFn (n := 126) fun l => cls l.val :=
  labCls_of CS.eq ch13620pCls

theorem conjW_eq : conjW () = ((List.range' 0 126).map (wlist wo wd)).toArray :=
  conjW_of WS.eq ch13620pW

end CertificateChecks.KernelFi22Cls

end
