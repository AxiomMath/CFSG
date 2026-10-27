module

public import Certificates.Kernel.Fi22Cls.LabParse
public import CFSG.Certificates.Kernel.Fi22Cls.Parse

public section

namespace CertificateChecks.KernelFi22Cls

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native (labOf witOf)
open CFSG.KS.Fi22ClsParse

theorem labOf_eq : labOf () = Array.ofFn (n := 19683) fun i => lab i.val :=
  arr_of LOS.eq ch13620pLab

theorem witOf_eq : witOf () = Array.ofFn (n := 19683) fun i => wit i.val :=
  arr_of WIS.eq ch13620pWit

end CertificateChecks.KernelFi22Cls

end
