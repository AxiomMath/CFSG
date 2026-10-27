module

public import Certificates.Kernel.Fin76bAut.Data
public import Certificates.Data.Kernel.Fin76bAutFacts
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFin76bAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.EAut

theorem ch24614Tup : eTupK ET 2646145 4 5 1920 = true := by quickRfl

theorem ch24614Ker : bAnd(ePrK ET 510760406, eKerK ET 510760406 1920 T 16 INN) = true := by
  quickRfl

theorem ch24614Fix : e613FixK ET 510760406 T 5 REP = true := by quickRfl

theorem ch24614Kl : e613KlK ET 2646145 4 5 510760406 T 5 REP 155 IV INN = true := by quickRfl

theorem ch24614Cent : e614K 2646145 4 1920 T 5 REP = true := by quickRfl

theorem ch24614Ea : e615K 2646145 4 128 ST = true := by quickRfl

end CertificateChecks.KernelFin76bAut

end
