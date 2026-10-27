module

public import CFSG.Certificates.Kernel.Th.Gen.Orders
public import Certificates.Kernel.Th.Assemble
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_S
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_K
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_Pf
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_O
public import CFSG.Certificates.Kernel.Common.RelNorm
public import CFSG.Certificates.Kernel.Th.S.HswTC

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh

open CFSG.KC.Th.Gen

#th_assemble orders OrdersData ordersChk

theorem orders_hA : CFSG.Sporadic.Th.Native.seedA = String.ofList ordersData.ThSeed_LA := by
  kernel_exact CFSG.KD.ThSeed.LA_eq

theorem orders_hB : CFSG.Sporadic.Th.Native.seedB = String.ofList ordersData.ThSeed_LB := by
  kernel_exact CFSG.KD.ThSeed.LB_eq

end CertificateChecks.KernelTh

end
