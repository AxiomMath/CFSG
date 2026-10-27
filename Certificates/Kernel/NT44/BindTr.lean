module

public import Certificates.Kernel.NT44.Pack2
public import Certificates.Data.Kernel.Misc.RowsBind
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CertificateChecks.KernelNT44

open CFSG.GH74.GLS.NT44.PermutationNative CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ConjTab
open CFSG.KC.Enum (pg)
open CFSG.KS (mask)
open CFSG.KC.Misc.Clos (allR)

theorem nt44_tr_bind : rowsBind 4 8 nt44Tr ((tr ()).toList.map Array.toList) 0 = true := by
  simp only [tr, Array.toList_append, List.toList_toArray]
  quickRfl

theorem nt44_parent : (decide ((parent ()).toList.getD 0 [] = []) &&
    allR 1 255 (parentAt (parent ()).toList nt44Tr fun i => pg 8 (mask 8) (nt44Par 0) i)) =
      true := by
  simp only [parent, Array.toList_append, List.toList_toArray]
  quickRfl

end CertificateChecks.KernelNT44

end
