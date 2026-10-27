module

public import CFSG.Certificates.Kernel.TwoNodeSmall.ExclKSound
import Certificates.Kernel.TwoNodeSmall.ExclChecks
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import Certificates.Kernel.TwoNodeSmall.ExclData

namespace CFSG.KD.TNS708602

#kc_forall_chunks allC (fun k => CFSG.KD.TNS708602.cc k = true) 42
  CFSG.KD.TNS708602.ch708602.c_ 1
#kc_forall_chunks allG (fun k => CFSG.KD.TNS708602.cg k = true) 84
  CFSG.KD.TNS708602.ch708602.g_ 1

public section

public theorem excl_closed_all :
    ∀ Q ∈ CFSG.TwoNodeSmall.exclPts (), ∀ [Fact Q.pt.p.Prime], Q.ClosedExcl :=
  CFSG.TwoNodeSmall.ExclK.excl_closed_of (CS := cs) (RS := rk) allC allG

end

end CFSG.KD.TNS708602
