module

public import Certificates.Kernel.Sporadic.Fi24Sev.DataB
import CFSG.Certificates.Kernel.Common.SliceRange
import CFSG.Certificates.Kernel.Common.ForallTree

public section

#kc_slice_range CFSG.KD.Fi24SevB.slc CFSG.KD.Fi24SevB.Ck.slc 0 79

#kc_forall_tree CFSG.KD.Fi24SevB.Ck.slcAll (fun i => CFSG.KD.Fi24SevB.slc i = true) 79
  CFSG.KD.Fi24SevB.Ck.slc

end
