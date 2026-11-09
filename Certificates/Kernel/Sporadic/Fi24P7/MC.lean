module

public import Certificates.Kernel.Sporadic.Fi24P7.Defs
public import Certificates.Kernel.Sporadic.Fi24P7.MCA2
public import Certificates.Kernel.Sporadic.Fi24P7.MCA4
public import Certificates.Kernel.Sporadic.Fi24P7.MCB4
public import Certificates.Kernel.Sporadic.Fi24P7.MCS4
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24P7

#kc_forall_tree CA2.all (fun i => chA2 i = true) 10 CFSG.KD.Fi24P7.CA2.c
#kc_forall_tree CA4.all (fun i => chA4 i = true) 11 CFSG.KD.Fi24P7.CA4.c
#kc_forall_tree CB4.all (fun i => chB4 i = true) 11 CFSG.KD.Fi24P7.CB4.c
#kc_forall_tree CS4.all (fun i => chS4 i = true) 5 CFSG.KD.Fi24P7.CS4.c

end CFSG.KD.Fi24P7

end
