module

public import Certificates.Kernel.Sporadic.Fi24P7.Defs
public import Certificates.Kernel.Sporadic.Fi24P7.S4a
public import Certificates.Kernel.Sporadic.Fi24P7.S4b
public import Certificates.Kernel.Sporadic.Fi24P7.S4c
public import Certificates.Kernel.Sporadic.Fi24P7.S4d
public import Certificates.Kernel.Sporadic.Fi24P7.S4e
import CFSG.Certificates.Kernel.Common.ForallTree

public noncomputable section

namespace CFSG.KD.Fi24P7

#kc_forall_tree S4.all (fun c => ok4 c = true) 75 CFSG.KD.Fi24P7.S4.c

end CFSG.KD.Fi24P7

end
