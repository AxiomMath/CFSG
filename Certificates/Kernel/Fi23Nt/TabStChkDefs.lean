module

public import Certificates.Data.Kernel.Fi23Nt.TabDefs
public import Certificates.Kernel.Fi23Nt.Data
public import Certificates.Kernel.Fi23Nt.DataE
public import Certificates.Kernel.Fi23Nt.DataT

public section

namespace CFSG.KD.Fi23Nt

open CFSG.KC.Fi23Nt

@[expose] noncomputable def lnkSt : Bool := lnkK eCW eCPar eCN tCA stIdx (fstK st)

@[expose] noncomputable def negLnkSt : Bool := Bool.not (lnkK eCW eCPar eCN tCA stIdx (fstK st).reverse)

end CFSG.KD.Fi23Nt

end
