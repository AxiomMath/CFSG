module

public import Certificates.Data.Kernel.L5.HFQ
public import Certificates.Data.Kernel.L5.HFV
public import Certificates.Kernel.L5.HFPData
import CFSG.Certificates.Kernel.Common.Each

public section

namespace CFSG.Certificates.Kernel.L5Q

open CFSG.Certificates.Kernel.L5H CFSG.GH74.GLS.C3.Layer2.L5.HF

set_option maxRecDepth 100000

@[expose] noncomputable def c5071n24Row (k : Nat) : Bool := rowQ gN (n24EntryV g72GN g72MP) k

@[expose] noncomputable def c5071famRow (k : Nat) : Bool := rowQ gFam (famEntryN g72GN g72MP) k

@[expose] noncomputable def c5071n24Neg (k : Nat) : Bool := !rowQ gN (fun _ => false) k

#kc_each CFSG.Certificates.Kernel.L5Q.c5071n24Row 0 4

#kc_each CFSG.Certificates.Kernel.L5Q.c5071famRow 0 4

#kc_each CFSG.Certificates.Kernel.L5Q.c5071n24Neg 1 2

end CFSG.Certificates.Kernel.L5Q

end
