module

public import Certificates.Data.Kernel.SmithL6Coll
public import Certificates.Kernel.SmithL6Coll.Data

public section

namespace CertificateChecks.KernelSmithL6Coll

open CFSG.SmithL6.CollK

@[expose] noncomputable def LM : List (List Nat × Nat × Nat × Nat) := rtop.flatten.zip tfm

@[expose] noncomputable def top (i : Nat) : Bool := topT rtop i

@[expose] noncomputable def rows (k : Nat) : Bool := rowsK LM (21 * k) 21

end CertificateChecks.KernelSmithL6Coll
