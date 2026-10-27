module

public import CFSG.Quasithin.Recognition.CertU33PermInputs

public section

namespace CertificateChecks.KernelMisc.U33

@[expose] def baseArr : Array Nat := (CFSG.Quasithin.u33Base.map Fin.val).toArray

@[expose] def derivs : List (List Int) := CFSG.Quasithin.u33Words.toList

end CertificateChecks.KernelMisc.U33

end
