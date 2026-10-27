module

public import Certificates.Kernel.FiveStd.Data
public import Certificates.Data.Kernel.FiveStdKDiag
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

@[expose] def R4 : List Nat := [78876, 409405, 412540, 79877]

@[expose] def R4I : List Nat := [78876, 409405, 415740, 80503]

theorem r4_inv : ∀ k < 4, invK (R4.getD k 0) = R4I.getD k 0 := by decide +kernel

noncomputable abbrev kpt : Nat → Bool := fun i => R4I.any fun ri => inKKK (mulK (rCode (f64 T i)) ri)

@[expose] noncomputable def kF (k : Nat) : Bool := allR (900 * k) 900 kpt

#kc_each_unfold kF 0 32 as CertificateChecks.FiveStd.ch5147k

#kc_forall_chunks cosetK (fun k => allR (900 * k) 900 kpt = true) 32
  CertificateChecks.FiveStd.ch5147k 1

theorem coset_chunks : ∀ k < 32, allR (900 * k) 900 kpt = true := cosetK

theorem coset_neg : (!allR 0 900 fun i => R4I.dropLast.any fun ri => inKKK (mulK (rCode (f64 T i)) ri)) = true := by
  decide +kernel

end CertificateChecks.FiveStd

end
