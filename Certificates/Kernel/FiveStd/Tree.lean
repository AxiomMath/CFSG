module

public import Certificates.Kernel.FiveStd.Data
public import Certificates.Data.Kernel.FiveStdKTree
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

noncomputable abbrev tpt : Nat → Bool := tPt T G 2 28800

@[expose] noncomputable def tF (k : Nat) : Bool := allR (900 * k) 900 tpt

#kc_each_unfold tF 0 32 as CertificateChecks.FiveStd.ch5147t

#kc_forall_chunks treeK (fun k => allR (900 * k) 900 tpt = true) 32
  CertificateChecks.FiveStd.ch5147t 1

theorem tree_chunks : ∀ k < 32, allR (900 * k) 900 tpt = true := treeK

end CertificateChecks.FiveStd

end
