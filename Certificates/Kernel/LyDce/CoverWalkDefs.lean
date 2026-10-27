module

public import Certificates.Data.Kernel.LyDce.CoverWalk
public import Certificates.Kernel.LyDce.CoverData

public section

namespace CertificateChecks.KernelLyDce

open CFSG.KC CFSG.KC.LyDce CertificateChecks.KernelLyB

@[expose] noncomputable def walkSWith (es : List (Nat × Nat × Nat)) : Bool :=
  walkSFrom (NS 0) (NS 1) pk kp tc td (maskOf o0) es

@[expose] noncomputable def walkSAt (i : Nat) : Bool := walkSWith (dfs.getD i [])

end CertificateChecks.KernelLyDce

end
