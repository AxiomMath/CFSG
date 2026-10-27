module

public import Certificates.Data.Kernel.LyDce.Cover
public import Certificates.Kernel.LyDce.ChainData
public import Certificates.Kernel.LyDce.Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelLyDce "Certificates/Kernel/LyDce/data/cover.json.gz" 1813523 4021400089761234105
  (o0 : List Nat) (root : Nat) (pk : Nat) (kp : Nat) (tc : Nat) (td : Nat) (ta : Nat) (tb : Nat)
  (te : Nat) (dfs : List (List (Nat × Nat × Nat))) (frs : List (List (Nat × Nat × Nat)))

namespace CertificateChecks.KernelLyDce

open CFSG.KC CFSG.KC.LyDce CertificateChecks.KernelLyB

@[expose] noncomputable def tabs : Tabs := ⟨tc, td, ta, tb, te⟩

@[expose] noncomputable def fix0 : Bool := fixOK NS (maskOf o0) (sG.getD 0 [])

@[expose] noncomputable def walkWith (es : List (Nat × Nat × Nat)) : Bool :=
  walkFrom (NS 0) (NS 1) pk kp tc td (maskOf o0) es

@[expose] noncomputable def walkAt (i : Nat) : Bool := walkWith (dfs.getD i [])

@[expose] noncomputable def covAll : Bool :=
  andB (andB (covOK dfs) (incOK kp)) (andB (tabOK tc td ta tb te) (Nat.blt root nL))

@[expose] noncomputable def frWith (n : Nat) (es : List (Nat × Nat × Nat)) : Bool :=
  frOK tabs nt rep (sG.getD n []) (Nat.succ n) root es 0

@[expose] noncomputable def frAt (n : Nat) : Bool := frWith n (frs.getD n [])

end CertificateChecks.KernelLyDce

end
