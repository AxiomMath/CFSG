module

public import Certificates.Data.Kernel.LyModel.Cp3
public import Certificates.Kernel.LyDce.CoverData
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelLyModel "Certificates/Kernel/LyModel/data/cp3.json.gz" 2247 15874446132204507115
  (yC : List Nat) (gC : List Nat) (uC : List (List Nat)) (l0 : Nat) (ents : List (Nat × Nat × Nat))

namespace CertificateChecks.KernelLyModel

open CFSG.KC CFSG.KC.LyDce CFSG.KC.LyModel CertificateChecks.KernelLyDce

@[expose] noncomputable def cm : Nat := maskOf (l0 :: ents.map Prod.fst)

@[expose] noncomputable def invWith (C i : Nat) : Bool :=
  allFrom (Nat.mul 1000 i) 1000 (invAt tc td root C yC)

@[expose] noncomputable def invChunk (i : Nat) : Bool := strictBN cm fun C => invWith C i

@[expose] noncomputable def orbAll : Bool :=
  andB (Nat.beq (mvC tc td gC root) l0) (orbOK tc td uC ents [l0])

end CertificateChecks.KernelLyModel

end
