module

public import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSporSch.HSD "Certificates/Kernel/SporSch/PairHS/data/hs2272.json.gz" 170011 14072147195037171034
  (bnd : List (Nat × Nat × Bool)) (ua : List Nat) (z0 : Nat) (fx : List Nat)
  (cf : List (List (List Nat)))
  (ch : List (List (Nat × List (List Nat) × List (Nat × Nat × Nat))))
  (od : List (List (Nat × List (List Nat) × List (List Nat × Nat))))
  (wd : List (List Nat)) (sw : List (List Nat)) (sK : Nat) (sM : Nat) (sS : Nat) (sSI : Nat)
  (sc : List (Nat × List Nat)) (uc : List (Nat × List Nat))

end
