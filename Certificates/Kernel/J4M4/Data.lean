module

public import Init
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelJ4M4
  "Certificates/Kernel/J4M4/data/j4m4.json.gz" 5103765 17246252552881078014
  (KG : List Nat) (KGI : List Nat) (GC : Nat) (GCI : Nat)
  (KL : List Nat) (KY : List (List (Nat × Nat × Nat)))
  (FL : List Nat) (FY : List (List (Nat × Nat × Nat)))
  (WL : List Nat) (WY : List (List (Nat × Nat × Nat)))
  (RL : List Nat) (RY : List (List (Nat × Nat × Nat)))
  (Y1L : List Nat) (Y1Y : List (List (Nat × Nat × Nat)))
  (Y2L : List Nat) (Y2Y : List (List (Nat × Nat × Nat)))
  (CL : List (List Nat)) (IR : List (Nat × Nat × List (List (Nat × Nat × Nat))))

end
