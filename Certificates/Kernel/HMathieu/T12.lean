module

public import Certificates.Data.Kernel.HMathieu.Tab
public import CFSG.Quasithin.H13.A5M12Inputs
public import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM11
public import CFSG.Quasithin.Vol2.Ch10SecQ1M12Data
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Bridge.M23Surj

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelHMathieu.T12
  "Certificates/Kernel/HMathieu/data/T12.json.gz" 11264 5152084004615231311
  (gens : List Nat) (E : List Nat) (inv : List Nat) (P : List Nat) (rows : List (Nat × Nat))
  (Mc : List (List Nat))

namespace CertificateChecks.KernelHMathieu.T12

open CFSG.KC.HMathieu CFSG.KC.Enum CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12

set_option maxHeartbeats 0 in
theorem bfs : (bfsP gens 64 [pidn 24 5] [pidn 24 5]).reverse = E := by decide +kernel

theorem vpE : E.all vpK = true := by decide +kernel

theorem vpG : gens.all vpK = true := by decide +kernel

theorem invOK : invFrom (E.getD 0 0) E 0 = inv := by decide +kernel

theorem pOK : P = inv.map (fun i => E.getD i 0) ++ [E.getD 0 0] := by decide +kernel

theorem lenOK : inv.length = 35 ∧ rows.length = 35 := by decide +kernel

set_option maxHeartbeats 0 in
theorem tabs : tabsK 35 P rows = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem mcOK : Mc = P.map (matP κC12Cols lift12Cols 10) := by decide +kernel

end CertificateChecks.KernelHMathieu.T12

end
