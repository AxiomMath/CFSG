module

public import Certificates.Kernel.HMathieu.Odd
public import Certificates.Data.Kernel.HMathieu.FixList
public import Certificates.Data.Kernel.HMathieu.Avoid
public import CFSG.Quasithin.Background.HMathieuMask
public import CFSG.Quasithin.Background.HMathieuPred
public import CFSG.Certificates.Kernel.Common.Each
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelHMathieu.OddFix
  "Certificates/Kernel/HMathieu/data/OddFix.json.gz" 8095 980164797073144840
  (J : List (List (List Nat))) (R : List (List (List Nat)))

namespace CertificateChecks.KernelHMathieu.OddFix

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu

@[expose] noncomputable def okOf (k : Nat) : List Nat → Bool :=
  if k < 5 then o2OK o2Masks23 else if k < 10 then avoidK 11 3 o2Masks24 else o2OK o2Masks22

@[expose] noncomputable def c7073fix (k : Nat) : Bool :=
  if k < 10 then
    fixAllK (okOf k) ccECols liftECols 11 ((Odd.E.getD k []).drop 1) (J.getD k []) (R.getD k [])
  else
    fixAllK (okOf k) cc10Cols lift10Cols 10 ((Odd.E.getD k []).drop 1) (J.getD k []) (R.getD k [])

#kc_each c7073fix 0 14

end CertificateChecks.KernelHMathieu.OddFix

end
