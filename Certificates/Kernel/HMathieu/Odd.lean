
module

public import Certificates.Data.Kernel.HMathieu.Odd
public import CFSG.Quasithin.Background.HMathieuCodeMask
public import CFSG.Quasithin.H13.A5M12Inputs
public import CFSG.Quasithin.Background.HF22Inputs
public import CFSG.Certificates.Kernel.Common.Each
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

#kc_repo #kc_json_gz CertificateChecks.KernelHMathieu.Odd
  "Certificates/Kernel/HMathieu/data/Odd.json.gz" 11126 17303551749236284121
  (G : List (List Nat)) (E : List (List Nat)) (J : List (List (List Nat)))

namespace CertificateChecks.KernelHMathieu.Odd

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12

@[expose] def spec : List (List Nat × List Nat × Nat × Nat × Nat) :=
  [(κCCols, liftCCols, 11, 6, 16), (κCCols, liftCCols, 11, 6, 16), (κCCols, liftCCols, 11, 6, 16),
    (κCCols, liftCCols, 11, 6, 16), (κCCols, liftCCols, 11, 6, 32),
    (κCCols, liftCCols, 11, 6, 32), (κCCols, liftCCols, 11, 7, 16), (κCCols, liftCCols, 11, 7, 16),
    (κCCols, liftCCols, 11, 7, 16), (κCCols, liftCCols, 11, 7, 32),
    (κC22Cols, lift22Cols, 10, 6, 16), (κC22Cols, lift22Cols, 10, 7, 16),
    (κC22Cols, lift22Cols, 10, 7, 16), (κC22Cols, lift22Cols, 10, 7, 16),
    (κC12Cols, lift12Cols, 10, 6, 32), (κC12Cols, lift12Cols, 10, 6, 16),
    (κC12Cols, lift12Cols, 10, 6, 16)]

@[expose] noncomputable def oddK (k : Nat) : Bool :=
  match spec.getD k ([], [], 0, 0, 0) with
  | (cc, lift, n, r, fuel) => oddOK cc lift n r fuel (G.getD k []) (E.getD k []) (J.getD k [])

#kc_each oddK 0 17

theorem cube : cubeOK (E.getD 5 []) = true := by decide +kernel

@[expose] def okH22 (a : Array Nat) : Bool :=
  conj3A22.any fun h => inAutOK h && ((h[0]! == 0 && h[1]! == 1) || (h[0]! == 1 && h[1]! == 0)) &&
    conjToB h a s0Arr22

set_option maxHeartbeats 0 in
theorem h22 : tailOK okH22 κC22Cols lift22Cols 10 (E.getD 10 []) = true := by decide +kernel

end CertificateChecks.KernelHMathieu.Odd

end
