module

public import Certificates.Data.PhilipHallSp6Cover
import CFSG.Certificates.Kernel.Common.JsonGzEval
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

#kc_repo #kc_json_gz_eval CertificateChecks.KernelSp6Cover
  "Certificates/Kernel/Sp6Cover/Data/sp6cover.json.gz" 2767 18085289626975229593
  (cX : Array (Array Nat)) (cBase : Array Nat) (cWN : List (List Nat)) (ew : List (List Nat))
  (nw : List (List Nat))

public section

namespace CertificateChecks.KernelSp6Cover

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData

@[expose] def yBaseA : Array Nat := (yBase.map Fin.val).toArray

@[expose] def yWD : List (List Int) := yW.toList.drop 3

@[expose] def cS : Array (Array Nat) := cA ++ cX

@[expose] def decL (e : Nat) : Int := if e % 2 = 0 then Int.ofNat (e / 2) else -Int.ofNat (e / 2)

@[expose] def cWD : List (List Int) := cWN.map fun w => w.map decL

end CertificateChecks.KernelSp6Cover
