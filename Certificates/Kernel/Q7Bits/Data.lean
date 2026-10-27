module

public import Certificates.Data.Kernel.Q7Bits.Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.Q7Bits "Certificates/Kernel/Q7Bits/data/q7lv.json.gz" 174615
  9629211764008888248 (rt : List Nat) (lv : List (List (List Nat)))

public section

namespace CFSG.KD.Q7Bits

open CFSG.Certificates.Kernel.Q7Bits CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

@[expose] noncomputable def rowOK (i : Nat) : Bool := rowCheck q7RepsData[i]! (rt.getD i 0) (lv.getD i [])

end CFSG.KD.Q7Bits
