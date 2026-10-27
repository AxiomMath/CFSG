module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.J2GL4 "Certificates/Kernel/J2GL4/data/j2gl4.json.gz" 2141 7090753705155660581
  (mX7 : List (List Nat)) (mY7 : List (List Nat)) (mA5 : List (List Nat)) (mB5 : List (List Nat))
  (mY5 : List (List Nat))

namespace CFSG.KD.J2GL4

@[expose] noncomputable def baseL (i : Nat) : List (List Nat) :=
  cond (Nat.beq i 0) mX7 (cond (Nat.beq i 1) mY7 (cond (Nat.beq i 2) mA5
    (cond (Nat.beq i 3) mB5 mY5)))

end CFSG.KD.J2GL4

end
