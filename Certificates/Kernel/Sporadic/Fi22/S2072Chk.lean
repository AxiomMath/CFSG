module

public import Certificates.Data.Kernel.Fi22Syl2072
public import Certificates.Kernel.Sporadic.Fi22.E2065T
public import CFSG.Sporadic.FischerOddCore.Fi22CentData
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

#kc_repo #kc_ktree CFSG.KD.Syl2072 D "Certificates/Kernel/Sporadic/Fi22/data/syl2072.bin" 40 4 42120 11092222007677768418

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2072

open CFSG.KC.Enum CFSG.KS CFSG.KC.Syl2072 CFSG.Sporadic.FischerOddCore

@[expose] noncomputable def sf (s i : Nat) : Nat := (fi22CentSylows.getD s []).getD i 0

@[expose] noncomputable def wf (w i : Nat) : Nat := (fi22CentWitnesses.getD w []).getD i 0

@[expose] noncomputable def off (s : Nat) : Nat :=
  [0, 27, 108, 113, 194, 199, 928, 953, 960, 1041, 1046].getD s 0

@[expose] noncomputable def root (s : Nat) : Nat := [0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0].getD s 0

@[expose] noncomputable def X (s w : Nat) : Nat :=
  Fi22CentT.L (wf (Nat.add (sf s (nat_lit 6)) w) (nat_lit 0))

@[expose] noncomputable def H (s w : Nat) : Nat :=
  Fi22CentT.L (wf (Nat.add (sf s (nat_lit 6)) w) (nat_lit 1))

@[expose] noncomputable def recS (s : Nat) : Bool :=
  bAnd(recK Fi22CentT.L CFSG.KD.Syl2072.D (X s) (sf s (nat_lit 3)) (sf s (nat_lit 4)) (off s)
      (sf s (nat_lit 2)) (sf s (nat_lit 1)) (sf s (nat_lit 7)) (root s),
    allN (sf s (nat_lit 7)) fun w => strictB (H s w) fun h =>
      witK (X s w) h (pinvS (nat_lit 3510) (nat_lit 12) (mask (nat_lit 12)) h) (sf s (nat_lit 1))
        (wf (Nat.add (sf s (nat_lit 6)) w) (nat_lit 3)))

end CertificateChecks.KernelSpor.S2072

#kc_each CertificateChecks.KernelSpor.S2072.recS 0 11

end
