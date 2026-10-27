module

public import Certificates.Kernel.Sporadic.SuzH.Data
public import Certificates.Kernel.Sporadic.Suz.Chain2306
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Spor.Raw
import CFSG.Sporadic.SuzI301Cover.Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def X (i : Nat) : Nat := SuzHS.F (i + 1)

@[expose] noncomputable def pw (p e : Nat) : Nat := ppow 1782 11 (mask 11) (pidn 1782 11) p e

@[expose] noncomputable def pc3 (a b c : Nat) : Nat :=
  pcomp 1782 11 (mask 11) a (pcomp 1782 11 (mask 11) b c)

@[expose] noncomputable def conjV (k i : Nat) (v : List Nat) : Bool :=
  Nat.beq (pc3 (SuzHN.F k) (X i) (pinvS 1782 11 (mask 11) (SuzHN.F k)))
    (pc3 (pw (X 0) v[0]!) (pw (X 1) v[1]!) (pw (X 2) v[2]!))

@[expose] noncomputable def conjK (k i : Nat) : Bool :=
  conjV k i ((CFSG.Sporadic.SuzI301Cover.Native.nMats[k]!)[i]!)

@[expose] noncomputable def siftS (G : Nat) : Bool :=
  siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 G

theorem kPerm : (permB 1782 11 (X 0) && permB 1782 11 (X 1) && permB 1782 11 (X 2) &&
    permB 1782 11 (SuzHN.F 0) && permB 1782 11 (SuzHN.F 1)) = true := by quickRfl

theorem kSift0 : siftS (SuzHN.F 0) = true := by quickRfl

theorem kSift1 : siftS (SuzHN.F 1) = true := by quickRfl

theorem kConj00 : conjK 0 0 = true := by quickRfl

theorem kConj01 : conjK 0 1 = true := by quickRfl

theorem kConj02 : conjK 0 2 = true := by quickRfl

theorem kConj10 : conjK 1 0 = true := by quickRfl

theorem kConj11 : conjK 1 1 = true := by quickRfl

theorem kConj12 : conjK 1 2 = true := by quickRfl

end CertificateChecks.KernelSpor.SuzH

end
