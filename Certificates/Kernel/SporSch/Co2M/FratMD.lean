
module

public import Certificates.Kernel.SporSch.Co2M.Local
public import CFSG.Sporadic.Co2Schreier.SylowCheckInputs

public section

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier

@[expose] noncomputable def prodPT (T : List (ℕ × ℕ)) (l : List ℕ) : ℕ × ℕ :=
  l.foldl (fun acc i => cmpP acc (T.getD i (0, 0))) (I22, I22)

@[expose] noncomputable def fratT0 : List (ℕ × ℕ) :=
  fratSpecs.map fun l => cmpP (prodPT sT l) (prodPT sT l)

@[expose] noncomputable def fratT : List (ℕ × ℕ) := extP mmK I22 fratT0 fratDerivs

@[expose] noncomputable def yBT : List (ℕ × ℕ) := yBasisSpecs.map (prodPT sT)

@[expose] noncomputable def yP (w : ℕ) : ℕ × ℕ := prodPT yBT (bits5 w)

end CertificateChecks.KernelSporSch.Co2M

end
