
module

public import Certificates.Kernel.SporSch.J4S.FiveT
public import Certificates.Kernel.SporSch.J4S.GenProf
public import Certificates.Data.Kernel.SporSch.J4SProf
meta import CFSG.Sporadic.Schreier.J4SProfile
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_table CertificateChecks.KernelSporSch.J4PT CFSG.Sporadic.J4Schreier.profTable 24 5

#kss_prof11 CertificateChecks.KernelSporSch.J4PS

namespace CertificateChecks.KernelSporSch.J4Profile

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CertificateChecks.KernelSporSch

@[expose] noncomputable def pf (s : Nat) : Bool := Nat.beq (sliceB J4E.T J4SQ.T J4CT.T s) (J4PS s)

@[expose] noncomputable def dK (a b : Nat) : Bool :=
  bIf(Nat.beq b a, true, Bool.not (allN 5 (fun j => Nat.beq (ent 24 (J4PT b) j) (ent 24 (J4PT a) j))))

end CertificateChecks.KernelSporSch.J4Profile

#kss_slices CertificateChecks.KernelSporSch.J4PSC CertificateChecks.KernelSporSch.J4Profile.pf 1 128

namespace CertificateChecks.KernelSporSch.J4Profile

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CertificateChecks.KernelSporSch

theorem tot : profK J4PT (sumK J4PS 128) = true := by quickRfl

theorem sqb : allN 1024 (fun e => Nat.blt (J4SQ.T e) 1024) = true := by quickRfl

theorem ctb : allN 1024 (fun e => Nat.blt (J4CT.T e) 16) = true := by quickRfl

theorem dist : allN 32 (fun b => bAnd(dK 5 b, bAnd(dK 6 b, bAnd(dK 7 b, bAnd(dK 8 b, dK 17 b))))) =
    true := by quickRfl

end CertificateChecks.KernelSporSch.J4Profile

end
