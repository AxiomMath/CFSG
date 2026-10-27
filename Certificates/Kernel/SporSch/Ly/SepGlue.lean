module

public import Certificates.Data.Kernel.SporSch.LySeed
public import Certificates.Data.Kernel.LyOmega.Base
public import Certificates.Kernel.SporSch.Ly.SeedData
public import CFSG.Sporadic.Schreier.LyCheckSep
import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.SporSch.Ly.SepGen
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporSch.LySeven
public import Certificates.Kernel.SporSch.Ly.Seed8132
public import Mathlib
public import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
public import CFSG.Sporadic.Ly.FaithSpec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LySep

open CFSG.KC.Enum CFSG.KC.LySeed Matrix
open CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CertificateChecks.KernelSporSch.LyBS CertificateChecks.KernelSporSch.LyBSF CFSG.KD.OrdLy

local notation "U" X:max => CFSG.KS.SporSch.LyM.unpackL 111 12 1332 X

end CertificateChecks.KernelSporSch.LySep

end
