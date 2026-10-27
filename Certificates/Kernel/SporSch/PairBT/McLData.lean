module

public import Certificates.Kernel.SporSch.Pair.McLCheck
public import CFSG.Sporadic.Schreier.PairMcLTotal2Inputs
public import CFSG.Certificates.Kernel.SporSch.PairBTSound
public meta import CFSG.Sporadic.Schreier.PairMcLCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLBT

open CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MBT CFSG.Sporadic.Schreier.PairMcL

meta def tAM : Array Nat := CFSG.Sporadic.Schreier.mclStrongArrs[0]!

meta def tBM : Array Nat := CFSG.Sporadic.Schreier.mclStrongArrs[1]!

meta def repsM : Array (Array Nat) := #[tAM]

@[expose] noncomputable def tA : List Nat := (unpack 275 9 (PMcL.S 0)).toList

@[expose] noncomputable def tB : List Nat := (unpack 275 9 (PMcL.S 1)).toList

@[expose] def ws1 : List (List Nat × Nat) := condWords conds

@[expose] def ws2 : List (List Nat × Nat) := condWords conds2

end CertificateChecks.KernelSporSch.McLBT

end
