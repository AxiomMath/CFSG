module

public import Certificates.Kernel.SporSch.Mathieu.M12Data
public meta import Certificates.Kernel.SporSch.Mathieu.M12Data
public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.GH74.BTFinCkM12
public meta import Certificates.Data.GH74.BTFinCkM12
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12Odd

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M12OC Certificates.BTFinCk.M12

meta def repA (k : Nat) : Array Nat := evalW 12 #[tAM, tBM] (rows.getD k default).2.1

meta def gensA (k : Nat) : Array (Array Nat) :=
  ((rows.getD k default).2.2.2.2.map (evalW 12 #[tAM, tBM])).toArray

meta def gAB : Array (Array Nat) := #[tAM, tBM]

meta def reps3 : List (Array Nat) := [repA 0, repA 1]

meta def reps5 : List (Array Nat) := [repA 2]

meta def reps11 : List (Array Nat) := [repA 3, repA 4]

meta def idM : Array Nat := Array.range 12

meta def idsA (k : Nat) : Array (Array Nat) := Array.replicate (gensA k).size idM

meta def g0 : Array (Array Nat) := gensA 0
meta def g1 : Array (Array Nat) := gensA 1
meta def g2 : Array (Array Nat) := gensA 2
meta def g3 : Array (Array Nat) := gensA 3
meta def g4 : Array (Array Nat) := gensA 4
meta def i0 : Array (Array Nat) := idsA 0
meta def i1 : Array (Array Nat) := idsA 1
meta def i2 : Array (Array Nat) := idsA 2
meta def i3 : Array (Array Nat) := idsA 3
meta def i4 : Array (Array Nat) := idsA 4

end CertificateChecks.KernelSporSch.M12Odd

end
