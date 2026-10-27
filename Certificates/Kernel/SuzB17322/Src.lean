module

public import Certificates.Data.TabSuzB

public section

namespace CertificateChecks.KernelSuzB17322

open CFSG.HardMathSupport.Dickson.I271.TabSuzB CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

@[expose] def aGs : Array (Array Nat) := aGens ()

@[expose] def hT : Array (Array Nat) :=
  #[#[1077, 992, 1501, 1062, 1060, 1639], #[178, 415, 1767, 954, 1010, 880],
    #[1054, 341, 254, 784, 294, 312], #[1129, 570, 258, 1413, 1326, 1367],
    #[0, 1, 2, 134, 290, 1286], #[519, 528, 921, 795, 971, 869],
    #[1032, 380, 1290, 1269, 791, 1750], #[1290, 1032, 380, 1576, 1415, 525],
    #[1395, 529, 42, 1437, 1448, 288]]

@[expose] def hGs : Array (Array Nat) :=
  let L := levels ()
  hT.map (rebuild L)

@[expose] def cGs : Array (Array Nat) := #[hGs[5]!, hGs[2]!]

@[expose] def qGs : Array (Array Nat) := hGs.extract 1 4

@[expose] def bGs : Array (Array Nat) := #[hGs[4]!, hGs[6]!, hGs[7]!, hGs[8]!]

@[expose] def yArr : Array Nat := hGs[4]!

@[expose] def keys : Array Nat := aKeys.toArray

@[expose] def bKeys : Array Nat := CFSG.Sporadic.SuzOddCore.smallBaseNat.toArray

@[expose] def ps : List Nat := CFSG.Sporadic.SuzOddCore.smallBaseNat

end CertificateChecks.KernelSuzB17322

end
