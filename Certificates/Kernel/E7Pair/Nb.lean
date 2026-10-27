module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.PairDataE7

public section

namespace Certificates.Kernel.E7Pair

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

theorem e7_nb_ok : e7Nb = (List.range (e7W.length + e7R.length)).map fun v =>
    bitsOf (e7W.length + e7R.length) (adjP e7R e7W v) := by
  decide +kernel

end Certificates.Kernel.E7Pair
