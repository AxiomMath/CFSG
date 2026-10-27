module

public import Certificates.Data.Kernel.GL33T
public import Certificates.Kernel.GL33T.Data

public section

namespace CFSG.KD.GL33T

open CFSG.KC.GL33T

@[expose] def nNodes : Nat := 48

@[expose] def nQ : Nat := 4

@[expose] noncomputable def nodeC (i : Nat) : Bool :=
  nodeK gens mask i (List.getD gens i []) (List.getD recs i []) (List.getD mask i 0)
    (List.getD kind i 9) (List.getD qmask (List.getD q i 0) 0)
    (List.getD qreps (List.getD q i 0) []) (List.getD s1reps i []) (List.getD s1cov i [])
    (List.getD orr i []) (List.getD org i []) (List.getD ori i []) (List.getD ucov i [])
    (List.getD phiw i []) (List.getD ch i [])

@[expose] noncomputable def qC (k : Nat) : Bool :=
  covT (List.getD qmask k 0) (List.getD qreps k []) false (List.getD qcov k [])

@[expose] noncomputable def rootC : Bool :=
  List.getD gens 0 [] == [13285] && Nat.beq (lenK gens) nNodes && Nat.beq (lenK recs) nNodes &&
    Nat.beq (lenK qmask) nQ

end CFSG.KD.GL33T

end
