module

public import Certificates.Data.Kernel.U43Twin.Wit
public import Certificates.Kernel.U43Twin.Data
public import Certificates.Kernel.U43Pk.Data
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_blocked_root CertificateChecks.KernelU43Twin.FxTT
  "Certificates/Kernel/U43Twin/data/fx_pts.bin"
  4 7 340282366920938463463374607431768211455 7744 6331149910515674787

#kc_repo #kc_blocked_root CertificateChecks.KernelU43Twin.WitT
  "Certificates/Kernel/U43Twin/data/wit_tab.bin"
  5 5 4294967295 55680 1398830730431384647

namespace CertificateChecks.KernelU43Twin

open CFSG.KC.Enum CFSG.KD.U43Pk CFSG.KD.U43Twin

@[expose] noncomputable def FX (i : Nat) : Nat := FxTT i

@[expose] noncomputable def SX (c k : Nat) : Nat := FxTT (Nat.add 100 (Nat.add (Nat.mul 4 k) c))

@[expose] noncomputable def EL (s u : Nat) : Nat := FxTT (Nat.add 36 (Nat.add (Nat.mul 8 s) u))

@[expose] noncomputable def GO (g : Nat) : Nat := FxTT (Nat.add 36 g)

@[expose] noncomputable def L2 (m : Nat) : Nat := FxTT (Nat.add 52 m)

@[expose] noncomputable def L1 (m : Nat) : Nat := FxTT (Nat.add 76 m)

@[expose] noncomputable def IW (i : Nat) : Nat := WitT i

@[expose] noncomputable def SP (i : Nat) : Nat := WitT (Nat.add 128 i)

@[expose] noncomputable def R (k : Nat) : Nat := WitT (Nat.add 1152 k)

@[expose] noncomputable def QW (m : Nat) : Nat := WitT (Nat.add 1248 m)

@[expose] noncomputable def PW (i : Nat) : Nat := WitT (Nat.add 10464 i)

@[expose] noncomputable def CW (i : Nat) : Nat := WitT (Nat.add 11616 i)

@[expose] noncomputable def DW (i : Nat) : Nat := WitT (Nat.add 12768 i)

@[expose] noncomputable def ch397503inv (q : Nat) : Bool :=
  allBlk (Nat.mul 64 q) (fun i => strictB i fun i => invK TT FX IW T0K i) 64

@[expose] noncomputable def ch397503sq (q : Nat) : Bool :=
  allBlk (Nat.mul 64 q) (fun i => strictB i fun i => sqK KernelU43Pk.T SP R T0K i) 64

@[expose] noncomputable def ch397503sqp (q : Nat) : Bool :=
  allBlk (Nat.mul 32 q) (fun k => strictB k fun k => sqpK KernelU43Pk.T R SX (FX 35) T0K k) 32

@[expose] noncomputable def ch397503q8 (k : Nat) : Bool :=
  allBlk 0 (fun l => strictB (QW (Nat.add (Nat.mul 96 k) l)) fun w =>
    q8pK KernelU43Pk.T R SX EL w k l) 96

@[expose] noncomputable def ch397503perm (q : Nat) : Bool :=
  allBlk (Nat.mul 32 q) (fun i => strictB i fun i => permK CT PW EL (FX 37) (FX 40) i) 32

@[expose] noncomputable def ch397503cent (q : Nat) : Bool :=
  allBlk (Nat.mul 64 q)
    (fun i => strictB i fun i => centK CT CW (FX 37) (FX 40) (FX 45) (FX 48) L1 L2 i) 64

@[expose] noncomputable def ch397503odd (q : Nat) : Bool :=
  allBlk (Nat.mul 32 q) (fun i => strictB i fun i => oddK CT DW GO i) 32

end CertificateChecks.KernelU43Twin

end
