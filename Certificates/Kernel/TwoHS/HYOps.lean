module

public import Certificates.Kernel.TwoHS.HYWords
public import Certificates.Data.Kernel.PkPow

public section

namespace CFSG.KD.TwoHS

@[expose] noncomputable def WKI (wd : List Nat) : Nat := WK wd.reverse

@[expose] noncomputable def EVK (G GI : Fin 6 → Nat) (wd : List (Fin 6 × Bool)) : Nat :=
  wd.foldl (fun acc l => pc acc (cond l.2 (G l.1) (GI l.1))) idK

@[expose] noncomputable def pw (p e : Nat) : Nat := CFSG.KC.PkPow.ppw 11200 14 p e

@[expose] noncomputable def fx (p : Nat) : Nat := CFSG.KC.PkPow.nfix 11200 14 p

end CFSG.KD.TwoHS

end
