module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Fi23Cov.Base
public import Certificates.Data.Kernel.Fi23Cov.Defs

#kc_repo #kc_json_gz CFSG.KD.Fi23Cov.Th "Certificates/Kernel/Fi23Cov/data/three.json.gz" 7366
  8358992658937212085
  (T : List (List Nat)) (AG : List Nat) (AX : List Nat) (AZa : List Nat) (AHa : List Nat)
  (AZb : List Nat) (AHb : List Nat) (BG : List Nat) (BX : List Nat)
  (CY1 : List Nat) (CY2 : List Nat) (CG1 : List Nat) (CG2 : List Nat) (CM : List (List Nat))
  (CC : List (List Nat)) (CR : List (List Nat))
  (DY1 : List Nat) (DY2 : List Nat) (DG1 : List Nat) (DG2 : List Nat) (DM : List (List Nat))
  (DC : List (List Nat)) (DR : List (List Nat))

public section

namespace CFSG.KD.Fi23Cov

open CFSG.KC.Fi23Cov

@[expose] noncomputable def gens : Bool := genOK E

@[expose] noncomputable def rep (i : Nat) : Bool := tOK E Th.T i

@[expose] noncomputable def ctl0 : Bool :=
  ctlA E (nthW Th.T 0) Th.AG Th.AX Th.AZa Th.AHa Th.AZb Th.AHb

@[expose] noncomputable def ctl1 : Bool := ctlB E (nthW Th.T 1) Th.BG Th.BX

@[expose] noncomputable def cH : Bool :=
  clH E (nthW Th.T 2) Th.CY1 Th.CY2 Th.CG1 Th.CG2 [39] Th.CM 16 Th.CR 13

@[expose] noncomputable def cL (j : Nat) : Bool := clL E Th.CY1 Th.CY2 4 Th.CM j

@[expose] noncomputable def cS (k : Nat) : Bool := stOK E Th.CM Th.CC Th.CR k

@[expose] noncomputable def cP : Bool := prOK E Th.CR [40]

@[expose] noncomputable def dH : Bool :=
  clH E (nthW Th.T 3) Th.DY1 Th.DY2 Th.DG1 Th.DG2 [40] Th.DM 16 Th.DR 10

@[expose] noncomputable def dL (j : Nat) : Bool := clL E Th.DY1 Th.DY2 4 Th.DM j

@[expose] noncomputable def dS (k : Nat) : Bool := stOK E Th.DM Th.DC Th.DR k

@[expose] noncomputable def dP : Bool := prOK E Th.DR [39]

end CFSG.KD.Fi23Cov

end
