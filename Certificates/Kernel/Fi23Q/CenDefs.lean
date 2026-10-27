module

public import Certificates.Data.Kernel.Fi23Q.Census
public import Certificates.Kernel.Fi23Q.Tabs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.Fi23Q "Certificates/Kernel/Fi23Q/data/census.json.gz"
  2620 2954395278917701193 (RV : Nat) (CR : Nat)

namespace CFSG.KD.Fi23Q

open CFSG.KC.Fi23Q

@[expose] noncomputable def cosK (i D : Nat) : Bool := cosChk H RV (nat_lit 145) i D

@[expose] noncomputable def repK (ρ MV ncl CV WD XD : Nat) : Bool :=
  repChk H RV CR (nat_lit 198) ρ MV ncl CV WD XD

end CFSG.KD.Fi23Q

end
