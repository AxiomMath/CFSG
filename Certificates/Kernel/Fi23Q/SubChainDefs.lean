module

public import Certificates.Data.Kernel.Fi23Q.SubChain
public import Certificates.Kernel.Fi23Q.SubDefs
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.Fi23Q "Certificates/Kernel/Fi23Q/data/sub_chain.items.gz" 1080 18124004727270743388
  sp[3] sV0[] sV1[] sV2[]

public section

namespace CFSG.KD.Fi23Q

open CFSG.KC.Pc3 CFSG.KC.Fi23K CFSG.KC.Fi23Q

@[expose] noncomputable def chainSL : List (Nat × List Nat) := [(sp0, sV0), (sp1, sV1), (sp2, sV2)]

@[expose] noncomputable def imgS (v x : Nat) : Nat := wv H (swR (nat_lit 9) SubV v) x

@[expose] noncomputable def chainSK : Bool := chainG imgS (vecOK (nat_lit 9)) chainSL

@[expose] noncomputable def negSDup : Bool := !chainG imgS (vecOK (nat_lit 9)) [(sp2, 0 :: sV2)]
@[expose] noncomputable def negSFix : Bool :=
  !chainG imgS (vecOK (nat_lit 9)) [(sp2, sV2), (sp1, sV1)]
@[expose] noncomputable def negSVec : Bool := !chainG imgS (vecOK (nat_lit 9)) [(sp2, [3])]

end CFSG.KD.Fi23Q

end
