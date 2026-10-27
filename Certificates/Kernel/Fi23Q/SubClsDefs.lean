module

public import Certificates.Data.Kernel.Fi23Q.SubCls
public import Certificates.Kernel.Fi23Q.SubDefs
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.Fi23Q "Certificates/Kernel/Fi23Q/data/cls.items.gz" 12166 10131625519534092196
  npV[] npB[] npQ[] npC[] npN[] npW[] clsR clsMt clsL[] clsB[] clsK[] clsX[] clsD3[]
  negR negL[] negB[] negNPV[] negA

public section

namespace CFSG.KD.Fi23Q

open CFSG.KC.Fi23Q

@[expose] noncomputable def npRow (k : Nat) : Bool :=
  npK (npV.getD k (nat_lit 0)) (npB.getD k (nat_lit 0)) (npQ.getD k (nat_lit 0))
    (npC.getD k (nat_lit 0)) (npN.getD k (nat_lit 0)) (npW.getD k (nat_lit 0))

@[expose] noncomputable def clsE : Bool := clsEK SubCJ
@[expose] noncomputable def clsRt : Bool := clsRK SubPW SubCJ clsR
@[expose] noncomputable def clsM : Bool := clsMK SubCJ clsMt
@[expose] noncomputable def clsLt : Bool := clsLK clsR clsL
@[expose] noncomputable def clsC : Bool := clsCK clsMt clsL clsB
@[expose] noncomputable def clsKd : Bool := clsKK clsL clsK
@[expose] noncomputable def clsG : Bool := clsGK clsMt npV clsB clsK clsX
@[expose] noncomputable def clsH : Bool := clsHK npV
@[expose] noncomputable def clsA : Bool := clsAK SubPW SubCJ clsMt npV clsL clsB clsK clsX
@[expose] noncomputable def clsBt : Bool := clsBK SubPW SubCJ clsMt npV clsL clsB clsK clsD3

@[expose] noncomputable def negClsR : Bool := !clsRK SubPW SubCJ negR
@[expose] noncomputable def negClsL : Bool := !clsLK clsR negL
@[expose] noncomputable def negClsB : Bool := !clsCK clsMt clsL negB
@[expose] noncomputable def negClsH : Bool := !clsHK negNPV
@[expose] noncomputable def negClsA : Bool :=
  !bad2 SubPW SubCJ clsMt npV (clsL.getD (nat_lit 25) (nat_lit 0)) (clsB.getD (nat_lit 25) (nat_lit 0)) negA
@[expose] noncomputable def negClsD : Bool :=
  !bad3 SubPW SubCJ clsMt npV (clsL.getD (nat_lit 39) (nat_lit 0)) (clsB.getD (nat_lit 39) (nat_lit 0))
    (nat_lit 1) (nat_lit 16) (nat_lit 64) (clsD3.getD (nat_lit 3) (nat_lit 0)) (clsD3.getD (nat_lit 4) (nat_lit 0))

end CFSG.KD.Fi23Q

end
