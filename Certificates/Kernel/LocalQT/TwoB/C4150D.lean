module

public import Certificates.Kernel.LocalQT.SV.C4126T
public import Certificates.Kernel.LocalQT.MulHD
public import Certificates.Data.Kernel.LocalQT.CommQ
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHSTwoBInputs
public meta import CFSG.Sporadic.SmallOddCore.LocalSpec

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.TB

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.QuasithinUnique.Id2519.SporHS

meta def idM : Array Nat := idTab 3850

meta def ids2M : Array (Array Nat) := #[idM, idM]

meta def yM : Array (Array Nat) := (twoBY.map natArr).toArray

meta def yiM : Array (Array Nat) := yM.map (CFSG.Monster.B.Co2.Native.invCand 3850)

meta def cM : Array (Array Nat) := (twoBGens.map natArr).toArray

meta def ciM : Array (Array Nat) := cM.map (CFSG.Monster.B.Co2.Native.invCand 3850)

meta def aRecM : Array (Array Nat) :=
  (bfs (fun j t => conjTab 3850 idM yM[j]! t) 2 idM 400).tabs

meta def aClM : Array (Array Nat) :=
  (aRecM.map fun x => (yM ++ yiM).map fun g => comp 3850 x g).flatten

meta def aNmM : Array (Array Nat) :=
  (aRecM.map fun x => (List.range 4).toArray.map fun j => conjTab 3850 cM[j]! ciM[j]! x).flatten

meta def aCmM : Array (Array Nat) :=
  ((List.range 4).toArray.map fun a => (List.range 4).toArray.map fun b =>
    comp 3850 (comp 3850 (comp 3850 cM[a]! cM[b]!) ciM[a]!) ciM[b]!).flatten

#kmulh_d CFSG.KD.LQT.TB.Y 3850 12 ids2M yM idM 400
#kmisc_packarrs CFSG.KD.LQT.TB.YI yiM 12
#kfind_d CFSG.KD.LQT.TB.YCl aRecM aClM
#kfind_d CFSG.KD.LQT.TB.YNm aRecM aNmM
#kfind_d CFSG.KD.LQT.TB.YCm aRecM aCmM

end CFSG.KD.LQT.TB

namespace CFSG.KD.LQT.TB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KD.LQT.C4126

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 3850 12 (mask 12) p q

@[expose] noncomputable def idK : Nat := pidn 3850 12

@[expose] noncomputable def cL (l : Nat) : Nat := HC.F (Nat.add (nat_lit 12) l)

@[expose] noncomputable def cC (j : Nat) : Nat := HC.F (Nat.add (nat_lit 13) j)

@[expose] noncomputable def cCI (j : Nat) : Nat := HCI (Nat.add (nat_lit 13) j)

end CFSG.KD.LQT.TB

end
