module

public import Certificates.Data.Kernel.Fi23Nt.TabDefs
public import Certificates.Kernel.Fi23Nt.DataB
public import Certificates.Kernel.Fi23Nt.DataE
public import Certificates.Kernel.Fi23Nt.DataM
public import Certificates.Kernel.Fi23Nt.DataT

public section

namespace CFSG.KD.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23Nt

@[expose] noncomputable def subHB : Bool := subHK eBN tBA

@[expose] noncomputable def subHC : Bool := subHK eCN tCA

@[expose] noncomputable def subSlOf (n PAR : Nat) (LT : List Nat) (A s : Nat) : Bool :=
  strictB (mskK A) fun M => allBlk (Nat.mul s (nat_lit 9)) (subIK n PAR LT A M) (nat_lit 9)

@[expose] noncomputable def subBSl (s : Nat) : Bool := subSlOf eBN eBPar eBLt tBA s

@[expose] noncomputable def subCSl (s : Nat) : Bool := subSlOf eCN eCPar eCLt tCA s

@[expose] noncomputable def cosBSl (s : Nat) : Bool :=
  allBlk (Nat.mul s (nat_lit 81)) (cosIK eBN eBPar eBLt tBA tBR tBNr tBD) (nat_lit 81)

@[expose] noncomputable def cosCSl (s : Nat) : Bool :=
  allBlk (Nat.mul s (nat_lit 81)) (cosIK eCN eCPar eCLt tCA tCR tCNr tCD) (nat_lit 81)

@[expose] noncomputable def centB : Bool :=
  allN tBNr fun c => centIK eBN eBPar eBLt tBA (nat_lit 10) (lnK (nat_lit 16) tBR c)

@[expose] noncomputable def centC : Bool :=
  allN tCNr fun c => centIK eCN eCPar eCLt tCA (nat_lit 10) (lnK (nat_lit 16) tCR c)

@[expose] noncomputable def zB : Bool := zK eBN eBPar eBLt tBA (nat_lit 4)

@[expose] noncomputable def lnkB : Bool := lnkK eBW eBPar eBN tBA fixIdx fixW

@[expose] noncomputable def lnkC : Bool :=
  bAnd(lnkK eCW eCPar eCN tCA tCY yW, lnkHK eCW eCPar eCN tCA hW aGen bW)

@[expose] noncomputable def genC : Bool := genK eCN eCPar eCLt tCA aGen tCE

end CFSG.KD.Fi23Nt

end
