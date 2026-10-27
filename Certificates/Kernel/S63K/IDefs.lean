module

public import Certificates.Kernel.S63K.IData
public import Certificates.Kernel.S63K.HData
public import Certificates.Data.Kernel.S63K.ConjTree
public import Certificates.Data.Kernel.SporSch.Co1Mat

public section

namespace CertificateChecks.KernelS63.ID

open CFSG.KC.S63K CFSG.KC.Enum CFSG.KS.SporSch.M24

@[expose] noncomputable def cj (x l : Nat) : Nat := cjStepK G x l

@[expose] noncomputable def ch21111T (b : Nat) : Bool :=
  allN 1274 fun r => treeAtK cj TP TQ 8 (Nat.add (Nat.mul 1274 b) r)

@[expose] noncomputable def ch21111S (b : Nat) : Bool :=
  allN 1274 fun r => distAtK TP TS 68796 (Nat.add (Nat.mul 1274 b) r)

@[expose] noncomputable def tagK (i : Nat) : Bool :=
  tagAtK idM ZP 819 TP 68796 (CertificateChecks.KernelS63.HD.TP i) (UT i)

@[expose] noncomputable def ch21111U (b : Nat) : Bool :=
  allN 1024 fun r => tagK (Nat.add (Nat.mul 1024 b) r)

end CertificateChecks.KernelS63.ID

end
