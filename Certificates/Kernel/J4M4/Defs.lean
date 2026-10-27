module

public import Certificates.Kernel.J4M4.Data
public import Certificates.Data.Kernel.J4M4Code
public import Certificates.Data.CFSGNative.J4Tree.M4Type

public section

namespace CertificateChecks.KernelJ4M4

open CFSG.KC.J4M4 CFSG.KC.J4Tree CFSG.KC.F2W CFSG.J4Tree.Native CFSG.J4Tree.M4

@[expose] noncomputable def closeKS (s : Nat) : Bool := eqL (msort (KL.map (actR KG s))) KL

@[expose] noncomputable def headK : Bool := certHead oneK KL KY

@[expose] noncomputable def layK (n : Nat) : Bool :=
  layerOK (actR KG) 10 (msort (keysY (KY.take (n + 1)))) (KY.getD (n + 1) [])

@[expose] noncomputable def boundK : Bool :=
  KL.all (fun k => Nat.blt k (2 ^ 144)) && Nat.beq KL.length 16384 && eqL KG (kGens.map ccK)

@[expose] noncomputable def smallK : Bool :=
  certOK (actR (fBasis.map ccK)) 10 oneK FL FY && closeOK (actR (fBasis.map ccK)) 10 FL &&
  certOK (actR ((treeWv 539).map ccK)) (treeWv 539).length oneK WL WY &&
    closeOK (actR ((treeWv 539).map ccK)) (treeWv 539).length WL &&
  certOK (actR ((treeBasis 539).map ccK)) (treeBasis 539).length oneK RL RY &&
    closeOK (actR ((treeBasis 539).map ccK)) (treeBasis 539).length RL &&
  certOK (actR (y136.map ccK)) y136.length oneK Y1L Y1Y &&
    closeOK (actR (y136.map ccK)) y136.length Y1L &&
  certOK (actR (y266.map ccK)) y266.length oneK Y2L Y2Y &&
    closeOK (actR (y266.map ccK)) y266.length Y2L

@[expose] noncomputable def sqK : Bool :=
  eqL (KL.filter fun k => eqC (mulW 12 k k) oneK) (IR.map fun r => r.1)

@[expose] noncomputable def irOK (r : Nat × Nat × List (List (Nat × Nat × Nat))) : Bool :=
  certOK (actC KG KGI) 10 r.1 (CL.getD r.2.1 []) r.2.2 &&
    (Nat.beq (CL.getD r.2.1 []).length 4 == false || FL.contains r.1)

@[expose] noncomputable def irK (n : Nat) : Bool := ((IR.drop (256 * n)).take 256).all irOK

@[expose] noncomputable def clOK (C : List Nat) : Bool :=
  closeOK (actC KG KGI) 10 C && C.all fun k => Nat.blt k (2 ^ 144)

@[expose] noncomputable def clK (n : Nat) : Bool := ((CL.drop (64 * n)).take 64).all clOK

end CertificateChecks.KernelJ4M4
