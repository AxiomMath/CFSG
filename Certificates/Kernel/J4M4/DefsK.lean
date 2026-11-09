module

public import Certificates.Kernel.J4M4.Defs
public import Certificates.Data.Kernel.J4M4SortK

public section

namespace CertificateChecks.KernelJ4M4

open CFSG.KC.J4M4 CFSG.KC.J4Tree CFSG.KC.F2W CFSG.J4Tree.Native CFSG.J4Tree.M4

@[expose] noncomputable def closeKK (s : Nat) : Bool := eqL (msortK (KL.map (actR KG s))) KL

@[expose] noncomputable def headKK : Bool := certHeadK oneK KL KY

@[expose] noncomputable def layKK (n : Nat) : Bool :=
  layerOKK (actR KG) 10 (msortK (keysY (KY.take (n + 1)))) (KY.getD (n + 1) [])

@[expose] noncomputable def smallKK : Bool :=
  certOKK (actR (fBasis.map ccK)) 10 oneK FL FY && closeOKK (actR (fBasis.map ccK)) 10 FL &&
  certOKK (actR ((treeWv 539).map ccK)) (treeWv 539).length oneK WL WY &&
    closeOKK (actR ((treeWv 539).map ccK)) (treeWv 539).length WL &&
  certOKK (actR ((treeBasis 539).map ccK)) (treeBasis 539).length oneK RL RY &&
    closeOKK (actR ((treeBasis 539).map ccK)) (treeBasis 539).length RL &&
  certOKK (actR (y136.map ccK)) y136.length oneK Y1L Y1Y &&
    closeOKK (actR (y136.map ccK)) y136.length Y1L &&
  certOKK (actR (y266.map ccK)) y266.length oneK Y2L Y2Y &&
    closeOKK (actR (y266.map ccK)) y266.length Y2L

theorem closeKS_eq (s : Nat) : closeKS s = closeKK s := by
  unfold closeKS closeKK
  rw [msortK_eq]

theorem headK_eq : headK = headKK := by
  unfold headK headKK
  rw [certHeadK_eq]

theorem layK_eq (n : Nat) : layK n = layKK n := by
  unfold layK layKK
  rw [msortK_eq, layerOKK_eq]

theorem smallK_eq : smallK = smallKK := by
  unfold smallK smallKK
  simp only [certOKK_eq, closeOKK_eq]

end CertificateChecks.KernelJ4M4
