module

public import Certificates.Kernel.He7030.Defs
public import Certificates.Kernel.He2111.Data
public import Certificates.Kernel.SporSch.HeT.Out2116
public import Certificates.Data.Kernel.He2111K

public noncomputable section

namespace CFSG.KD.He7030

open CFSG.KC.PtEnum CFSG.KC.E64F CFSG.KC.SLDc CFSG.KD.HeDc CFSG.KC.He2111 CFSG.KS.PEnum

@[expose] def BR (q : Nat) : Nat := e14 (CFSG.KD.He2111.BrT.F 0) q

@[expose] def BI (q : Nat) : Nat := r32 CFSG.KD.He2111.PI q

@[expose] def RR (q : Nat) : Nat := e14 CertificateChecks.KernelSporSch.HeO16.R q

@[expose] def uJ (q : Nat) : Nat := BR (RR (RR (RR (RR (RR (BI q))))))

@[expose] def xiF (f : Nat → Nat) (p : Nat) : Nat :=
  wordF L Dt.w (uJ (f (uJ (wordF L (invW Dt.w) p))))

@[expose] def aChk : Bool :=
  (Dt.w.all fun l => Nat.blt l 2) && invB (wordF L Dt.w) (wordF L (invW Dt.w)) &&
  ([2, 3, 4, 5].all fun l => labF (xiF (L l)) Δ == Δ) &&
  ([3, 4].all fun k => !((Om k).lbl.toList.contains (labF (xiF (wordF L (mW k))) Δ)))

end CFSG.KD.He7030

end
