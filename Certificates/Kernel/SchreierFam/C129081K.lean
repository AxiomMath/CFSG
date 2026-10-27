module

public import Certificates.Kernel.SchreierFam.Co2Slp
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2HeisData
public import Certificates.Kernel.SporSch.Co2M.Class

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.Co2Slp

open CertificateChecks.KernelSporSch.Co2M CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2

@[expose] noncomputable def heisT : List (ℕ × ℕ) := aT ++ [zP, tP, uP]

@[expose] noncomputable def heisE : List (ℕ × ℕ) := CFSG.KS.MatRep.extP CFSG.KS.Co2M.mmK
  CFSG.KS.Co2M.I22 heisT heisSlp

theorem heis_k : slpM heisE heisT heisT.length heisSlp heisEqs heisNes = true := by decide +kernel

end CertificateChecks.KernelSchreierFam.Co2Slp
