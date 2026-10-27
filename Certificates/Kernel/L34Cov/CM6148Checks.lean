module

public import Certificates.Data.Kernel.L34Cov.NfLift
public import Certificates.Kernel.L34Cov.Checks
public import CFSG.LocalAnalysis.OddStandard.ONanIdCMInputs

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.OddStandard.ONanRec.IdCM

@[expose] def code6148 (d : ℕ × ℕ × ℕ) : ℕ := 12 * d.1 + 3 * d.2.1 + d.2.2

@[expose] def cmL : List (List (Fin 6 × Bool) × List (Fin 2 × Bool) × ℕ) :=
  relData.map (fun d => (d.1.toWord, [], code6148 d.2)) ++
    [(invA, [(0, false)], 1), (invB, [(1, false)], 18), (invU, [], 0)]

@[expose] noncomputable def nfLiftsK (uA uB : List (Fin 2 × Bool))
    (L : List (List (Fin 6 × Bool) × List (Fin 2 × Bool) × ℕ)) : Bool :=
  nfLiftsOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab FW uA uB genW L

theorem ch6148p_k : (relData.all (fun d => !(nfOf d.1.toWord).2) && !(nfOf invA).2 &&
    !(nfOf invB).2 && (nfOf invU).2) = true := by
  decide +kernel

theorem ch6148l_k : nfLiftsK uAU uBU cmL = true := by decide +kernel

end CertificateChecks.KernelL34Cov

end
