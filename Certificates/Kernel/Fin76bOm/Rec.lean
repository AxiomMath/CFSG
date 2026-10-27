module

public import Certificates.Kernel.Fin76bOm.Data
public import Certificates.Kernel.Fin76bOm.J2
public import Certificates.Kernel.Fin76bOm.J3

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelC24608

open CFSG.KC.YoshQ

set_option maxHeartbeats 0 in
theorem j2W_rec : replayK 32 6 32 2000 J2W.GS J2W.cnt J2W.EP J2W.PL J2W.POS J2W.SM J2W.SF = true ∧
    (List.range J2W.cnt).map (fldN J2W.EP (32 * 6)) = J2W.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem j2E_rec : replayK 32 6 32 40 J2E.GS J2E.cnt J2E.EP J2E.PL J2E.POS J2E.SM J2E.SF = true ∧
    (List.range J2E.cnt).map (fldN J2E.EP (32 * 6)) = J2E.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem j2_gs : J2W.GS = (List.range 4).map J2OmT ∧
    J2E.GS = J2W.RL.filter (fun x => eqN 32 6 (pmN 32 6 x x) (J2OmT 4)) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem j3W_rec : replayK 80 7 80 2000 J3W.GS J3W.cnt J3W.EP J3W.PL J3W.POS J3W.SM J3W.SF = true ∧
    (List.range J3W.cnt).map (fldN J3W.EP (80 * 7)) = J3W.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem j3E_rec : replayK 80 7 80 40 J3E.GS J3E.cnt J3E.EP J3E.PL J3E.POS J3E.SM J3E.SF = true ∧
    (List.range J3E.cnt).map (fldN J3E.EP (80 * 7)) = J3E.RL := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem j3_gs : J3W.GS = (List.range 5).map J3OmT ∧
    J3E.GS = J3W.RL.filter (fun x => eqN 80 7 (pmN 80 7 x x) (J3OmT 5)) := by
  decide +kernel

end CertificateChecks.KernelC24608

end
