module

public import Certificates.Kernel.Misc.Sp4Cen.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.Sp4Cen

open CFSG.KD.Sp4Cen CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4 CFSG.KC.Misc.Clos

theorem sp4_gen_ok : andB (invOK S0) (invOK S1) = true := by quickRfl

theorem sp4_inv_ok : invK RI = true := by quickRfl

theorem sp4_ri_ok : allN (nat_lit 316) (riAt RI R0 R1 REPS0 REPS1) = true := by quickRfl

theorem sp4_srch0_ok : allL REPS0 (srchK RI LF (nat_lit 12) R0) = true := by quickRfl

theorem sp4_srch1_ok : allL REPS1 (srchK RI LF (nat_lit 12) R1) = true := by quickRfl

theorem sp4_leaf_ok : allN (nat_lit 12) (leafAt LF LC LW W0 S0 S1) = true := by quickRfl

theorem sp4_sb_ok : allN (nat_lit 720) (fun k => andB (treeAt mul4F id4 SG2 2 SBE SBP k)
    (andB (sortAt (nat_lit 720) SBE SBS k) (closedAt mul4F SG2 2 (nat_lit 720) SBE SBC k))) = true := by
  quickRfl

theorem sp4_form_ok : andB (Nat.beq (FM 0) W0) (allN (nat_lit 28) (formAt FM FG FP FC SG2 W0)) = true := by
  quickRfl

theorem sp4_wit_ok : witK F5 F5I X3 X3I = true := by quickRfl

end CertificateChecks.KernelMisc.Sp4Cen

end
