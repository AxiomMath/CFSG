module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.Fi22
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LQT.Fi22 CFSG.SectionRank.Native.fi22Data 3 77
  CFSG.Blueprint.NativeSporadic.Fi22Seed1 CFSG.Blueprint.NativeSporadic.Fi22Seed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem fi22_elem : ∃ E : Subgroup NativeSporadic.Fi22, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have h := elem_sound _ CFSG.KD.LQT.Fi22.lay_ok CFSG.KD.LQT.Fi22.decA CFSG.KD.LQT.Fi22.decB
    CFSG.KD.LQT.Fi22.one CFSG.KD.LQT.Fi22.steps CFSG.KD.LQT.Fi22.elem
  rw [← CFSG.KD.LQT.Fi22.LA_eq, ← CFSG.KD.LQT.Fi22.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
