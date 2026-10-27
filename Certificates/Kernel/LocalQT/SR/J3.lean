module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.J3
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LQT.J3 CFSG.SectionRank.Native.j3Data 2 80
  CFSG.Blueprint.NativeSporadic.J3Seed1 CFSG.Blueprint.NativeSporadic.J3Seed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem j3_elem : ∃ E : Subgroup NativeSporadic.J3, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  have h := elem_sound _ CFSG.KD.LQT.J3.lay_ok CFSG.KD.LQT.J3.decA CFSG.KD.LQT.J3.decB
    CFSG.KD.LQT.J3.one CFSG.KD.LQT.J3.steps CFSG.KD.LQT.J3.elem
  rw [← CFSG.KD.LQT.J3.LA_eq, ← CFSG.KD.LQT.J3.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
