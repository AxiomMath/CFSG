module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.Fi23
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LQT.Fi23 CFSG.SectionRank.Native.fi23Data 3 253
  CFSG.Blueprint.NativeSporadic.Fi23Seed1 CFSG.Blueprint.NativeSporadic.Fi23Seed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem fi23_elem : ∃ E : Subgroup NativeSporadic.Fi23, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have h := elem_sound _ CFSG.KD.LQT.Fi23.lay_ok CFSG.KD.LQT.Fi23.decA CFSG.KD.LQT.Fi23.decB
    CFSG.KD.LQT.Fi23.one CFSG.KD.LQT.Fi23.steps CFSG.KD.LQT.Fi23.elem
  rw [← CFSG.KD.LQT.Fi23.LA_eq, ← CFSG.KD.LQT.Fi23.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
