module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.Suz
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LQT.Suz CFSG.SectionRank.Native.suzData 3 64
  CFSG.Blueprint.NativeSporadic.SuzSeed1 CFSG.Blueprint.NativeSporadic.SuzSeed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem suz_elem : ∃ E : Subgroup NativeSporadic.Suz, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have h := elem_sound _ CFSG.KD.LQT.Suz.lay_ok CFSG.KD.LQT.Suz.decA CFSG.KD.LQT.Suz.decB
    CFSG.KD.LQT.Suz.one CFSG.KD.LQT.Suz.steps CFSG.KD.LQT.Suz.elem
  rw [← CFSG.KD.LQT.Suz.LA_eq, ← CFSG.KD.LQT.Suz.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
