module

public import Certificates.Kernel.Sporadic.OddCore.Suz786001
import all Certificates.Data.GrSLitL34FactsCF23SuzCheck

public section

namespace CertificateChecks.KernelSpor.Suz786001

open CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.GSThmB.CF23L34

theorem fus_eq {k : Nat} (hk : k < 3) :
    hexTable 3 1782 (1782 * k) suzFusText = unpack 1782 11 (Suz786001T.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound Suz786001T.all k hk
  rw [← Suz786001T.eq] at h
  exact h

theorem y1_eq : suzY1Arr = unpack 1782 11 (Suz786001T.F 0) := fus_eq (k := 0) (by decide)

theorem y2_eq : suzY2Arr = unpack 1782 11 (Suz786001T.F 1) := fus_eq (k := 1) (by decide)

theorem m_eq : suzMArr = unpack 1782 11 (Suz786001T.F 2) := fus_eq (k := 2) (by decide)

end CertificateChecks.KernelSpor.Suz786001

end
