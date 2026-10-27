module

public import Certificates.Data.Kernel.G2Three.Sec1F
public import Certificates.Kernel.G2Three.Sec1T3Data
public import Certificates.Kernel.G2Three.Sec1T3Rec
public import Certificates.Kernel.G2Three.Sec1T5Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1T3

open CFSG.KC.Loop CFSG.KD.G2Three.Sec1

theorem s3m_one : Nat.beq (X3 0) ONEP = true := by quickRfl

theorem s3m_clos0 : closR X3 gS3 RT 0 192 3 = true := by quickRfl
theorem s3m_clos1 : closR X3 gS3 RT 192 192 3 = true := by quickRfl
theorem s3m_clos2 : closR X3 gS3 RT 384 192 3 = true := by quickRfl
theorem s3m_clos3 : closR X3 gS3 RT 576 192 3 = true := by quickRfl

theorem s3m_par : parR RT PA PB 127 2 = true := by quickRfl

theorem s3m_sort : CFSG.KD.G2Three.sortK X3 X3SRT X3SRI 128 2 = true := by quickRfl

end CFSG.KD.G2Three.Sec1T3

end
