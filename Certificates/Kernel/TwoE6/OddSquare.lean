module

public import CFSG.Certificates.Kernel.CTIBqSound
public import Certificates.Kernel.TwoE6.CTIBqChecks

public section

namespace CertificateChecks.KernelTwoE6

open CFSG.KC.CTIBq CFSG.EvenSmallLie.TwoE6

theorem words_eq : wordY2a = y2aK.map decL ∧ wordY2b = y2bK.map decL ∧ wordCY2a = cy2aK.map decL ∧
    wordCY2b = cy2bK.map decL ∧ wordY3a = y3aK.map decL ∧ wordY3b = y3bK.map decL :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

open CFSG.EvenSmallLie.TwoE6 in
theorem cert3129 : (frameCodesOK = true)
    ∧ (oddWitOK 1 6 wordY2a 8 3 wordY2b 4 3 37440 4112 = true)
    ∧ (oddWitOK 1 7 wordCY2a 4 3 wordCY2b 4 3 2096 4112 = true)
    ∧ (oddWitOK 32 7 wordY3a 1 3 wordY3b 2 3 102610 16 = true) := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := words_eq
  refine ⟨soundFrame CFSG.Monster.B.Bin.gramRows CFSG.Monster.B.CTIB.Native.liftImgs6
    CFSG.Monster.B.CTIB.Native.liftImgs8 CFSG.Monster.B.Bin.quotRows1 CFSG.Monster.B.Bin.quotRows2
    GR A6 A8 Q1 Q2 kBinds kFrame, ?_, ?_, ?_⟩
  · rw [w1, w2]
    exact soundOdd CFSG.Monster.B.Bin.gramRows CFSG.Monster.B.CTIB.Native.liftImgs6
      CFSG.Monster.B.CTIB.Native.liftImgs8 CFSG.Monster.B.Bin.quotRows1 CFSG.Monster.B.Bin.quotRows2
      GR A6 A8 Q1 Q2 3711077 3015616 1 6 8 3 4 3 37440 4112 y2aK y2bK kBinds (by decide)
      (by decide) (by decide) kOdd1
  · rw [w3, w4]
    exact soundOdd CFSG.Monster.B.Bin.gramRows CFSG.Monster.B.CTIB.Native.liftImgs6
      CFSG.Monster.B.CTIB.Native.liftImgs8 CFSG.Monster.B.Bin.quotRows1 CFSG.Monster.B.Bin.quotRows2
      GR A6 A8 Q1 Q2 3711077 3015616 1 7 4 3 4 3 2096 4112 cy2aK cy2bK kBinds (by decide)
      (by decide) (by decide) kOdd2
  · rw [w5, w6]
    exact soundOdd CFSG.Monster.B.Bin.gramRows CFSG.Monster.B.CTIB.Native.liftImgs6
      CFSG.Monster.B.CTIB.Native.liftImgs8 CFSG.Monster.B.Bin.quotRows1 CFSG.Monster.B.Bin.quotRows2
      GR A6 A8 Q1 Q2 3711077 3015616 32 7 1 3 2 3 102610 16 y3aK y3bK kBinds (by decide)
      (by decide) (by decide) kOdd3

end CertificateChecks.KernelTwoE6

end
