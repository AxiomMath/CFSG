module

public import Certificates.Kernel.LocalComp.HeGlueCheckA
public import Certificates.Kernel.LocalComp.HeGlueCheckB
public import Certificates.Kernel.LocalComp.HeGlueCheckC
public import Certificates.Kernel.LocalComp.HeGlueCheckX
public import Certificates.Kernel.LocalComp.HeGlueCheckY
public import CFSG.Certificates.Kernel.HeGlueKSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeGlue

open CFSG.KC.HeGlueK CFSG.KC.HeModelK CFSG.KC.HeAutK CFSG.KC.HexaK CFSG.KC.Enum CFSG.KS
open CFSG.KC.BfsPin CFSG.KS.Raw CFSG.ComponentClassification.AS81.HeTri
open CFSG.ComponentClassification.AS81.Hexa CertificateChecks.KernelLC.HeModel

theorem heGlueCheck_true : heGlueCheck = true := by
  have kp := kPins
  simp only [Bool.and_eq_true] at kp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, q1⟩, q2⟩, q3⟩, q4⟩, q5⟩, q6⟩, k1⟩, k2⟩, k3⟩,
    k4⟩, k5⟩, k6⟩ := kp
  have kb := kBind
  simp only [Bool.and_eq_true] at kb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩ := kb
  rw [heGlueCheck_eq]
  refine heGlueK_sound (h := heG) (d := hd) (WB := HeGlueD.WB) (WR := HeGlueD.WR)
    (WC := HeGlueD.WC) (WF := HeGlueD.WF) (WM := HeGlueD.WM) (WX := wX) (KY := HeGlueD.KY)
    (FX := fun j => Nat.land (HeGlueD.KX j) 7)
    (FX1 := fun j => Nat.land (Nat.shiftRight (HeGlueD.KX j) 3) 7)
    (FX2 := fun j => Nat.shiftRight (HeGlueD.KX j) 6)
    (pinB_of b1 q1 HeMP12.ok k1) (pinB_of b2 q2 HeMB0.ok k2) (pinB_of b3 q3 HeMP23.ok k3)
    (pinB_of b4 q4 HeMP0.ok k4) (pinB_of b5 q5 HeMP1.ok k5) (pinB_of b6 q6 HeMBC.ok k6)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩
    kInv kPerm kSrc ?_ ?_ kRepF kNorm kWB
    (fun k hk => allN_spec kFus k hk) kPi kKerE ?_ ?_ kMem kGen kId rfl kRange
  · refine allR_chunks (K := 4) (L := 768) fun s hs => ?_
    interval_cases s
    exacts [kB0, kB1, kB2, kB3]
  · intro i hi
    refine allR_chunks (K := 4) (L := 768) fun s hs => ?_
    interval_cases i <;> interval_cases s
    exacts [kC0_0, kC0_1, kC0_2, kC0_3, kC1_0, kC1_1, kC1_2, kC1_3, kC2_0, kC2_1, kC2_2, kC2_3,
      kC3_0, kC3_1, kC3_2, kC3_3]
  · refine allR_chunks (K := 12) (L := 768) fun s hs => ?_
    interval_cases s
    exacts [kY0, kY1, kY2, kY3, kY4, kY5, kY6, kY7, kY8, kY9, kY10, kY11]
  · refine allR_chunks (K := 12) (L := 768) fun s hs => ?_
    interval_cases s
    exacts [kX0, kX1, kX2, kX3, kX4, kX5, kX6, kX7, kX8, kX9, kX10, kX11]

end CertificateChecks.KernelLC.HeGlue

end
