module

public import Certificates.Data.Kernel.TabMatGrp
public import Certificates.Kernel.LocalComp.J3Seeds
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.ModelData
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.W4Presentation
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTablePresented
public import Mathlib

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelW4Model

open CFSG.KC.TabMatGrp CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
  CertificateChecks.KernelLC.J3Ops

@[expose] def segs : List (List (Fin 2 × Bool)) :=
  (List.range 7).map fun k => (uWord k).map pairLetter

theorem chk : grpK 80 SA.M SB.M 2 3 (segs.map natW) [(natW (wRel 4 1), [])] = true := by
  quickRfl

theorem neg : (!grpK 80 SA.M SB.M 2 3 (segs.map natW) [(natW (wRel 4 0), [])]) = true := by
  quickRfl

end CertificateChecks.KernelW4Model

end
