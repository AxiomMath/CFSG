module

public import Certificates.Kernel.Sp62L.Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62FrameData

public section

namespace CertificateChecks.KernelSp62F

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.Quasithin.G2U CFSG.KGroups.Sp6
  CertificateChecks.KernelSp62L

theorem ch9452tt_a : (gensT.all genB && SD.ET.toArray.size == 81 &&
    allCheck validB SD.ET.toArray) = true := by decide +kernel

theorem ch9452tt_p : (allCheck genB SD.ET.toArray &&
    allCheck (fun c => inZ c || SD.ET.all fun t => !(commB c t) ||
      inTab SD.EB.toArray t) SD.EB.toArray &&
    allCheck (fun x => powC x 9 == oneC) SD.ET.toArray &&
    allCheck (fun x => powC x 3 == oneC ||
      SD.ET.any fun t => !((List.range 9).any fun k => conjC t x == powC x k))
      SD.ET.toArray &&
    !(inTab SD.EB.toArray cSg) && gensT.all (commB cZ) &&
    allCheck (fun x => !(gensB.all (commB x)) || inTab SD.EB.toArray x) SD.ET.toArray) = true := by
  decide +kernel

theorem ch9452n2_ : (allCheck genB SD.EB.toArray &&
    allCheck (fun w => w == oneC || irrOK w) SD.EB.toArray &&
    conjC cSg cW0 == cW1 && conjC cSg cW1 == cW2 && conjC cSg cW2 == cW0) = true := by
  decide +kernel

theorem ch9452wx_ : (gensX.all genB && [cIo1, cTau12].all (commB cW0) &&
    evalWordC gensX wordTau == cTau && evalWordC gensX wordIo == cIo &&
    evalWordC gensX wordGD == cGD &&
    dcPairs.all fun p => genB p.1 && !(gensB.all fun g => inTab SD.EB.toArray (conjC p.1 g))) =
      true := by
  decide +kernel

theorem ch9452dw_ : chkDCWords () = true := by decide +kernel

end CertificateChecks.KernelSp62F

end
