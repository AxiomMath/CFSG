module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3DataCo1
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3DataCo2
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3DataCo3

public section

namespace CertificateChecks.KernelLocal3

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

@[expose] def co1Masks : String := co1Local3.masks

@[expose] def co2Masks : String := co2Local3.masks

@[expose] def co3Masks : String := co3Local3.masks

end CertificateChecks.KernelLocal3

end
