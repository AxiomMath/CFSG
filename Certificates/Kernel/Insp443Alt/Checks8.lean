module

public import Certificates.Data.Kernel.Insp443Alt.Invol
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.Certificates.Kernel.Insp443Alt

open CFSG.Certificates.Kernel.PkCV CFSG.SectionRank.QTK.Insp443.Alt CFSG.Quasithin.KGC31

theorem chkI8 : chkI 8 = true := by quickRfl

end CFSG.Certificates.Kernel.Insp443Alt

end
