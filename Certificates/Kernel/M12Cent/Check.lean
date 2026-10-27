module

public import Certificates.Data.Kernel.M12Cent
public import Certificates.Kernel.M12Cent.Data
public import CFSG.RankThree.PartTwo.Toolkit.M12LocalInputs

public section

namespace CertificateChecks.KernelM12Cent

open CFSG.KC.M12Cent

theorem t_eq : D.t = CFSG.RankThree.PartTwo.Toolkit.M12.zT := by decide +kernel

theorem S_eq : D.S = CFSG.RankThree.PartTwo.Toolkit.M12.ET ++ CFSG.RankThree.PartTwo.Toolkit.M12.FT := by
  decide +kernel

theorem cent_ok : centCheck D.t D.S D.W D.C D.R = true := by decide +kernel

theorem cent_neg1 : centCheck D.t D.S D.W.dropLast D.C D.R = false := by decide +kernel

theorem cent_neg2 : centCheck D.t D.S D.W ([2] :: D.C.tail) D.R = false := by decide +kernel

end CertificateChecks.KernelM12Cent

end
