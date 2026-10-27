module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def sort3 (i : Nat) : Bool := sortOk (Nat.add 6144 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.S3 CFSG.KD.HNXK.sort3 2048

end
