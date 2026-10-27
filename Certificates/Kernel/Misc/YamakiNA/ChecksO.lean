module

public import Certificates.Data.Kernel.Misc.YamakiNO
public import Certificates.Kernel.Misc.YamakiA0.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.YamakiNA

open CFSG.ClassicalInvolution.Sp62Rec

theorem na550822or : orbK CFSG.KD.YamakiA0.REC CFSG.KD.YamakiA0.REC = true := by quickRfl

theorem na550822e8 : e8K CFSG.KD.YamakiA0.REC = true := by quickRfl

theorem na550822rm : rhoMatCheck () = true := by decide +kernel

end CFSG.KD.YamakiNA

end
