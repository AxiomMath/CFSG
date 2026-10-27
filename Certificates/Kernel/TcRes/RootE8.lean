module

public import Certificates.Kernel.TcRes.Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

#kc_each CFSG.KD.TcRes.ch715750e8 root CFSG.KD.TcRes.E8.root 0 240
#kc_each CFSG.KD.TcRes.ch715750e8 row CFSG.KD.TcRes.E8.row 0 240

theorem CFSG.KD.TcRes.ch715750e8.srt : CFSG.KD.TcRes.E8.srt = true := by quickRfl

end
