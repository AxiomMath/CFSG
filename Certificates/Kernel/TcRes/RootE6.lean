module

public import Certificates.Kernel.TcRes.Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

#kc_each CFSG.KD.TcRes.ch715750e6 root CFSG.KD.TcRes.E6.root 0 72
#kc_each CFSG.KD.TcRes.ch715750e6 row CFSG.KD.TcRes.E6.row 0 72

theorem CFSG.KD.TcRes.ch715750e6.srt : CFSG.KD.TcRes.E6.srt = true := by quickRfl

end
