module

public import Certificates.Kernel.TcRes.C3Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.TcRes.ch715752

theorem zl : C3.zl = true := by quickRfl

theorem cnt : C3.cnt = true := by quickRfl

theorem cols : C3.cols = true := by quickRfl

theorem bx : C3.bx = true := by quickRfl

theorem sig : C3.sig = true := by quickRfl

theorem cls : C3.cls = true := by quickRfl

theorem lineJ : C3.lineJ = true := by quickRfl

theorem jok : C3.jok = true := by quickRfl

end CFSG.KD.TcRes.ch715752

#kc_each CFSG.KD.TcRes.ch715752 gen CFSG.KD.TcRes.C3.gen 0 3
#kc_each CFSG.KD.TcRes.ch715752 root CFSG.KD.TcRes.C3.root 0 4
#kc_each CFSG.KD.TcRes.ch715752 line CFSG.KD.TcRes.C3.line 0 12
#kc_each CFSG.KD.TcRes.ch715752 leaf CFSG.KD.TcRes.C3.leaf 0 120

end
