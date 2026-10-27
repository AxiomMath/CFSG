module

public import Certificates.Data.Kernel.ThCent.Defs
public import Certificates.Kernel.ThCent.Data
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel

public section

namespace CFSG.KD.ThCent.W

open CFSG.KC.Th CFSG.KC.ThCent

theorem w3B : witOK ThS.RBf ThS.c ThS.rm ThS.ONE ThS.Bi ThS.GRf ThS.IRf Z3B hw3B hn3B tw3B tn3B =
    true := by decide +kernel
theorem w3A : witOK ThS.RBf ThS.c ThS.rm ThS.ONE ThS.Bi ThS.GRf ThS.IRf Z3A hw3A hn3A tw3A tn3A =
    true := by decide +kernel
theorem w7A : witOK ThS.RBf ThS.c ThS.rm ThS.ONE ThS.Bi ThS.GRf ThS.IRf Z7 hw7A hn7A tw7A tn7A =
    true := by decide +kernel
theorem w7B : witOK ThS.RBf ThS.c ThS.rm ThS.ONE ThS.Bi ThS.GRf ThS.IRf Z7 hw7B hn7B tw7B tn7B =
    true := by decide +kernel

theorem d3B : codes4 tw3B tn3B = C3B.word := by decide +kernel
theorem d3A : codes4 tw3A tn3A = C3A.word := by decide +kernel
theorem d7A : codes4 tw7A tn7A = C7A.word := by decide +kernel
theorem d7B : codes4 tw7B tn7B = C7B.word := by decide +kernel

end CFSG.KD.ThCent.W

end
