module

public import Certificates.Data.G23RecogWordsInputs
public import CFSG.Certificates.CosetTablePresented
public import Certificates.Kernel.Bounds.Family

open CFSG.CosetTable CFSG.GH74.QTGen4.Recog.G23

public section

#kb_family "data/F320004.json.gz" 3156 12979235006924717526 (r0 := g23Words)
  (r1 := restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) g23Words) (r2 := g23PD) (r3 := g23PM)

end
