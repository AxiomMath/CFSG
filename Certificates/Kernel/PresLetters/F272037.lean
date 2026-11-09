module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.W4Presentation
public import Certificates.Kernel.Bounds.Family
public import CFSG.Certificates.CosetTablePresented
public import Mathlib

open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition CFSG.CosetTable

public section

#kb_family "data/F272037.json" 13876 6002490152997556791
  (cr := fun k => j3WordsRest ++ [collapseRels.getD k []]) (ja := j2Words)
  (jb := restrictWords (subsetOf 7 [0, 1, 2, 3, 4, 5]) j2Words) (wa := j3WordsW)
  (wb := restrictWords (subsetOf 7 [0, 1, 2, 3, 5, 6]) j3WordsW)

end
