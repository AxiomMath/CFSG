module

public import CFSG.Literature.ParrottTitsPresentation
public import Certificates.Kernel.Bounds.Family
public import Mathlib

open CFSG.Literature.ParrottTits CFSG.CosetTable

public section

#kb_family "data/F2004.json.gz" 1690 17452435828992829003 (pa := parrottWords)
  (pb := restrictWords (subsetOf 10 [0, 2, 3, 4, 5, 6, 7, 8, 9]) parrottWords)

end
