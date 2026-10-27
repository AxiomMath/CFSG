module

public import CFSG.CGT.M24R.R3Inputs
public import Certificates.Kernel.Bounds.Family
public import CFSG.Certificates.CosetTablePresented
public import Mathlib

open CFSG.CGT.M24R CFSG.CGT.M24R.R3

public section

#kb_family "data/F21194.json.gz" 12061 9686228138885590679
  (collRels := fun i : Fin 16 => relsN8 ++ thetaRels8 ++ [collRel i])

end
