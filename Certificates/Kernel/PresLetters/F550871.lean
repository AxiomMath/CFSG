module

public import Certificates.Data.E64PresRels
public import CFSG.Certificates.CosetTablePresented
public import Certificates.Kernel.Bounds.Family
public import Mathlib

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E64P

set_option maxRecDepth 100000

public section

#kb_family "data/F550871.json.gz" 1654 3241220513028223012 (r0 := e64MemberRels ())
  (r1 := restrictWords (subsetOf 28 [0, 1]) (e64MemberRels ()))

end
