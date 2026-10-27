module

public import Certificates.Data.Kernel.ThDemp.Orb
public import Certificates.Kernel.ThDemp.Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.ThDempO "Certificates/Kernel/ThDemp/data/orb.json.gz" 6338015
  2327803327457774673
  (Ti : List (List Nat)) (words : List (List Nat)) (sb : List Nat)
  (grp : List (List (List (List Nat)))) (ky : List Nat) (par : List Nat) (edges : List Nat)
  (ord : List Nat) (fx5 : List Nat) (x5 : Nat) (x31 : Nat) (yb : Nat) (dm : Nat) (f5 : Nat)
  (v5 : Nat) (qm : Nat) (gs5 : Nat) (gs31 : Nat) (Ga : Nat) (Gb : Nat) (gd0 : Nat) (gd1 : Nat)

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

@[expose] noncomputable def orbData : OrbData where
  Ti := CFSG.KD.ThDempO.Ti
  words := CFSG.KD.ThDempO.words
  sb := CFSG.KD.ThDempO.sb
  grp := CFSG.KD.ThDempO.grp
  ky := CFSG.KD.ThDempO.ky
  par := CFSG.KD.ThDempO.par
  edges := CFSG.KD.ThDempO.edges
  ord := CFSG.KD.ThDempO.ord
  fx5 := CFSG.KD.ThDempO.fx5
  x5 := CFSG.KD.ThDempO.x5
  x31 := CFSG.KD.ThDempO.x31
  yb := CFSG.KD.ThDempO.yb
  dm := CFSG.KD.ThDempO.dm
  f5 := CFSG.KD.ThDempO.f5
  v5 := CFSG.KD.ThDempO.v5
  qm := CFSG.KD.ThDempO.qm
  gs5 := CFSG.KD.ThDempO.gs5
  gs31 := CFSG.KD.ThDempO.gs31
  Ga := CFSG.KD.ThDempO.Ga
  Gb := CFSG.KD.ThDempO.Gb
  gd0 := CFSG.KD.ThDempO.gd0
  gd1 := CFSG.KD.ThDempO.gd1

end CertificateChecks.KernelThDemp

end
