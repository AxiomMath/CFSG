module

public import Certificates.Data.Kernel.ThDemp.Defs
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.ThDemp "Certificates/Kernel/ThDemp/data/demp.json.gz" 4437334
  12767656790841757507
  (c : Nat) (rm : Nat) (tm0 : Nat) (tm1 : Nat) (tm2 : Nat) (tm3 : Nat) (tm4 : Nat) (tm5 : Nat)
  (tm6 : Nat) (tm7 : Nat) (up : Nat) (dg : Nat) (ONE : Nat) (regs : List Nat) (cs1 : List Nat)
  (cs2 : List Nat) (r1 : Nat) (nreg : Nat) (rd : Nat) (pr : Nat) (npr : Nat) (L : Nat)
  (fr : List Nat) (bv : List Nat) (osz : List Nat) (pts : List (List Nat))
  (tr : List (List Nat)) (tree : List (List Nat)) (ord : List (List Nat))
  (res : List (List Nat))

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

@[expose] noncomputable def dempData : DempData where
  c := CFSG.KD.ThDemp.c
  rm := CFSG.KD.ThDemp.rm
  tm0 := CFSG.KD.ThDemp.tm0
  tm1 := CFSG.KD.ThDemp.tm1
  tm2 := CFSG.KD.ThDemp.tm2
  tm3 := CFSG.KD.ThDemp.tm3
  tm4 := CFSG.KD.ThDemp.tm4
  tm5 := CFSG.KD.ThDemp.tm5
  tm6 := CFSG.KD.ThDemp.tm6
  tm7 := CFSG.KD.ThDemp.tm7
  up := CFSG.KD.ThDemp.up
  dg := CFSG.KD.ThDemp.dg
  ONE := CFSG.KD.ThDemp.ONE
  SA := CFSG.KD.ThSeed.SA
  SB := CFSG.KD.ThSeed.SB
  regs := CFSG.KD.ThDemp.regs
  cs1 := CFSG.KD.ThDemp.cs1
  cs2 := CFSG.KD.ThDemp.cs2
  r1 := CFSG.KD.ThDemp.r1
  nreg := CFSG.KD.ThDemp.nreg
  rd := CFSG.KD.ThDemp.rd
  pr := CFSG.KD.ThDemp.pr
  npr := CFSG.KD.ThDemp.npr
  L := CFSG.KD.ThDemp.L
  fr := CFSG.KD.ThDemp.fr
  bv := CFSG.KD.ThDemp.bv
  osz := CFSG.KD.ThDemp.osz
  pts := CFSG.KD.ThDemp.pts
  tr := CFSG.KD.ThDemp.tr
  tree := CFSG.KD.ThDemp.tree
  ord := CFSG.KD.ThDemp.ord
  res := CFSG.KD.ThDemp.res

end CertificateChecks.KernelThDemp

end
