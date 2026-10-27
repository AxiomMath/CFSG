module

public import Certificates.Kernel.MonsterExist.WeylE6.Data
public import CFSG.Certificates.Kernel.WeylE6Sound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Rank
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Sylow
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace CertificateChecks.MonsterExist.WeylE6

open CFSG.KC.WeylE6 CFSG.Monster.Existence.StdOdd.P5

set_option Elab.async false

noncomputable abbrev pt : Nat → Bool := wPt WT WP WE 51840

@[expose] noncomputable def cF (k : Nat) : Bool := allR (1080 * k) 1080 pt

#kc_each_unfold cF 0 48 as CertificateChecks.MonsterExist.WeylE6.c

#kc_forall_chunks chunksK (fun k => allR (1080 * k) 1080 pt = true) 48
  CertificateChecks.MonsterExist.WeylE6.c 1

theorem chunks : ∀ k < 48, allR (1080 * k) 1080 pt = true := chunksK

theorem seed : Nat.beq (keyOf (f48 WP 21604)) idKey = true := by quickRfl

theorem tab_ok : TabOK WT := by
  decide +kernel

theorem w_ok : wOK WT WP WE 51840 21604 = true := by
  have hall : allN 51840 pt = true := (allN_iff _ _).2 (all_of_chunks chunks)
  unfold wOK
  rw [hall, seed]
  rfl

end CertificateChecks.MonsterExist.WeylE6

end
