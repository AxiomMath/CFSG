module

public import Certificates.Kernel.U43Pk.CovData
public import Certificates.Kernel.Misc.ArgCharsAt
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Data
public import CFSG.Certificates.Kernel.Common.StrSplit
import all Init.Data.List.SplitOn.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Std.Data.HashMap

public section

set_option maxRecDepth 400000

#kc_arg_chars_at CertificateChecks.KernelU43Pk.U43T
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.u43Data 2

namespace CertificateChecks.KernelU43Pk

open CFSG.KD.U43Pk CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check

@[expose] noncomputable def tabPieces : List (List Char) := (U43T.chars.splitOn ' ').filter fun l => !l.isEmpty

theorem o8L : (List.range 1024).filter o8D = (List.range 384).map OI := by decide +kernel

theorem invL : (List.range 1024).filter invD = (List.range 191).map II := by decide +kernel

theorem gpL : ((List.range 384).flatMap fun a =>
    ((List.range 191).filter fun b => Nat.beq (WD a b) 65535).map fun b => (OI a, II b)) =
      (List.range 2304).map fun k => (GI k, GJ k) := by decide +kernel

theorem tabDigits : tabPieces.all (fun l => l.all Char.isDigit) = true := by decide +kernel

theorem tabL : pairUp (tabPieces.map CFSG.KC.Str.decVal) = (List.range 2304).map fun k => (TR k, TS k) := by
  decide +kernel

theorem repsL : u43Data.reps.size = 48 ∧ ∀ r < 48,
    ((u43Data.reps[r]!).x.size = 17 ∧ ∀ j < 17, (u43Data.reps[r]!).x[j]! = dg (RX r) j) ∧
      ((u43Data.reps[r]!).t.size = 17 ∧ ∀ j < 17, (u43Data.reps[r]!).t[j]! = dg (RT r) j) := by
  decide +kernel

end CertificateChecks.KernelU43Pk

end
