module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSp4Inputs
public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Data.Kernel.Spor.Prim
public meta import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSp4Inputs
public meta import Certificates.Data.CFSGNative.KGroups.Enum
public meta import Certificates.Data.CFSGNative.KGroups.Perm
public import Certificates.Kernel.SporSch.Th.GenV4
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import Init.Data.Array.Basic
import Init.Data.List.Basic

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Twin77001

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups.NativeChecks
  CFSG.CGT.PushingUpLit.SolKNA.PSp4Twin

meta def lvM : Array (Array Nat) := (levelsA QP45).flatten.toArray

meta def twM : Array (Array Nat) := #[toA tw1, toA tw2]

meta def wcM : List Nat := Id.run do
  let E := (CFSG.KGroups.Native.productsA 45 (levelsA QP45)).toArray
  let ts := #[toA tw2, toA tw1]
  let mut out : Array Nat := #[]
  for u in E do
    if CFSG.KGroups.Native.isInvolA 45 u then
      let mut code := 0
      let mut found := false
      for r in [0:2] do
        if !found then
          for j in [0:E.size] do
            if !found && CFSG.Monster.B.Co2.Native.eqA 45 (CFSG.Monster.B.Co2.Native.compA 45 E[j]! ts[r]!)
                (CFSG.Monster.B.Co2.Native.compA 45 u E[j]!) then
              code := 2 * j + r
              found := true
      out := out.push code
    else
      out := out.push 0
  return out.toList

end CertificateChecks.KernelMisc.Twin77001

#kss_perms CertificateChecks.KernelMisc.Twin77001.LV 6 CertificateChecks.KernelMisc.Twin77001.lvM
#kss_perms CertificateChecks.KernelMisc.Twin77001.TW 6 CertificateChecks.KernelMisc.Twin77001.twM
#kss_natlist CertificateChecks.KernelMisc.Twin77001.WC CertificateChecks.KernelMisc.Twin77001.wcM

public section

namespace CertificateChecks.KernelMisc.Twin77001

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups.NativeChecks
  CFSG.CGT.PushingUpLit.SolKNA.PSp4Twin

@[expose] noncomputable def lvls : List (List Nat) :=
  [(List.range 45).map fun k => LV k, (List.range 32).map fun k => LV (45 + k),
    (List.range 9).map fun k => LV (77 + k), (List.range 2).map fun k => LV (86 + k)]

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 45 6 (mask 6) p q

@[expose] noncomputable def pe : Nat := pidn 45 6

@[expose] noncomputable def prodsP : List (List Nat) → List Nat
  | [] => [pe]
  | T :: Ts =>
    let P := prodsP Ts
    T.flatMap fun t => P.map (pc t)

@[expose] noncomputable def twinK (L : List Nat) (t : Nat) : Bool :=
  let C := L.filter fun g => Nat.beq (pc g t) (pc t g)
  C.all fun a => !(Nat.beq (pc a a) t) ||
    (C.filter fun b => (Nat.beq (pc (pc a b) (pc a b)) pe && !(Nat.beq (pc a b) pe)) &&
      !(Nat.beq (pc a b) t)).any fun b => C.any fun g => Nat.beq (pc b g) (pc g a)

@[expose] noncomputable def covF (ts L : List Nat) (u : Nat) : Bool :=
  !(Nat.beq (pc u u) pe && !(Nat.beq u pe)) || ts.any fun t => L.any fun g => Nat.beq (pc g t) (pc u g)

@[expose] noncomputable def coverK (L ts : List Nat) : Bool := L.all (covF ts L)

@[expose] noncomputable def el (a b c d : Nat) : Nat :=
  pc (LV a) (pc (LV (45 + b)) (pc (LV (77 + c)) (pc (LV (86 + d)) pe)))

@[expose] noncomputable def elIdx (j : Nat) : Nat := el (j / 576) (j / 18 % 32) (j / 2 % 9) (j % 2)

@[expose] noncomputable def tOf (r : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (TW 0) (TW 1) (Nat.beq r 0)

@[expose] noncomputable def invB (u : Nat) : Bool := Nat.beq (pc u u) pe && !(Nat.beq u pe)

@[expose] noncomputable def witOK (u w : Nat) : Bool :=
  Nat.blt (w / 2) 25920 && Nat.beq (pc (elIdx (w / 2)) (tOf (w % 2))) (pc u (elIdx (w / 2)))

@[expose] noncomputable def cv (a b c d : Nat) : Bool :=
  !(invB (el a b c d)) || witOK (el a b c d) (WC (((a * 32 + b) * 9 + c) * 2 + d))

@[expose] noncomputable def coverA (a : Nat) : Bool :=
  allN 32 (fun b => allN 9 (fun c => allN 2 (fun d => cv a b c d)))

theorem kBind : levelsA QP45 = lvls.map (List.map (unpack 45 6)) := by decide +kernel

theorem kTw : toA tw1 = unpack 45 6 (TW 0) ∧ toA tw2 = unpack 45 6 (TW 1) := by decide +kernel

theorem kPerm : allN 88 (fun k => permOK 45 6 (mask 6) (45 * 6) (LV k) (pinvS 45 6 (mask 6) (LV k))) =
    true := by
  quickRfl

theorem kPermT : allN 2 (fun k => permOK 45 6 (mask 6) (45 * 6) (TW k) (pinvS 45 6 (mask 6) (TW k))) =
    true := by
  quickRfl

theorem kSz : szOK 45 6 = true := by quickRfl

theorem kT1 : twinK (prodsP lvls) (TW 0) = true := by quickRfl

theorem kT2 : twinK (prodsP lvls) (TW 1) = true := by quickRfl

#kc_each CertificateChecks.KernelMisc.Twin77001.coverA 0 45

theorem neg : bAnd(bIf(coverK (prodsP lvls) [], false, true), bAnd(bIf(Nat.beq (TW 0) (TW 1), false,
    true), Nat.beq (prodsP lvls).length 25920)) = true := by
  quickRfl

end CertificateChecks.KernelMisc.Twin77001

end
