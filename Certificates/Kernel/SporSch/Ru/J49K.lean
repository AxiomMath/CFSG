module

public import Certificates.Kernel.SporSch.Ru.G2Ru7164K
public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.LocalQT.Cmd
public import Certificates.Data.Kernel.SporSch.IntLines
public import CFSG.Sporadic.Schreier.RuJ49Sl2
public meta import CFSG.Sporadic.Schreier.RuJ49Sl2
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#lqt_chars CertificateChecks.KernelSporSch.RuJ49.JW CFSG.Sporadic.RuSchreier.J49.wordsText
#lqt_chars CertificateChecks.KernelSporSch.RuJ49.JR CFSG.Sporadic.RuSchreier.J49.Sl2.rowsText

namespace CertificateChecks.KernelSporSch.RuJ49

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.IntLines
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.G2Ru7164
  CFSG.Sporadic.RuSchreier.J49

meta def tabsM : Array (Array Nat) := CFSG.Sporadic.RuSchreier.J49.tabs ()

end CertificateChecks.KernelSporSch.RuJ49

#kss_perms CertificateChecks.KernelSporSch.RuJ49.W 12 CertificateChecks.KernelSporSch.RuJ49.tabsM

namespace CertificateChecks.KernelSporSch.RuJ49

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.IntLines
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.G2Ru7164
  CFSG.Sporadic.RuSchreier.J49 CFSG.Sporadic.RuSchreier.J49.Sl2

@[expose] noncomputable def wordsK : List (List Int) := ((linesNE JW).map lineInts).map List.reverse

@[expose] noncomputable def rowOf (l : List Int) : Nat × List Int :=
  List.rec (motive := fun _ => Nat × List Int) (0, []) (fun k w _ => (k.toNat, w)) l

@[expose] noncomputable def rowsK : List (Nat × List Int) := (linesNE JR).map fun l => rowOf (lineInts l)

theorem textW : textOK JW = true := by quickRfl

theorem textR : textOK JR = true := by quickRfl

theorem wordsOK : (Nat.beq wordsK.length 19 && wordsK.all (CFSG.Monster.B.Co2.Native.lettersOK 2)) =
    true := by
  quickRfl

@[expose] noncomputable def Gab (j : Nat) : Nat := Bool.rec (motive := fun _ => Nat) A1 A0 (Nat.beq j 0)

@[expose] noncomputable def wordChk (k : Nat) : Bool := Nat.beq (wK Gab (wordsK.getD k [])) (W k)

@[expose] noncomputable def permChk (k : Nat) : Bool :=
  permOK 4060 12 (mask 12) (4060 * 12) (W k) (pinv (W k))

#kc_each wordChk 0 19
#kc_each permChk 0 19

theorem permA : bAnd(permOK 4060 12 (mask 12) (4060 * 12) A0 (pinv A0),
    permOK 4060 12 (mask 12) (4060 * 12) A1 (pinv A1)) = true := by
  quickRfl

@[expose] noncomputable def exK (T : Nat → Nat) (e : Ex) : Nat :=
  Ex.rec (motive := fun _ => Nat) (fun k => Bool.rec (motive := fun _ => Nat) pid (T k) (Nat.blt k 19))
    pid (fun _ _ a b => pc a b) (fun _ n a => powK a n) e

@[expose] noncomputable def atK (T : Nat → Nat) (a : At) : Bool :=
  At.rec (motive := fun _ => Bool)
    (fun a b => Nat.beq (exK T a) (exK T b))
    (fun a b => !Nat.beq (exK T a) (exK T b))
    (fun a cs => cs.any fun c => Nat.beq (exK T a) (exK T c))
    (fun _ _ ih ic => !ih || ic) a

@[expose] noncomputable def atChunk (c : Nat) : Bool :=
  (List.range 40).all fun j => atK W ((atoms ()).getD (40 * c + j) (.eq .one .one))

theorem atomsLen : Nat.beq (atoms ()).length 737 = true := by quickRfl

#kc_each atChunk 0 19

@[expose] noncomputable def G03 (j : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (W 3) (W 0) (Nat.beq j 0)

@[expose] noncomputable def tabKK (k : Nat) : Nat := wK G03 (wordOf rowsK k)

@[expose] noncomputable def keyK (k : Nat) : Bool :=
  Nat.beq (tabKK (keyMul k 533)) (pc (tabKK k) (W 0)) &&
    Nat.beq (tabKK (keyMul k 107)) (pc (tabKK k) (W 3)) && (k == 126 || !Nat.beq (tabKK k) pid)

@[expose] noncomputable def keyChunk (c : Nat) : Bool :=
  (List.range 10).all fun j => keyK ((slKeys ()).getD (10 * c + j) 126)

#kc_each keyChunk 0 12

theorem sl2Pure : ((List.range 625).all (fun k => (wordOf rowsK k).all fun l => l == 1 || l == 2) &&
    (slKeys ()).all (fun k => keyProd (wordOf rowsK k) == k) &&
    wordOf rowsK 126 == [] && wordOf rowsK 533 == [1] && wordOf rowsK 107 == [2] &&
    (slKeys ()).length == 120 &&
    rowsK.all (fun r => r.2.all fun l => l == 1 || l == 2)) = true := by
  quickRfl

theorem neg : (!Nat.beq (W 0) (W 3) && !atK W (.eq (.el 12) .one) &&
    !Nat.beq (pc (W 0) (W 3)) (pc (W 3) (W 0)) &&
    !Nat.beq (tabKK (keyMul 533 107)) (pc (tabKK 533) (W 0))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.RuJ49

end
