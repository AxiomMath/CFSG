
module

public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Kernel.SporSch.Ru.JChain
public import Certificates.Kernel.Misc.Tits.Text
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Quasithin.Recognition.RuRank3RuIsoDataInputs
public import Certificates.Data.Kernel.SporSch.RuK
meta import CFSG.Quasithin.Recognition.RuRank3RuIsoDataInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.Iso7047R CFSG.Quasithin.RuRank3.ruR0Text
#kmisc_hexflat CertificateChecks.KernelSporSch.Iso7047R CFSG.Quasithin.RuRank3.ruR0Text 3 4060 12 4
#ks_chars CertificateChecks.KernelSporSch.Iso7047D CFSG.Quasithin.RuRank3.ruDText
#kmisc_hexflat CertificateChecks.KernelSporSch.Iso7047D CFSG.Quasithin.RuRank3.ruDText 3 1755 12 1
#ks_chars CertificateChecks.KernelSporSch.Iso7047P CFSG.Quasithin.RuRank3.ruTreeParText
#kmisc_hexflat CertificateChecks.KernelSporSch.Iso7047P CFSG.Quasithin.RuRank3.ruTreeParText
  3 4060 12 1
#ks_chars CertificateChecks.KernelSporSch.Iso7047L CFSG.Quasithin.RuRank3.ruTreeLabText
#kmisc_hexflat CertificateChecks.KernelSporSch.Iso7047L CFSG.Quasithin.RuRank3.ruTreeLabText
  1 4060 4 1

namespace CertificateChecks.KernelSporSch.Iso7047

meta def qM : Array Nat := Id.run do
  let d := CFSG.Quasithin.RuRank3.ruDArr
  let mut a : Array Nat := Array.replicate 4060 0
  for j in [0:1755] do
    a := a.set! d[j]! j
  return a

end CertificateChecks.KernelSporSch.Iso7047

#ks_perm CertificateChecks.KernelSporSch.Iso7047.Q 12 CertificateChecks.KernelSporSch.Iso7047.qM

namespace CertificateChecks.KernelSporSch.Iso7047

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def R (i : Nat) : Nat := Iso7047R.F i

@[expose] noncomputable def D : Nat := Iso7047D.F 0

@[expose] noncomputable def Par : Nat := Iso7047P.F 0

@[expose] noncomputable def Lab : Nat := Iso7047L.F 0

@[expose] noncomputable def twK (fuel : Nat) : Nat → List Int :=
  Nat.rec (motive := fun _ => Nat → List Int) (fun _ => [])
    (fun _ ih x => Bool.rec (motive := fun _ => List Int)
      (List.cons (CFSG.Quasithin.RuRank3.ruTreeLetter (pg 4 (mask 4) Lab x)) (ih (pg 12 (mask 12) Par x)))
      [] (Nat.beq x 0)) fuel

@[expose] noncomputable def gK (l : Int) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) A1I A0I (l == -1)) A1
      (l == 2)) A0 (l == 1)

@[expose] noncomputable def ptK (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun l _ ih => pg 12 (mask 12) (gK l) ih) w

theorem kHi : bAnd(Nat.beq (Nat.shiftRight A0I (4060 * 12)) 0,
    bAnd(Nat.beq (Nat.shiftRight A1I (4060 * 12)) 0,
    bAnd(Nat.beq (Nat.shiftRight A0 (4060 * 12)) 0, Nat.beq (Nat.shiftRight A1 (4060 * 12)) 0))) =
    true := by quickRfl

theorem kRange : allN 4060 (fun i => bAnd(Nat.blt (pg 12 (mask 12) A0 i) 4060,
    bAnd(Nat.blt (pg 12 (mask 12) A1 i) 4060, bAnd(Nat.blt (pg 12 (mask 12) A0I i) 4060,
    bAnd(Nat.blt (pg 12 (mask 12) A1I i) 4060, Nat.blt (pg 12 (mask 12) Par i) 4060))))) = true := by
  quickRfl

theorem kPerm : bAnd(permOK 4060 12 (mask 12) (4060 * 12) A0 A0I,
    permOK 4060 12 (mask 12) (4060 * 12) A1 A1I) = true := by quickRfl

theorem kTree : allN 4060 (fun x => bAnd(CFSG.Monster.B.Co2.Native.lettersOK 2 (twK 32 x),
    Nat.beq (ptK (twK 32 x)) x)) = true := by quickRfl

@[expose] noncomputable def rOK (i : Nat) : Bool :=
  bAnd(permOK 4060 12 (mask 12) (4060 * 12) (R i) (pinvS 4060 12 (mask 12) (R i)),
  bAnd(Nat.beq (Nat.shiftRight (R i) (4060 * 12)) 0,
  bAnd(allN 4060 (fun x => Nat.blt (pg 12 (mask 12) (R i) x) 4060),
  bAnd(siftK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) RuJS.LR RuJS.TRI RuJS.BP 4 0 (R i),
  bAnd(Nat.beq (pg 12 (mask 12) (R i) 0) 0,
    allN 1755 (fun j => bAnd(Nat.blt (pg 11 (mask 11) (CertificateChecks.KernelMisc.TitsText.F i) j) 1755,
      Nat.beq (pg 12 (mask 12) (R i) (pg 12 (mask 12) D j))
        (pg 12 (mask 12) D (pg 11 (mask 11) (CertificateChecks.KernelMisc.TitsText.F i) j)))))))))

theorem kR0 : rOK 0 = true := by quickRfl
theorem kR1 : rOK 1 = true := by quickRfl
theorem kR2 : rOK 2 = true := by quickRfl
theorem kR3 : rOK 3 = true := by quickRfl

theorem kD : bAnd(Nat.beq (pg 12 (mask 12) D 0) 1, allN 1755 (fun j =>
    bAnd(Nat.blt (pg 12 (mask 12) D j) 4060, bIf(Nat.beq (pg 12 (mask 12) D j) 0, false, true)))) =
    true := by quickRfl

theorem kDist : allN 1755 (fun j => Nat.beq (pg 12 (mask 12) Q (pg 12 (mask 12) D j)) j) = true := by
  quickRfl

theorem neg : bAnd(bIf(Nat.beq (ptK (twK 32 5)) 6, false, true),
    bAnd(bIf(Nat.beq (R 0) (R 1), false, true),
      bIf(Nat.beq (pg 12 (mask 12) D 0) (pg 12 (mask 12) D 1), false, true))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Iso7047

end
