
module

public import Certificates.Kernel.SporSch.Ru.RFacts
public import Certificates.Kernel.SporSch.Ru.F1920
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Kernel.SporSch.GenPerms
public import CFSG.Sporadic.Schreier.RuCheckProfileInputs
meta import CFSG.Sporadic.Schreier.RuCheckProfileInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuP

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

meta def tvM : Array (Array Nat) := (Array.range 8).map ruTv

meta def badM : Array (Array Nat) := (Array.range 8).map fun v =>
  let L := rawLevels 1920 (ruField1920 4) (ruBaseArr 1920 ruRBase)
  let rows := (List.range L[0]!.pts.size).filter fun a =>
    !((List.range L[1]!.pts.size).all fun b => ruOrd8F (compA 1920 (ruTv v) (prod2A 1920 L a b)))
  #[rows.headD 0]

end CertificateChecks.KernelSporSch.RuP

#kss_perms CertificateChecks.KernelSporSch.RuP.TV 11 CertificateChecks.KernelSporSch.RuP.tvM
#kss_perms CertificateChecks.KernelSporSch.RuP.BAD 12 CertificateChecks.KernelSporSch.RuP.badM

namespace CertificateChecks.KernelSporSch.RuP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelSporSch

@[expose] noncomputable def zfK (Y : Nat) : Bool :=
  bIf(Nat.beq Y (pidn 1920 11), true, Nat.beq Y RuF.ZF)

@[expose] noncomputable def ord8K (v G : Nat) : Bool :=
  strictB (pcomp 1920 11 (mask 11) (TV v) G) (fun X =>
  strictB (pcomp 1920 11 (mask 11) X X) (fun X2 =>
  strictB (pcomp 1920 11 (mask 11) X2 X2) (fun X4 =>
  strictB (pcomp 1920 11 (mask 11) X4 X4) (fun X8 => bAnd(zfK X8, Bool.not (zfK X4))))))

@[expose] noncomputable def row4 (a : Nat) : Bool :=
  row2K 1920 11 (mask 11) (1920 * 11) RuRS.LR RuRS.TR (ord8K 4) a

@[expose] noncomputable def bad (v : Nat) : Bool :=
  bIf(Nat.beq v 4, true, strictB (BAD v) (fun a => bAnd(Nat.blt a (rcnt (RuRS.LR 0)),
    Bool.not (row2K 1920 11 (mask 11) (1920 * 11) RuRS.LR RuRS.TR (ord8K v) a))))

@[expose] noncomputable def tvok (v : Nat) : Bool :=
  strictB (ppow 1920 11 (mask 11) (pidn 1920 11) (RuT1920.L 7) (v % 2)) (fun A =>
  strictB (ppow 1920 11 (mask 11) (pidn 1920 11) (RuT1920.L 9) (v / 2 % 2)) (fun B =>
  strictB (ppow 1920 11 (mask 11) (pidn 1920 11) (RuT1920.L 10) (v / 4 % 2)) (fun C =>
    bAnd(canonK 1920 11 (mask 11) (1920 * 11) A, bAnd(canonK 1920 11 (mask 11) (1920 * 11) B,
    bAnd(canonK 1920 11 (mask 11) (1920 * 11) C,
    bAnd(canonK 1920 11 (mask 11) (1920 * 11) (pcomp 1920 11 (mask 11) A B),
      Nat.beq (pcomp 1920 11 (mask 11) (pcomp 1920 11 (mask 11) A B) C) (TV v))))))))

end CertificateChecks.KernelSporSch.RuP

#kss_each CertificateChecks.KernelSporSch.RuP.R4 CertificateChecks.KernelSporSch.RuP.row4 256
#kss_each CertificateChecks.KernelSporSch.RuP.BC CertificateChecks.KernelSporSch.RuP.bad 8
#kss_each CertificateChecks.KernelSporSch.RuP.TC CertificateChecks.KernelSporSch.RuP.tvok 8

namespace CertificateChecks.KernelSporSch.RuP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelSporSch

theorem canons : bAnd(canonK 1920 11 (mask 11) (1920 * 11) (pidn 1920 11),
    bAnd(canonK 1920 11 (mask 11) (1920 * 11) RuF.ZF,
    bAnd(canonK 1920 11 (mask 11) (1920 * 11) (RuT1920.L 7),
    bAnd(canonK 1920 11 (mask 11) (1920 * 11) (RuT1920.L 9),
      canonK 1920 11 (mask 11) (1920 * 11) (RuT1920.L 10))))) = true := by quickRfl

theorem idOK1920 : idK 1920 11 (mask 11) = true := by quickRfl

theorem cnt0 : Nat.beq (rcnt (RuRS.LR 0)) 256 = true := by quickRfl

end CertificateChecks.KernelSporSch.RuP

end
