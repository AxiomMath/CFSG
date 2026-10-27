
module

public import Certificates.Kernel.Misc.Tits.K0Use7050
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.SporSch.OrbRec
public import CFSG.Quasithin.Recognition.RuRank3E0DataInputs
public import CFSG.Quasithin.Recognition.RuRank3RuAutDataInputs
public meta import CFSG.Quasithin.Recognition.RuRank3E0DataInputs
public meta import CFSG.Quasithin.Recognition.RuRank3RuAutDataInputs
public meta import CFSG.Quasithin.Recognition.RuRank3TitsSylInputs
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Misc.Tits.K0Chain7050

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.TSd CFSG.Quasithin.RuRank3.ruSdText
#kmisc_hexflat CertificateChecks.KernelMisc.TSd CFSG.Quasithin.RuRank3.ruSdText 3 1755 11 2
#ks_chars CertificateChecks.KernelMisc.TBl CFSG.Quasithin.RuRank3.titsK0BlText
#kmisc_hexflat CertificateChecks.KernelMisc.TBl CFSG.Quasithin.RuRank3.titsK0BlText 2 1755 11 1

namespace CertificateChecks.KernelMisc.E7043

meta def labM : Array Nat := CFSG.Quasithin.RuRank3.titsK0Lab

meta def rootsM : Array Nat := (CFSG.Quasithin.RuRank3.orbLabels 1755 CFSG.Quasithin.RuRank3.titsK0Gens).2

meta def mM : Array Nat := #[rootsM.size]

meta def forestM : Array Nat × Array Nat × Array Nat := Id.run do
  let gens := CFSG.Quasithin.RuRank3.titsK0Gens
  let n := 1755
  let mut par : Array Nat := Array.replicate n 0
  let mut kk : Array Nat := Array.replicate n 0
  let mut dep : Array Nat := Array.replicate n 0
  let mut seen : Array Bool := Array.replicate n false
  for r in rootsM do
    seen := seen.set! r true
    let mut queue : Array Nat := #[r]
    let mut head := 0
    for _ in [0:n] do
      if head < queue.size then
        let x := queue[head]!
        head := head + 1
        for k in [0:gens.size] do
          let y := (gens[k]!)[x]!
          if y < n && !seen[y]! then
            seen := seen.set! y true
            par := par.set! y x
            kk := kk.set! y k
            dep := dep.set! y (dep[x]! + 1)
            queue := queue.push y
  return (par, kk, dep)

meta def parM : Array Nat := forestM.1
meta def kM : Array Nat := forestM.2.1
meta def depM : Array Nat := forestM.2.2

meta def tauM : Array Nat := CFSG.Quasithin.RuRank3.titsK0Tau.foldl (· ++ ·) #[]
meta def repsM : Array Nat := CFSG.Quasithin.RuRank3.titsK0BlReps

end CertificateChecks.KernelMisc.E7043

#ks_perm CertificateChecks.KernelMisc.E7043.EL 11 CertificateChecks.KernelMisc.E7043.labM
#ks_perm CertificateChecks.KernelMisc.E7043.ER 11 CertificateChecks.KernelMisc.E7043.rootsM
#ks_perm CertificateChecks.KernelMisc.E7043.EM 11 CertificateChecks.KernelMisc.E7043.mM
#ks_perm CertificateChecks.KernelMisc.E7043.EP 11 CertificateChecks.KernelMisc.E7043.parM
#ks_perm CertificateChecks.KernelMisc.E7043.EK 11 CertificateChecks.KernelMisc.E7043.kM
#ks_perm CertificateChecks.KernelMisc.E7043.ED 11 CertificateChecks.KernelMisc.E7043.depM
#ks_perm CertificateChecks.KernelMisc.E7043.ETau 11 CertificateChecks.KernelMisc.E7043.tauM
#ks_perm CertificateChecks.KernelMisc.E7043.EReps 11 CertificateChecks.KernelMisc.E7043.repsM

public section

namespace CertificateChecks.KernelMisc.E7043

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.OrbLab CertificateChecks.KernelMisc
  CertificateChecks.KernelMisc.Tits7050 CertificateChecks.KernelSpor.Tits2264

@[expose] noncomputable def fl (T x : Nat) : Nat := pg 11 (mask 11) T x

@[expose] noncomputable def gK (k x : Nat) : Nat := fl (TK.F k) x

@[expose] noncomputable def Lf (x : Nat) : Nat := fl EL x
@[expose] noncomputable def Rf (c : Nat) : Nat := fl ER c
@[expose] noncomputable def Pf (x : Nat) : Nat := fl EP x
@[expose] noncomputable def Kf (x : Nat) : Nat := fl EK x
@[expose] noncomputable def Df (x : Nat) : Nat := fl ED x
@[expose] noncomputable def Mv : Nat := fl EM 0

@[expose] noncomputable def Bf (x : Nat) : Nat := fl (TBl.F 0) x

@[expose] noncomputable def Tf (i c : Nat) : Nat := fl ETau (26 * i + c)

@[expose] noncomputable def Rp (c : Nat) : Nat := fl EReps c

@[expose] noncomputable def SA : Nat := TSd.F 0
@[expose] noncomputable def SB : Nat := TSd.F 1

theorem kOrb : orbRecK 1755 Mv 3 gK Lf Rf Pf Kf Df = true := by quickRfl

theorem kRange : allN 3 (fun k => allN 1755 (fun x => Nat.blt (gK k x) 1755)) = true := by quickRfl

@[expose] noncomputable def blkK (i x : Nat) : Bool :=
  !(Nat.beq (Lf x) 1) || (Nat.blt (Bf x) 26 && Nat.beq (Bf (gK i x)) (Tf i (Bf x)))

theorem kBlk : allN 3 (fun i => allN 1755 (blkK i)) = true := by quickRfl

theorem kReps : allN 26 (fun c => Nat.blt (Rp c) 1755 && Nat.beq (Lf (Rp c)) 1 &&
    Nat.beq (Bf (Rp c)) c) = true := by
  quickRfl

theorem kPerm : bAnd(permC SA, permC SB) = true := by quickRfl

@[expose] noncomputable def cj (c t : Nat) : Nat := pc (pc c t) (pinvS 1755 11 (mask 11) c)

@[expose] noncomputable def sk (G : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK0.LR TitsK0.TRI TitsK0.BP 3 0 G

theorem kSift : allN 3 (fun i => bAnd(bAnd(sk (cj SA (TK.F i)), permC (cj SA (TK.F i))),
    bAnd(sk (cj SB (TK.F i)), permC (cj SB (TK.F i))))) = true := by
  quickRfl

theorem kPow : bAnd(Nat.beq (pw SA 8) (pidn 1755 11), bAnd(bIf(Nat.beq (pw SA 4) (pidn 1755 11), false,
    true), bAnd(Nat.beq (pc SB SB) (pidn 1755 11), bAnd(Nat.beq (cj SB SA) (pw SA 3),
    allN 8 (fun i => bIf(Nat.beq SB (pw SA i), false, true)))))) = true := by
  quickRfl

theorem kDA : bAnd(siftD (pc SA (GI 1)), permC (pc SA (GI 1))) = true := by quickRfl

theorem kDB : siftD SB = true := by quickRfl

theorem neg : bAnd(bIf(siftD SA, false, true), bAnd(bIf(Nat.beq (pw SA 2) (pidn 1755 11), false, true),
    bAnd(bIf(allN 1755 (fun x => !(Nat.beq (Lf x) 1) || Nat.beq (Bf (gK 0 x)) (Tf 1 (Bf x))), false,
      true), bIf(Nat.beq (Mv) 0, false, true)))) = true := by
  quickRfl

end CertificateChecks.KernelMisc.E7043

end
