module

public import Certificates.Kernel.Sporadic.Fi22.HypCB
public meta import Certificates.Kernel.Sporadic.Fi22.HypCB
public import Certificates.Data.Kernel.Spor.CommBaseF
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22P0

open CFSG.EvenSporadicStandard.HypOne.Fi22

meta def gensM : Array (Array Nat) :=
  let g1 := (hypTbl 4).map (·.toNat)
  let g2 := (hypTbl 5).map (·.toNat)
  #[g1, g2, Fi22CB.invA g1, Fi22CB.invA g2]

meta def lettersOf (S : List (List Int × Nat)) : Array (Array Nat) :=
  let G := #[(hypTbl 4).map (·.toNat), (hypTbl 5).map (·.toNat)]
  let H := (S.map fun s => Fi22CB.powA (Fi22CB.wordA G s.1) s.2).toArray
  H ++ #[CFSG.Sporadic.FischerOddCore.fi22ExtArr 21] ++ H.map Fi22CB.invA

meta def lettersAM : Array (Array Nat) := lettersOf
  [([-2, -2, -2, 2, 1, -2, 1, -2], 4), ([2, -1, 2, -2, -2, -1, -1, -1], 4),
   ([-1, -1, -2, 1, -2, 1, -2], 4), ([-1, 2, -1, 1, -1], 12), ([-1, 1, -1, 1, -2, 1], 12),
   ([-1, 1, 2, -1, -1, 2, 2, 2], 12), ([-2, -1], 12), ([-2, -1, 1, 1, 2], 12),
   ([-2, 1, 2, -1, -1], 12)]

meta def lettersBM : Array (Array Nat) := lettersOf
  [([1, -1, 1], 1), ([-1], 1), ([1, 2, 2, 2, 1, -1, 1, 1], 6), ([1, -2], 6), ([-1], 6),
   ([-1, 1, 2, -1], 6), ([-1, -2, -1, -2, -2], 6), ([-1, -2, 2, -1, 1, -1, 2], 6)]

end CertificateChecks.KernelSpor.Fi22P0

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22P0G CertificateChecks.KernelSpor.Fi22P0.gensM 12

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22P0aL CertificateChecks.KernelSpor.Fi22P0.lettersAM 12

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22P0bL CertificateChecks.KernelSpor.Fi22P0.lettersBM 12

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22P0aD
  "Certificates/Kernel/Sporadic/Fi22/data/hypp0a.json.gz" 38731 15670637720685634736
  (S : List (List Nat × Nat)) (B : List CFSG.KC.CommBase.BaseRec)
  (B3 : List CFSG.KC.CommBase.Fix3Rec) (PF : Nat) (ZF : Nat) (DF : Nat)

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22P0bD
  "Certificates/Kernel/Sporadic/Fi22/data/hypp0b.json.gz" 38578 17898163965825824733
  (S : List (List Nat × Nat)) (B : List CFSG.KC.CommBase.BaseRec)
  (B3 : List CFSG.KC.CommBase.Fix3Rec) (PF : Nat) (ZF : Nat) (DF : Nat)

namespace CertificateChecks.KernelSpor.Fi22P0

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.CommBase

@[expose] noncomputable def T : Nat := Fi22ExtT.L 21

@[expose] noncomputable def G (j : Nat) : Nat := Fi22P0G j

@[expose] noncomputable def LA (z : Nat) : Nat := Fi22P0aL z

@[expose] noncomputable def LB (z : Nat) : Nat := Fi22P0bL z

@[expose] noncomputable def one : Nat := pidn 3510 12

@[expose] noncomputable def commOK (p q : Nat) : Bool := Nat.beq (Fi22X.c p q) (Fi22X.c q p)

@[expose] noncomputable def wval (g : Nat → Nat) (W : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) one (fun z _ ih => strictN ih (fun v => Fi22X.c (g z) v)) W

@[expose] noncomputable def ppow (p e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) one (fun _ ih => strictN ih (fun v => Fi22X.c p v)) e

@[expose] noncomputable def wpow (g : Nat → Nat) (s : List Nat × Nat) : Nat :=
  strictN (wval g s.1) (fun p => ppow p s.2)

@[expose] noncomputable def gensOK (g : Nat → Nat) (t : Nat) : Bool :=
  bAnd(allN 4 (fun j => Fi22X.cn (g j)), bAnd(Fi22X.cn t,
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) (g 0) (g 2),
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) (g 1) (g 3),
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) t t,
  bAnd(Fi22X.siftP (g 0), bAnd(Fi22X.siftP (g 1),
  bAnd(commOK (g 0) t, commOK (g 1) t))))))))

@[expose] noncomputable def specsOK (M g : Nat → Nat) (S : List (List Nat × Nat)) (i : Nat) :
    Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun s _ ih i => bAnd(Nat.beq (M i) (wpow g s), ih (Nat.succ i))) S i

@[expose] noncomputable def lettersOK (M g : Nat → Nat) (t nA E : Nat) (S : List (List Nat × Nat)) :
    Bool :=
  strictB S.length (fun m =>
  bAnd(allN (Nat.add (Nat.add m m) 1) (fun z => Fi22X.cn (M z)),
  bAnd(Nat.beq (M m) t,
  bAnd(allN m (fun i => permOK 3510 12 (mask 12) (3510 * 12) (M i) (M (Nat.add (Nat.add m 1) i))),
  bAnd(allL (fun s => Nat.beq s.2 E) (S.drop nA),
  specsOK M g S 0)))))

@[expose] noncomputable def aOK (M : Nat → Nat) : Bool :=
  bAnd(allN 3 (fun i => Nat.beq (ppow (M i) 3) one),
  bAnd(commOK (M 0) (M 1), bAnd(commOK (M 0) (M 2), commOK (M 1) (M 2))))

@[expose] noncomputable def bOK (g : Nat → Nat) (nA : Nat) (S : List (List Nat × Nat)) : Bool :=
  bAnd(Nat.beq (ppow (g 0) 16) one,
  allL (fun s => allL (fun z => bIf(Nat.beq z 0, true, Nat.beq z 2)) s.1) (S.take nA))

@[expose] noncomputable def baseChk (M : Nat → Nat) (nL : Nat) (B : List BaseRec)
    (B3 : List Fix3Rec) (PF ZF DF : Nat) : Bool :=
  commBaseF 3510 12 (mask 12) M nL B B3 PF ZF DF

theorem gensAll : gensOK G T = true := by quickRfl

theorem lettersA : lettersOK LA G T 3 12 Fi22P0aD.S = true := by quickRfl

theorem lettersB : lettersOK LB G T 2 6 Fi22P0bD.S = true := by quickRfl

theorem caseA : aOK LA = true := by quickRfl

theorem caseB : bOK G 2 Fi22P0bD.S = true := by quickRfl

theorem baseA : baseChk LA 19 Fi22P0aD.B Fi22P0aD.B3 Fi22P0aD.PF Fi22P0aD.ZF Fi22P0aD.DF = true := by
  quickRfl

theorem baseB : baseChk LB 17 Fi22P0bD.B Fi22P0bD.B3 Fi22P0bD.PF Fi22P0bD.ZF Fi22P0bD.DF = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22P0

end
