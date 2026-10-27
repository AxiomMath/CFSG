module

public import Certificates.Kernel.OmegaEight.E4O8NbrK
public import Certificates.Kernel.OmegaEight.E4O8MembersData
public import Certificates.Data.E4SplitO8
public import Certificates.Data.Kernel.EvenSporSuz.Defs
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight

@[expose] noncomputable def e4Comm (i j b : Nat) : Bool :=
  bAnd(Nat.beq (pc b i) (pc i b), Nat.beq (pc b j) (pc j b))

@[expose] noncomputable def e4GoodK (u v rt x xt : Nat) : Bool :=
  bAnd(e4Pm x, bAnd(e4Pm xt, bAnd(e4Comm u v (pc (pc (pinv x) rt) x),
    e4Comm u v (pc (pc (pinv xt) rt) xt))))

@[expose] noncomputable def e4Good (r u v t x : Nat) : Bool :=
  bAnd(cn x, strictB (pc r t) fun rt => strictB (pc x t) fun xt => e4GoodK u v rt x xt)

@[expose] noncomputable def e4WW (l : Nat) : List Int :=
  CFSG.ClassicalInvolution.Q3.TL4.E4O8.toWord (e4MR.getD l ([], (0, 0))).1

@[expose] noncomputable def e4TRel (r u v : Nat) (L : List Nat) (t : Nat) : Bool :=
  bAnd(Nat.beq (pc t r) (pc r t), bIf(e4Norms L u v t, false, true))

@[expose] noncomputable def e4TAt (r u v : Nat) (L : List Nat) (t l : Nat) : Bool :=
  bIf(e4TRel r u v L t, bAnd(Nat.blt l 6300, bAnd(lettersK 17 (e4WW l),
    strictB (wO (e4WW l)) fun x => e4Good r u v t x)), true)

@[expose] noncomputable def e4Cand (j : Nat) : Nat :=
  wO ((CFSG.ClassicalInvolution.Q3.TL4.E4O8.splitW ()).getD j [])

@[expose] noncomputable def e4SRel (r u v : Nat) (L : List Nat) (w t : Nat) : Bool :=
  bAnd(Nat.beq t r, bIf(e4Norms L u v w, false, true))

@[expose] noncomputable def e4SAt (r u v : Nat) (L : List Nat) (w t j : Nat) : Bool :=
  bIf(e4SRel r u v L w t, bAnd(Nat.blt j 2, e4Comm (cj w u) (cj w v) (e4Cand j)), true)

@[expose] noncomputable def e4RowK (r u v : Nat) (L : List Nat) (wd : List Int) (l j : Nat) :
    Bool :=
  bAnd(lettersK 17 wd, strictB (wO wd) fun w => bAnd(cn w, bAnd(e4Pm w,
    strictB (cj w r) fun t => bAnd(e4Pm t, bAnd(e4TAt r u v L t l, e4SAt r u v L w t j)))))

@[expose] noncomputable def e4Row (r u v : Nat) (L : List Nat) (R : List Nat × (Nat × Nat)) :
    Bool :=
  e4RowK r u v L (CFSG.ClassicalInvolution.Q3.TL4.E4O8.toWord R.1) R.2.1 R.2.2

@[expose] noncomputable def e4RowsAt (r u v : Nat) (L : List Nat) (s : Nat) : Bool :=
  ((e4MR.drop (Nat.mul 16 s)).take 16).all (e4Row r u v L)

@[expose] noncomputable def e4Chunk (s : Nat) : Bool :=
  strictB (mainK 0) fun r => strictB e4U fun u => strictB om0V fun v => strictB pid fun p =>
    strictB (pc u r) fun ur => strictB (pc v r) fun vr => strictB (pc u v) fun uv =>
      strictB (pc uv r) fun uvr => e4RowsAt r u v [p, r, u, ur, v, vr, uv, uvr] s

@[expose] def e4Piece (p : List Char) : Bool :=
  p.isEmpty || (p.splitOn ' ').all CFSG.KC.EvenSporSuz.digitsK

@[expose] def e4Nats (p : List Char) : List Nat :=
  bif p.isEmpty then [] else CFSG.KC.EvenSporSuz.natsK p

theorem kE4Parse : bAnd((e4MS.chars.splitOn ';').all e4Piece,
    decide ((e4MS.chars.splitOn ';').map e4Nats = e4MR.map Prod.fst)) = true := by
  quickRfl

theorem kE4Len : Nat.beq e4MR.length 6300 = true := by quickRfl

@[expose] noncomputable def e4CandK (u v : Nat) (L : List Nat) (c : Nat) : Bool :=
  bAnd(cn c, bAnd(e4Pm c, bAnd(Nat.beq (pc c c) (pinv c),
    bAnd(e4Norms L u v c, bIf(e4Comm u v c, false, true)))))

theorem kE4Cand : allN 2 (fun c =>
    bAnd(lettersK 17 ((CFSG.ClassicalInvolution.Q3.TL4.E4O8.splitW ()).getD c []),
      strictB e4U fun u => strictB om0V fun v => strictB (mainK 0) fun r =>
        strictB (pc u r) fun ur => strictB (pc v r) fun vr => strictB (pc u v) fun uv =>
          strictB (e4Cand c) fun x =>
            e4CandK u v [pid, r, u, ur, v, vr, uv, pc uv r] x)) = true := by
  quickRfl

end CertificateChecks.KernelO8

end
