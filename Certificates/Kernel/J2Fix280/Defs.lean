module

public import Certificates.Kernel.J2Fix280.Data
public import Certificates.Kernel.J2Fix280.Tree
public import Certificates.Data.Kernel.B3S3K

public section

namespace CertificateChecks.KernelJ2Fix280

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.KC.B3S3K (cm)
open CFSG.RankThree.PartTwo.J2Residue.C280

@[expose] noncomputable def tg (T i : ℕ) : ℕ := pg 9 (mask 9) T i

@[expose] noncomputable def gK (k : ℕ) : ℕ := if k = 0 then AB 0 else AB 1

@[expose] noncomputable def gI (k : ℕ) : ℕ := if k = 0 then AI 0 else AI 1

@[expose] noncomputable def wK (w : List ℕ) : ℕ := w.foldr (fun k acc => cm 315 9 (gK k) acc) (pidn 315 9)

@[expose] noncomputable def cjK (g y : ℕ) : ℕ := cm 315 9 g (cm 315 9 y (pinvS 315 9 (mask 9) g))

@[expose] noncomputable def cjI (g gi y : ℕ) : ℕ := cm 315 9 g (cm 315 9 y gi)

@[expose] noncomputable def sameK (t y : ℕ) : Bool := Nat.beq t y || Nat.beq t (cm 315 9 y y)

@[expose] noncomputable def wcode (w : List ℕ) : ℕ := w.foldr (fun k c => Nat.add (Nat.mul 2 c) k) 1

@[expose] noncomputable def wcT (i : ℕ) : ℕ := pg 40 (mask 40) WC i

@[expose] noncomputable def wcChk (ws : List (List ℕ)) : ℕ → Bool :=
  ws.rec (fun _ => true) fun w _ ih i =>
    Nat.beq (wcode w) (wcT i) && w.all (fun k => Nat.blt k 2) && ih (Nat.succ i)

@[expose] noncomputable def rowT (i : ℕ) : Bool :=
  (Nat.beq i 0 || (Nat.blt (tg PAR i) i && Nat.blt (tg LET i) 2 &&
      Nat.beq (wcT i) (Nat.add (Nat.mul 2 (wcT (tg PAR i))) (tg LET i)) &&
      Nat.beq (YT i) (cjI (gK (tg LET i)) (gI (tg LET i)) (YT (tg PAR i))))) &&
    Nat.blt (tg TA i) 280 && Nat.blt (tg TB i) 280 && Nat.blt (tg TZ i) 280 &&
    sameK (cjI (gK 0) (gI 0) (YT i)) (YT (tg TA i)) &&
    sameK (cjI (gK 1) (gI 1) (YT i)) (YT (tg TB i)) && sameK (cjI Z ZI (YT i)) (YT (tg TZ i))

@[expose] noncomputable def tabK (u : List ℕ) (i : ℕ) : ℕ :=
  u.foldr (fun k j => tg (if k = 0 then TA else TB) j) i

@[expose] noncomputable def uOfK (j : ℕ) : List ℕ := uWords[tg UIDX j]!

@[expose] noncomputable def relK (c : ℕ) : List ℕ :=
  [tg REPS c, tg TZ (tg REPS c), tg TZ (tg TZ (tg REPS c))]

@[expose] noncomputable def relMuK (m : List Bool) (c : ℕ) : List ℕ :=
  relK c ++ if m.getD c false then [0] else []

@[expose] noncomputable def combListK (m : List Bool) (ts : List (ℕ × ℕ)) : List ℕ :=
  ts.flatMap fun t => (relMuK m (tg CLS t.2)).map (tabK (words[t.1]! ++ uOfK t.2))

@[expose] noncomputable def checkBK : Bool :=
  (List.range 3).all (fun c => decide (tg REPS c < 280) && tg TZ (tg TZ (tg TZ (tg REPS c))) == tg REPS c) &&
    (List.range 7).all fun p =>
      (combs[p]!).all (fun t => decide (tg CLS t.2 < 3)) && parityOK (combListK pats[p]! combs[p]!)

@[expose] noncomputable def checkCK : Bool :=
  tg TZ 0 == 0 && words[0]! == [] &&
    (List.range 280).all fun j => j == 0 ||
      (decide (tg CLS j < 3) && tabK (uOfK j) 0 == 0 &&
        permEq ((relK (tg CLS j)).map (tabK (uOfK j))) [j, tg TZ j, tg TZ (tg TZ j)])

end CertificateChecks.KernelJ2Fix280

end
