module

public import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.MulH
public import Certificates.Data.Kernel.PkPow
public import Certificates.Data.Kernel.Spor.MulHQI
public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KD.TwoHS.FC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KS.PEnum

theorem pg_rdC (w p i : Nat) : pg w (mask w) p i = rdC w (mask w) p i :=
  (CFSG.KS.PK.rdC_eq w p i).symm

@[expose] noncomputable def canonKC (n w m nw p : Nat) : Bool :=
  bAnd(szOK n w, bAnd(Nat.beq (Nat.shiftRight p nw) (nat_lit 0),
    allN n (fun i => Nat.blt (rdC w m p i) n)))

theorem canonK_C (n w nw p : Nat) : canonK n w (mask w) nw p = canonKC n w (mask w) nw p := by
  unfold canonK canonKC
  simp only [pg_rdC]

@[expose] noncomputable def permOKC (n w m nw p q : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight p nw) (nat_lit 0), bAnd(Nat.beq (Nat.shiftRight q nw) (nat_lit 0),
    allN n (fun i => strictB (rdC w m p i) (fun v => bAnd(Nat.blt v n, Nat.beq (rdC w m q v) i)))))

theorem permOK_C (n w nw p q : Nat) :
    permOK n w (mask w) nw p q = permOKC n w (mask w) nw p q := by
  unfold permOK permOKC
  simp only [pg_rdC]

theorem invEqK_C (n w nw p q : Nat) :
    invEqK n w (mask w) nw p q = permOKC n w (mask w) nw p q :=
  permOK_C n w nw p q

@[expose] noncomputable def wfoldKC (n w m : Nat) (S : Nat → Nat) (wd : List Nat) (acc : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (pcompC n w m acc (S l)) ih) wd acc

theorem wfoldK_C (n w : Nat) (S : Nat → Nat) (wd : List Nat) (acc : Nat) :
    wfoldK n w (mask w) S wd acc = wfoldKC n w (mask w) S wd acc := by
  unfold wfoldK wfoldKC
  simp only [CFSG.KS.PK.pcompC_eq]

theorem wfoldK_fun_C (n w : Nat) : wfoldK n w (mask w) = wfoldKC n w (mask w) := by
  funext S wd acc
  exact wfoldK_C n w S wd acc

theorem pcomp_fun_C (n w : Nat) : pcomp n w (mask w) = pcompC n w (mask w) := by
  funext p q
  exact (CFSG.KS.PK.pcompC_eq n w p q).symm

theorem canonK_fun_C (n w nw : Nat) : canonK n w (mask w) nw = canonKC n w (mask w) nw := by
  funext p
  exact canonK_C n w nw p

theorem invEqK_fun_C (n w nw : Nat) : invEqK n w (mask w) nw = permOKC n w (mask w) nw := by
  funext p q
  exact invEqK_C n w nw p q

@[expose] noncomputable def ppwC (n w p e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn n w)
    (fun _ ih => strictN ih (fun q => pcompC n w (mask w) p q)) e

theorem ppw_fun_C (n w : Nat) : CFSG.KC.PkPow.ppw n w = ppwC n w := by
  funext p e
  unfold CFSG.KC.PkPow.ppw ppwC
  simp only [CFSG.KS.PK.pcompC_eq]

@[expose] noncomputable def nfixC (n w p : Nat) : Nat :=
  foldN n (fun x c => nIf(Nat.beq (rdC w (mask w) p x) x, Nat.succ c, c)) (nat_lit 0)

theorem nfix_fun_C (n w : Nat) : CFSG.KC.PkPow.nfix n w = nfixC n w := by
  funext p
  unfold CFSG.KC.PkPow.nfix nfixC
  simp only [pg_rdC]

@[expose] noncomputable def nqGKC (n w m k nc cnt : Nat) (T S C CI CL NP : Nat → Nat) : Bool :=
  allN k (fun l => allN nc (fun j => strictB (r32 NP (Nat.add (Nat.mul (r32 CL l) nc) j)) (fun b =>
    bAnd(Nat.blt b cnt, Nat.beq (T b) (pcompC n w m (pcompC n w m (C j) (S l)) (CI j))))))

theorem nqGK_C (n w : Nat) : nqGK n w (mask w) = nqGKC n w (mask w) := by
  funext k nc cnt T S C CI CL NP
  unfold nqGK nqGKC
  rw [pcomp_fun_C]

end CFSG.KD.TwoHS.FC

end
