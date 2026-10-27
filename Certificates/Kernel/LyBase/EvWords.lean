module

public import Certificates.Kernel.LyTr.Defs
public import Certificates.Kernel.LyBase.Data

public section

namespace CertificateChecks.KernelLyBase

open CFSG.KC CFSG.KC.Loop CFSG.KC.LyBase CFSG.KC.LyGlue CFSG.KC.LyBenes
  CertificateChecks.KernelLy CertificateChecks.KernelLyTr CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.Sporadic.Recognition.McLMultiplier

@[expose] noncomputable def fixC (cs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => andB (Nat.beq (cdPtC cL dL cs b) b) ih) base

@[expose] noncomputable def bCodes (r : List (Fin 6 × Bool)) : List Nat := (r.map letIdx).flatMap jC

@[expose] def uExp (Ut : List ℤ) : List ℤ :=
  Ut.flatMap fun l =>
    if 0 < l then Ly0.uWords.getD (l.toNat - 1) [] else invW (Ly0.uWords.getD ((-l).toNat - 1) [])

@[expose] def txExp (t : List (Fin 5 × Bool)) : List ℤ :=
  t.flatMap fun l =>
    if l.2 then Glue.txWords.getD l.1.val [] else invW (Glue.txWords.getD l.1.val [])

@[expose] noncomputable def eFix (ev : EEv) : Bool :=
  andB (isUWord ev.1) (andB (isUWord (substW ev.1)) (andB (isBWord ev.2.1) (andB (isBWord ev.2.2)
    (andB (fixC (bCodes ev.2.1 ++ (invW (uExp ev.1)).map lcode))
      (fixC ((uExp (substW ev.1)).map lcode ++ bCodes ev.2.2))))))

@[expose] noncomputable def segFix (sg : TrSeg) : Bool :=
  andB (isBWord sg.1) (andB (isTxWord sg.2) (fixC (bCodes sg.1 ++ (invW (txExp sg.2)).map lcode)))

@[expose] noncomputable def trFix (ev : TrEv) : Bool :=
  andB (segFix ev.1) (andB (ev.2.all segFix) (Nat.beq (wK 243 8 LG ((trWord ev).map zOf)) id8))

end CertificateChecks.KernelLyBase

end
