module

public import Certificates.Kernel.SporSch.Tits.T614D
public import Certificates.Kernel.SporSch.Tits.GenAll5

public section

namespace CertificateChecks.KernelSporSch.T614

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsAbel

@[expose] noncomputable def PCJ (t0 t1 t2 t3 t4 : Nat) : Bool :=
  bIf(commPts 1755 11 (mask 11) T614P t0 t1 t2 t3 t4,
    bIf(eqPts 1755 11 (mask 11) (pidn 1755 11) t0 t1 t2 t3 t4, true,
      eqPts 1755 11 (mask 11) TitsZ t0 t1 t2 t3 t4), true)

@[expose] noncomputable def QCJ : Nat → Nat → Nat → Nat → Nat → Nat → Bool := fun _ => PCJ

@[expose] noncomputable def labEq (t0 t1 t2 t3 t4 q : Nat) : Bool :=
  Nat.beq (labT (pg 11 (mask 11) T614PI
    (gpt 11 (mask 11) t0 t1 t2 t3 t4 (pg 11 (mask 11) T614P q)))) (labT q)

@[expose] noncomputable def PSS (t0 t1 t2 t3 t4 : Nat) : Bool :=
  bIf(allN 2 (labEq t0 t1 t2 t3 t4), sfJ (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4), true)

@[expose] noncomputable def QSS : Nat → Nat → Nat → Nat → Nat → Nat → Bool := fun _ => PSS

@[expose] noncomputable def uPt (t0 t1 t2 t3 t4 x : Nat) : Nat :=
  gpt 11 (mask 11) t0 t1 t2 t3 t4 (pg 11 (mask 11) T614G1 x)

@[expose] noncomputable def cmEq (t0 t1 t2 t3 t4 H E : Nat) : Bool :=
  allN 8 (fun x => Nat.beq (uPt t0 t1 t2 t3 t4 (pg 11 (mask 11) H x))
    (pg 11 (mask 11) H (uPt t0 t1 t2 t3 t4 (pg 11 (mask 11) E x))))

@[expose] noncomputable def kTests (U UI : Nat) : Bool :=
  bAnd(permOK 1755 11 (mask 11) (1755 * 11) U UI,
  bAnd(canonK 1755 11 (mask 11) (1755 * 11) UI,
  bAnd(allN 2 (fun j => sfK (pc (pc U (TitsK.S j)) UI)),
    allN 4 (fun j => sfK (pc (pc (pc UI (TitsN.SI j)) U) (TitsN.S j))))))

@[expose] noncomputable def POU (t0 t1 t2 t3 t4 : Nat) : Bool :=
  bIf(allN 3 (fun i => T614EL.any (cmEq t0 t1 t2 t3 t4 (TitsH.S i))),
    strictB (pc (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) T614G1) (fun U =>
      strictB (pinv U) (fun UI => kTests U UI)), true)

@[expose] noncomputable def QOU : Nat → Nat → Nat → Nat → Nat → Nat → Bool := fun _ => POU

end CertificateChecks.KernelSporSch.T614

end
