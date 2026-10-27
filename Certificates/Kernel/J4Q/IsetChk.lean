module

public import Certificates.Kernel.J4Q.IsetBase

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.IS CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] noncomputable def VGP : List (List Nat) :=
  (List.range 5).map fun i => (List.range 16).map fun j => getN 0 IVG (Nat.add (Nat.mul 16 i) j)

@[expose] noncomputable def VGL : List (List (List Nat)) := VGP.map (List.map unpackP)

@[expose] noncomputable def L17 : List (List Nat) :=
  (List.range 17).map fun i => (List.range 16).map fun j => getN 0 IL17 (Nat.add (Nat.mul 16 i) j)

@[expose] noncomputable def xkP (k : Nat) : Nat := getN 0 XKL k

@[expose] noncomputable def eqP (a b : Nat) : Bool := a % 2 ^ 121 == b % 2 ^ 121

@[expose] noncomputable def hasP (L : List Nat) (x : Nat) : Bool := L.any fun y => eqP x y

@[expose] noncomputable def xcB (p : Nat) : Nat := compB (xkP 1) (compB p (xkP 4))

@[expose] noncomputable def xcsB (p : Nat) : List Nat :=
  [p, xcB p, xcB (xcB p), xcB (xcB (xcB p)), xcB (xcB (xcB (xcB p)))]

@[expose] noncomputable def commB (p : Nat) : Bool :=
  eqP (compB p (xcB p)) (compB (xcB p) p) &&
    (let c := xcsB p
     (List.range 5).all (fun i => (List.range 5).all fun j =>
       eqP (compB (c.getD i idP) (c.getD j idP)) (compB (c.getD j idP) (c.getD i idP))) &&
       eqP (c.foldr compB idP) idP)

@[expose] noncomputable def subsetB (c : List Nat) : List Nat :=
  c.foldr (fun x acc => acc ++ acc.map (compB x)) [idP]

@[expose] noncomputable def spanB (p : Nat) : List Nat := ((subsetB (xcsB p)).map (· % 2 ^ 121)).eraseDups

@[expose] noncomputable def vStepB (acc : List (List Nat)) (p : Nat) : List (List Nat) :=
  if !(eqP p idP) && commB p && !(acc.any fun G => hasP G p) then acc ++ [spanB p] else acc

@[expose] noncomputable def vYB (p : Nat) : Bool := !commB p || VGP.any fun G => hasP G p

@[expose] noncomputable def cubeB (t : Nat) : Nat := compB t (compB t (compB t idP))

@[expose] noncomputable def cIB (k p : Nat) : Bool :=
  VGP.all fun G =>
    !(G.all fun g => hasP G (compB p (compB g p))) || !(hasP G (cubeB (compB (xkP k) p))) ||
      IDL.any fun c => actB (xkP k) c == c && actB p c == c && G.all fun g => actB g c == c

@[expose] noncomputable def cIIB (k p : Nat) : Bool :=
  !(eqP (cubeB (compB (xkP k) p)) idP) ||
    IDL.any (fun c => actB (xkP k) c == c && actB p c == c) ||
    L17.all fun S => !(S.all fun s => S.contains (actB p s)) ||
      S.all fun s => s == 0 || actB (compB (xkP k) p) s != s

@[expose] noncomputable def iAllB (p : Nat) : Bool :=
  vYB p && (cIB 1 p && cIB 2 p && cIB 3 p && cIB 4 p) && (cIIB 1 p && cIIB 2 p && cIIB 3 p && cIIB 4 p)

@[expose] noncomputable def iChunk (c : Nat) : List Nat :=
  (List.range 64).map fun j => iKey (Nat.add (Nat.mul 64 c) j)

@[expose] noncomputable def iCK (c : Nat) : Bool :=
  andB (List.foldl vStepB (VGP.take (getN 0 IVC c)) (iChunk c) == VGP.take (getN 0 IVC (Nat.succ c)))
    (allR 64 fun j => iAllB (iKey (Nat.add (Nat.mul 64 c) j)))

@[expose] noncomputable def iCH (h c : Nat) : Bool := iCK (Nat.add (Nat.mul 338 h) c)

@[expose] noncomputable def iCA (c : Nat) : Bool := iCH 0 c

@[expose] noncomputable def iCB (c : Nat) : Bool := iCH 1 c

end CertificateChecks.KernelJ4Q

end
