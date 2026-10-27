module

public import Certificates.Kernel.Fi22Rho.Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22GuestRankData
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22GuestRankData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Guest

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen.Native
  CFSG.AGLEmbedding.KFactProofs.Fi22Guest

@[expose] def gWords : List Word := [wx, wy] ++ nData.map fun t => t.2.2

meta def guestTabs : Array Nat := Id.run do
  let O := CFSG.Sporadic.Fi22.Native.orbitData ()
  let bi := invT 3510 O.beta
  let n := 3510
  let wt := fun (w : Word) => wordTab n O.alpha O.alpha O.beta bi w
  let ws : List Word := [wx, wy] ++ nData.map fun t => t.2.2
  let mut out : Array Nat := #[]
  for k in [0:20] do
    let T := wt (ws.getD k [])
    for x in [0:n] do
      out := out.push (ap T x)
  for j in [0:18] do
    let T := invT n (wt (ws.getD (j + 2) []))
    for x in [0:n] do
      out := out.push (ap T x)
  for i in [0:4] do
    let T := eTab n O.alpha O.alpha O.beta bi i
    for x in [0:n] do
      out := out.push (ap T x)
  return out

end CertificateChecks.KernelFi22Guest

#krowsw CertificateChecks.KernelFi22Guest.GT 12 CertificateChecks.KernelFi22Guest.guestTabs

namespace CertificateChecks.KernelFi22Guest

open CFSG.KC.Enum CFSG.KS CFSG.KS.Row CFSG.AGLEmbedding.KFactProofs.Fi22Guest
  CertificateChecks.KernelFi22Rho

@[expose] noncomputable def tb (k y : Nat) : Nat :=
  rg (nat_lit 12) (mask (nat_lit 12)) GT (nat_lit 0) (Nat.add (Nat.mul (nat_lit 3510) k) y)

@[expose] noncomputable def wSl (s : Nat) : Bool :=
  strictB (Nat.div s (nat_lit 6)) fun k => strictB (Nat.mul (Nat.mod s (nat_lit 6)) (nat_lit 585))
    fun lo => allN (nat_lit 585) fun t =>
      Nat.beq (tb k (Nat.add lo t)) (wordK (List.getD gWords k []) (Nat.add lo t))

@[expose] noncomputable def nT (j y : Nat) : Nat := tb (Nat.add (nat_lit 2) j) y

@[expose] noncomputable def nI (j y : Nat) : Nat := tb (Nat.add (nat_lit 20) j) y

@[expose] noncomputable def eT (i y : Nat) : Nat := tb (Nat.add (nat_lit 38) i) y

@[expose] noncomputable def lmap (s : Int) (y : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => nT (Nat.pred k) y) (fun k => nI k y) s

@[expose] noncomputable def eComp (i y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) y (fun s _ ih => strictN ih fun z => lmap s z)
    (List.getD eData i [])

@[expose] noncomputable def iterK (f : Nat → Nat) (m y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) y (fun _ ih => strictN ih f) m

@[expose] noncomputable def mvK (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) n (fun k ih => nIf(Nat.beq (f k) k, ih, k)) n

@[expose] noncomputable def movesK (f : Nat → Nat) : Bool :=
  strictB (mvK f (nat_lit 3510)) fun w => bAnd(Nat.blt w (nat_lit 3510), !(Nat.beq (f w) w))

@[expose] noncomputable def invChk : Bool :=
  allN (nat_lit 18) fun j => allN (nat_lit 3510) fun x =>
    bAnd(Nat.blt (nI j x) (nat_lit 3510), Nat.beq (nT j (nI j x)) x)

@[expose] noncomputable def eChk : Bool :=
  allN (nat_lit 4) fun i => allN (nat_lit 3510) fun x => Nat.beq (eT i x) (eComp i x)

@[expose] noncomputable def e3Chk : Bool :=
  allN (nat_lit 4) fun i => allN (nat_lit 3510) fun x => Nat.beq (iterK (eT i) (nat_lit 3) x) x

@[expose] noncomputable def commChk : Bool :=
  allN (nat_lit 4) fun i => allN (nat_lit 4) fun j => allN (nat_lit 3510) fun x =>
    Nat.beq (eT i (eT j x)) (eT j (eT i x))

@[expose] noncomputable def prodMap (t y : Nat) : Nat :=
  iterK (eT (nat_lit 0)) (Nat.div t (nat_lit 27))
    (iterK (eT (nat_lit 1)) (Nat.mod (Nat.div t (nat_lit 9)) (nat_lit 3))
      (iterK (eT (nat_lit 2)) (Nat.mod (Nat.div t (nat_lit 3)) (nat_lit 3))
        (iterK (eT (nat_lit 3)) (Nat.mod t (nat_lit 3)) y)))

@[expose] noncomputable def prodChk : Bool :=
  allN (nat_lit 80) fun t => movesK (prodMap (Nat.succ t))

@[expose] noncomputable def qMap (j y : Nat) : Nat :=
  nIf(Nat.beq j (nat_lit 0), tb (nat_lit 0) y, nIf(Nat.beq j (nat_lit 1), tb (nat_lit 1) y,
    tb (nat_lit 0) (iterK (tb (nat_lit 1)) (Nat.pred j) y)))

@[expose] noncomputable def relChk : Bool :=
  bAnd(allN (nat_lit 3510) fun z => bAnd(Nat.beq (iterK (tb (nat_lit 0)) (nat_lit 5) z) z,
      bAnd(Nat.beq (iterK (tb (nat_lit 1)) (nat_lit 5) z) z,
        Nat.beq (tb (nat_lit 0) (tb (nat_lit 1) z)) (tb (nat_lit 1) (tb (nat_lit 0) z)))),
    allN (nat_lit 18) fun k =>
      strictB (List.getD nData k (0, 0, [])).1 fun j =>
      strictB (List.getD nData k (0, 0, [])).2.1 fun m =>
      allN (nat_lit 3510) fun z => Nat.beq (nT k (qMap j z)) (iterK (qMap j) m (nT k z)))

@[expose] noncomputable def qMvChk : Bool :=
  allN (nat_lit 18) fun k => strictB (List.getD nData k (0, 0, [])).1 fun j => movesK (qMap j)

end CertificateChecks.KernelFi22Guest

end
