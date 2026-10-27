module

public import Certificates.Kernel.Sporadic.L2.Text
public import Certificates.Kernel.Sporadic.L2.TextN
public import Certificates.Kernel.Sporadic.L2.TextE
public import Certificates.Kernel.Sporadic.L2.TextV
public import Certificates.Kernel.Sporadic.L2.TextI
public import Certificates.Kernel.Sporadic.L2.Pins
public import Certificates.Kernel.Sporadic.L2.XCD
public import Certificates.Kernel.Sporadic.OddCore.SuzWK
public import Certificates.Kernel.Sporadic.OddCore.SuzTwC
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Kernel.Sporadic.Q3A.KT

public section

namespace CertificateChecks.KernelSpor.L2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs

local notation "pgk" => pg 11 (mask 11)
local notation "pgv" => pg 12 (mask 12)
local notation "pc" => pcomp 1782 11 (mask 11)
local notation "Idn" => pidn 1782 11
local notation "inv" => invEqK 1782 11 (mask 11) (1782 * 11)

@[expose] noncomputable def XG (s : Nat) : Nat := Q3AK.XK s
@[expose] noncomputable def XGI (s : Nat) : Nat := Q3AK.XIK s
@[expose] noncomputable def RHO : Nat := SuzTwG 2
@[expose] noncomputable def RHOI : Nat := Q3AI 2
@[expose] noncomputable def T1 : Nat := SuzInvT1.F 0
@[expose] noncomputable def W0 : Nat := SuzTwG 6

@[expose] noncomputable def aParK (i : Nat) : Nat := pgv (L2TA.F 0) i
@[expose] noncomputable def aLabK (i : Nat) : Nat := pgv (L2TA.F 1) i
@[expose] noncomputable def wParK (j : Nat) : Nat := pgv (L2TW.F 0) j
@[expose] noncomputable def wLabK (j : Nat) : Nat := pgv (L2TW.F 1) j
@[expose] noncomputable def TK (j k : Nat) : Nat := L2T (Nat.add (Nat.mul 3 j) k)
@[expose] noncomputable def VK (s v : Nat) : Nat := pgv (L2V s) v
@[expose] noncomputable def nbK (x k : Nat) : Nat := pgv (L2NB.F x) k
@[expose] noncomputable def tParK (z : Nat) : Nat := pgv (L2SP.F 0) z
@[expose] noncomputable def tDepK (z : Nat) : Nat := pgv (L2SP.F 1) z

@[expose] noncomputable def fA (i : Nat) : Nat := fpK 11 (mask 11) (L2A i)
@[expose] noncomputable def fT (i : Nat) : Nat := fpK 11 (mask 11) (L2T i)

@[expose] noncomputable def aStep (i : Nat) : Bool :=
  strictB (aParK i) fun p => strictB (aLabK i) fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l 2, Nat.beq (L2A i) (pc (XG l) (pc (L2A p) (XGI l)))))

@[expose] noncomputable def aVt (i : Nat) : Bool :=
  bAnd(bIf(Nat.beq i 0, Nat.beq (L2A 0) T1, aStep i),
    bAnd(canonK 1782 11 (mask 11) (1782 * 11) (L2A i), inv (L2A i) (L2A i)))

@[expose] noncomputable def vtA (s v : Nat) : Bool :=
  strictB (VK s v) fun v' => bAnd(Nat.blt v' 2835,
    bAnd(Nat.beq (fA v') (fpCK 11 (mask 11) (XG s) (XGI s) (L2A v)),
      bIf(bAnd(Nat.blt 0 v', bAnd(Nat.beq (aParK v') v, Nat.beq (aLabK v') s)), true,
        Nat.beq (L2A v') (pc (XG s) (pc (L2A v) (XGI s))))))

@[expose] noncomputable def aChk (v : Nat) : Bool := bAnd(aVt v, bAnd(vtA 0 v, vtA 1 v))

@[expose] noncomputable def aSl (s : Nat) : Bool := allBlk (Nat.mul 5 s) aChk 5

@[expose] noncomputable def wStep (j : Nat) : Bool :=
  strictB (wParK j) fun p => strictB (wLabK j) fun l =>
    bAnd(Nat.blt p j, bAnd(Nat.blt l 2, Nat.beq (TK j 0) (pc (XG l) (pc (TK p 0) (XGI l)))))

@[expose] noncomputable def tVt (j : Nat) : Bool :=
  bAnd(bIf(Nat.beq j 0, Nat.beq (TK 0 0) W0, wStep j),
  bAnd(Nat.beq (TK j 1) (pc RHO (pc (TK j 0) RHOI)),
  bAnd(Nat.beq (TK j 2) (pc RHO (pc (TK j 1) RHOI)),
  bAnd(allN 3 (fun k => canonK 1782 11 (mask 11) (1782 * 11) (TK j k)),
  bAnd(inv (TK j 0) (TK j 0), Bool.not (Nat.beq (TK j 0) (TK j 1)))))))

@[expose] noncomputable def vtW (s j : Nat) : Bool :=
  strictB (VK s (Nat.add 2835 j)) fun v' => bAnd(Nat.ble 2835 v', bAnd(Nat.blt v' 2997,
    strictB (Nat.sub v' 2835) fun j' => strictB (pc (XG s) (pc (TK j 0) (XGI s))) fun C =>
      bIf(Nat.beq (TK j' 0) C, true, bIf(Nat.beq (TK j' 1) C, true, Nat.beq (TK j' 2) C))))

@[expose] noncomputable def wChk (j : Nat) : Bool := bAnd(tVt j, bAnd(vtW 0 j, vtW 1 j))

@[expose] noncomputable def wSl (s : Nat) : Bool := allBlk (Nat.mul 3 s) wChk 3

@[expose] noncomputable def ordA (m : Nat) : Nat := pgv (L2OA 0) m
@[expose] noncomputable def posA (i : Nat) : Nat := pgv (L2PA 0) i
@[expose] noncomputable def ordT (m : Nat) : Nat := pgv (L2OT 0) m
@[expose] noncomputable def posT (i : Nat) : Nat := pgv (L2PT 0) i

@[expose] noncomputable def sortK (n : Nat) (f ord pos : Nat → Nat) : Bool :=
  bAnd(allN (Nat.pred n) (fun m => Nat.blt (f (ord m)) (f (ord (Nat.succ m)))),
    allN n (fun i => strictB (pos i) fun m => bAnd(Nat.blt m n, Nat.beq (ord m) i)))

@[expose] noncomputable def occK (x y : Nat) : Bool :=
  bIf(Nat.blt x 2835, Bool.not (allN 36 fun k => Bool.not (Nat.beq (nbK x k) y)), false)

@[expose] noncomputable def adjK (x y : Nat) : Bool :=
  bAnd(Bool.not (Nat.beq x y), bIf(occK x y, true, occK y x))

@[expose] noncomputable def grK (s x : Nat) : Bool :=
  bIf(Nat.blt x 2835, allN 36 (fun k =>
    bAnd(Nat.blt (nbK x k) 2997, adjK (VK s x) (VK s (nbK x k)))), true)

@[expose] noncomputable def grChk (x : Nat) : Bool := bAnd(grK 0 x, grK 1 x)

@[expose] noncomputable def sv (e : Nat) : Nat := pgv (L2SV.F (Nat.div e 147)) (Nat.mod e 147)
@[expose] noncomputable def si (e : Nat) : Nat :=
  pg 20 (mask 20) (L2SI.F (Nat.div e 98)) (Nat.mod e 98)
@[expose] noncomputable def S0 (i : Nat) : Nat :=
  nIf(Nat.blt i 2996, tParK (Nat.succ i), sv (Nat.mul 3 (Nat.sub i 2996)))
@[expose] noncomputable def S1 (i : Nat) : Nat :=
  nIf(Nat.blt i 2996, Nat.succ i, sv (Nat.succ (Nat.mul 3 (Nat.sub i 2996))))
@[expose] noncomputable def S2 (i : Nat) : Nat := sv (Nat.add (Nat.mul 3 (Nat.sub i 2996)) 2)
@[expose] noncomputable def S3 (i : Nat) : Nat := si (Nat.mul 2 (Nat.sub i 2996))
@[expose] noncomputable def S4 (i : Nat) : Nat := si (Nat.succ (Nat.mul 2 (Nat.sub i 2996)))

@[expose] noncomputable def endsK (j x y : Nat) : Bool :=
  bIf(bAnd(Nat.beq (S0 j) x, Nat.beq (S1 j) y), true, bAnd(Nat.beq (S0 j) y, Nat.beq (S1 j) x))

@[expose] noncomputable def ty2 (x : Nat) : Nat := nIf(Nat.ble 2835 x, 1, 0)

@[expose] noncomputable def triK (x y z : Nat) : Bool :=
  bAnd(adjK x y, bAnd(adjK y z, bAnd(adjK x z,
    Nat.beq (Nat.add (Nat.add (ty2 x) (ty2 y)) (ty2 z)) 1)))

@[expose] noncomputable def stepK (i : Nat) : Bool :=
  strictB (S0 i) fun a => strictB (S1 i) fun b =>
  bAnd(Nat.blt a 2997, bAnd(Nat.blt b 2997, bAnd(adjK a b,
    bIf(Nat.blt i 2996,
      bIf(bAnd(Nat.blt 0 b, Nat.beq (tParK b) a), true, bAnd(Nat.blt 0 a, Nat.beq (tParK a) b)),
      strictB (S2 i) fun c => strictB (S3 i) fun i₁ => strictB (S4 i) fun i₂ =>
        bAnd(Nat.blt c 2997, bAnd(Nat.blt i₁ i, bAnd(Nat.blt i₂ i, bAnd(endsK i₁ a c,
          bAnd(endsK i₂ c b, triK a c b)))))))))

@[expose] noncomputable def treeK (z : Nat) : Bool :=
  bIf(Nat.beq z 0, true, strictB (tParK z) fun p =>
    bAnd(Nat.blt p 2997, bAnd(Nat.blt (tDepK p) (tDepK z), adjK p z)))

@[expose] noncomputable def emK (x : Nat) : Bool :=
  allN 36 fun k => strictB (nbK x k) fun y => bIf(Nat.beq x y, true, bIf(Nat.ble 2997 y, true,
    strictB (pg 20 (mask 20) (L2EM.F x) k) fun e => bAnd(Nat.blt e 76545, endsK e x y)))

@[expose] noncomputable def grSl (s : Nat) : Bool := allBlk (Nat.mul 160 s) grChk 160

@[expose] noncomputable def stepG (i : Nat) : Bool := bIf(Nat.blt i 76545, stepK i, true)

@[expose] noncomputable def stSl (s : Nat) : Bool := allBlk (Nat.mul 1000 s) stepG 1000

@[expose] noncomputable def teG (x : Nat) : Bool :=
  bIf(Nat.blt x 2997, bAnd(treeK x, bIf(Nat.blt x 2835, emK x, true)), true)

@[expose] noncomputable def teSl (s : Nat) : Bool := allBlk (Nat.mul 500 s) teG 500

@[expose] noncomputable def memXK (G : Nat) : Bool :=
  siftK 1782 11 (mask 11) (1782 * 11) Idn L2XC.LR L2XC.TRI L2XC.BP 5 0 G

@[expose] noncomputable def elemK (k : Nat) : Bool :=
  bAnd(inv (L2EL.F k) (L2EI k), memXK (L2EL.F k))

@[expose] noncomputable def sendsK (G GI v v' : Nat) : Bool :=
  bIf(Nat.blt v 2835, bAnd(Nat.blt v' 2835, Nat.beq (L2A v') (pc G (pc (L2A v) GI))),
    bAnd(Nat.ble 2835 v', bAnd(Nat.blt v' 2997,
      strictB (pc G (pc (TK (Nat.sub v 2835) 0) GI)) fun C => strictB (Nat.sub v' 2835) fun j' =>
        bIf(Nat.beq (TK j' 0) C, true, bIf(Nat.beq (TK j' 1) C, true, Nat.beq (TK j' 2) C)))))

@[expose] noncomputable def sendsE (k v v' : Nat) : Bool := sendsK (L2EL.F k) (L2EI k) v v'

end CertificateChecks.KernelSpor.L2K

end
