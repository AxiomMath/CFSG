module

public import Certificates.Kernel.Sporadic.ONL37.Data
public import Certificates.Kernel.Sporadic.ON2.Data
public import Certificates.Kernel.Sporadic.ON2.Words
public import Certificates.Data.Kernel.Spor.ONCSOp
public import CFSG.RankThree.Native.ONTripleData

public section

namespace CertificateChecks.KernelSpor.ONL37

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONC CFSG.KS.Words CFSG.RankThree.Native.ONTriple
open CFSG.KD.ONL37

@[expose] noncomputable def FA (j : Nat) : Nat := List.getD ONW.LA j (nat_lit 0)
@[expose] noncomputable def FB (j : Nat) : Nat := List.getD ONW.LB j (nat_lit 0)

@[expose] noncomputable def ckW (c : Nat) : Nat := List.getD CK (Nat.mul (nat_lit 3) c) (nat_lit 0)
@[expose] noncomputable def ckA (c : Nat) : Nat :=
  List.getD CK (Nat.add (Nat.mul (nat_lit 3) c) (nat_lit 1)) (nat_lit 0)
@[expose] noncomputable def ckB (c : Nat) : Nat :=
  List.getD CK (Nat.add (Nat.mul (nat_lit 3) c) (nat_lit 2)) (nat_lit 0)

@[expose] noncomputable def ipC (c : Nat) : Nat := List.getD IP c (nat_lit 0)

@[expose] noncomputable def imgW (k : Nat) : List Int := decW (IMW.WC k) (IMW.WL k)

@[expose] noncomputable def chunkW (c : Nat) : List Int := ((imgW (ckW c)).drop (ckA c)).take (ckB c)

@[expose] noncomputable def preC (c : Nat) : Nat :=
  nIf(Nat.beq (ckA c) (nat_lit 0), ONE, ipC (Nat.sub c (nat_lit 1)))

@[expose] noncomputable def l37Wch (c : Nat) : Bool := chunkK FA FB (chunkW c) (preC c) (ipC c)

@[expose] def imgIdx : List Nat := [0, 1, 2, 3, 5, 6, 7]

@[expose] noncomputable def ckOK : Bool :=
  bAnd(Nat.beq CK.length (nat_lit 24), bAnd(Nat.beq IP.length (nat_lit 8),
  bAnd(allN (nat_lit 8) fun c => bIf(Nat.beq (ckA c) (nat_lit 0), true,
    bAnd(Nat.blt (nat_lit 0) c, bAnd(Nat.beq (ckW (Nat.sub c (nat_lit 1))) (ckW c),
      Nat.beq (Nat.add (ckA (Nat.sub c (nat_lit 1))) (ckB (Nat.sub c (nat_lit 1)))) (ckA c)))),
    allN (nat_lit 7) fun k => strictB (List.getD imgIdx k (nat_lit 0)) fun c =>
      bAnd(Nat.blt c (nat_lit 8), bAnd(Nat.beq (ckW c) k,
        Nat.beq (Nat.add (ckA c) (ckB c)) (IMW.WL k))))))

@[expose] noncomputable def imgL (k : Nat) : Nat := ipC (List.getD imgIdx k (nat_lit 0))

@[expose] noncomputable def initL : List Nat :=
  [imgL 0, imgL 1, imgL 2, imgL 3, imgL 4, imgL 5, imgL 6, ONE]

@[expose] noncomputable def VIf (r : Nat) : Nat := List.getD VI r (nat_lit 0)

@[expose] noncomputable def MLf (q : Nat) : Nat := List.getD ML q (nat_lit 0)

@[expose] def regL (l : Nat) : Nat := (rL.getD 0 []).getD l 0
@[expose] def regV (m i : Nat) : Nat := ((rV.getD 0 []).getD m []).getD i 0

@[expose] noncomputable def finL (st : List Nat × Bool) : Bool :=
  strictB LL fun L => strictB HH fun H => strictB CM fun cm => strictB RM fun rm =>
  bAnd(st.2, bAnd(Nat.beq st.1.length (nat_lit 200),
    allN (nat_lit 12) fun q =>
      strictB (regL (Nat.div q (nat_lit 6))) fun n =>
      strictB (regV (Nat.div (Nat.mod q (nat_lit 6)) (nat_lit 2)) (Nat.mod q (nat_lit 2))) fun v =>
        bAnd(Bool.rec (motive := fun _ => Bool) true false (Nat.beq (VIf n) (nat_lit 0)),
          Nat.beq (mul3 L H cm rm (mul3 L H cm rm (VIf n) (List.getD st.1 v (nat_lit 0)))
            (List.getD st.1 n (nat_lit 0))) (MLf q))))

@[expose] noncomputable def l37Prog : Bool := sopK initL VIf finL progM

@[expose] noncomputable def fixK (k : Nat) : Bool :=
  strictB CS fun cs => strictB DS fun ds => strictB LL fun L => strictB HH fun H =>
  strictB CM fun cm => strictB RM fun rm =>
  strictB (List.getD W k (nat_lit 0)) fun w =>
  bAnd(Nat.blt w (nat_lit 245520), bAnd(canon (key ONW.K w),
    strictB (batK cs ds (fun _ => key ONW.K w) (nat_lit 0) (nat_lit 1)) fun X =>
      allN (nat_lit 4) fun j =>
        Nat.beq (mul3 L H cm rm (MLf (List.getD GI (Nat.add (Nat.mul (nat_lit 4) k) j) (nat_lit 0))) X) X))

@[expose] noncomputable def l37Fix : Bool :=
  bAnd(ckOK, bAnd(Nat.beq GI.length (nat_lit 36), bAnd(Nat.beq W.length (nat_lit 9),
    allN (nat_lit 9) fixK)))

end CertificateChecks.KernelSpor.ONL37

end
