module

public import Certificates.Kernel.U43Pk.Data
public import Certificates.Data.Kernel.U43Pk.Cover
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_blocked_root CertificateChecks.KernelU43Pk.CV "Certificates/Kernel/U43Pk/data/cov.bin"
  6 4 65535 168318 14569792805913029119

#kc_repo #kc_blocked_root CertificateChecks.KernelU43Pk.RP "Certificates/Kernel/U43Pk/data/reps.bin"
  4 7 340282366920938463463374607431768211455 1536 2379026175695536336

namespace CertificateChecks.KernelU43Pk

open CFSG.KD.U43Pk CFSG.KC.Enum

@[expose] noncomputable def CL (i : Nat) : Nat := CV i

@[expose] noncomputable def OI (a : Nat) : Nat := CV (Nat.add 1024 a)

@[expose] noncomputable def II (b : Nat) : Nat := CV (Nat.add 1408 b)

@[expose] noncomputable def GI (k : Nat) : Nat := CV (Nat.add 1599 k)

@[expose] noncomputable def GJ (k : Nat) : Nat := CV (Nat.add 3903 k)

@[expose] noncomputable def TR (k : Nat) : Nat := CV (Nat.add 6207 k)

@[expose] noncomputable def TS (k : Nat) : Nat := CV (Nat.add 8511 k)

@[expose] noncomputable def WD (a b : Nat) : Nat := CV (Nat.add 10815 (Nat.add (Nat.mul 191 a) b))

@[expose] noncomputable def RX (r : Nat) : Nat := RP r

@[expose] noncomputable def RT (r : Nat) : Nat := RP (Nat.add 48 r)

@[expose] noncomputable def o8D (i : Nat) : Bool := Nat.beq (Nat.mod (CL i) 2) 1

@[expose] noncomputable def invD (i : Nat) : Bool := Nat.beq (Nat.div (CL i) 2) 1

@[expose] noncomputable def u43ClsBlk (q : Nat) : Bool :=
  allBlk (Nat.mul 64 q) (fun i => strictB i fun i => Nat.beq (clsK (T i)) (CL i)) 64

@[expose] noncomputable def u43PairBlk (q : Nat) : Bool :=
  allBlk (Nat.mul 8 q) (fun a => strictB a fun a => strictB (T (OI a)) fun x =>
    allBlk 0 (fun b => strictB (T (II b)) fun t => pairK (WD a b) x t) 191) 8

@[expose] noncomputable def conjC (k : Nat) : Bool :=
  strictB (TR k) fun r => strictB (TS k) fun s => strictB (GI k) fun i => strictB (GJ k) fun j =>
    bAnd(Nat.blt r 48, bAnd(Nat.blt s 1024, bAnd(Nat.blt i 1024, bAnd(Nat.blt j 1024,
      conjK (T s) (T i) (T j) (RX r) (RT r)))))

@[expose] noncomputable def u43ConjBlk (q : Nat) : Bool :=
  allBlk (Nat.mul 64 q) (fun k => strictB k conjC) 64

@[expose] noncomputable def repDigC : Bool := allBlk 0 (fun r => bAnd(digK (RX r), digK (RT r))) 48

end CertificateChecks.KernelU43Pk

end
