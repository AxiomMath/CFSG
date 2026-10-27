module

public import Certificates.Data.Kernel.Fi22Twist.Search
public import Certificates.Kernel.Fi22Twist.Data
public import Certificates.Kernel.Sporadic.Fi22.N3153Data

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist

@[expose] noncomputable def blk (j lo hi k : Nat) : Bool :=
  allBlk (Nat.add lo (Nat.mul (nat_lit 16) k)) (fun n =>
    bIf(Nat.blt n hi, blockK TF DF CFSG.KD.N3153.M BF HF KF j n, true)) (nat_lit 16)

@[expose] noncomputable def ch431009cs0_ (k : Nat) : Bool := blk (nat_lit 0) (nat_lit 0) (nat_lit 81) k

@[expose] noncomputable def ch431009cs1_ (k : Nat) : Bool := blk (nat_lit 1) (nat_lit 81) (nat_lit 405) k

@[expose] noncomputable def ch431009cs2_ (k : Nat) : Bool := blk (nat_lit 2) (nat_lit 405) (nat_lit 891) k

@[expose] noncomputable def ch431009cs3_ (k : Nat) : Bool := blk (nat_lit 3) (nat_lit 891) (nat_lit 2835) k

@[expose] noncomputable def ch431009cs4_ (k : Nat) : Bool := blk (nat_lit 4) (nat_lit 2835) (nat_lit 2997) k

end CertificateChecks.KernelFi22Twist

end
