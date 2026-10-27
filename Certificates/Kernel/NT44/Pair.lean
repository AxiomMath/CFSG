module

public import Certificates.Kernel.NT44.Pack
public import Certificates.Kernel.NT44.Pack2
public import Certificates.Kernel.NT44.Pack3
public import Certificates.Data.Kernel.Misc.IdxMul
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelNT44

open CFSG.GH74.GLS.NT44.PermutationNative CFSG.KC.Misc.IdxMul
open CFSG.KC.Enum (pg)
open CFSG.KS (mask)
open CFSG.KC.Ord (andB notB)
open CFSG.KC.LQT.P (allN anyL impB)
open CFSG.KC.Misc.Clos (allR)

@[expose] noncomputable def nt44Mul : Nat → Nat → Nat := mulK 8 10 4 (nt44TF 0) (nt44PL 0) 8

@[expose] noncomputable def nt44Am (a : Nat) : Nat := pg 256 (mask 256) (nt44AM 0) a

@[expose] noncomputable def nt44Row : Nat → Bool := pairRow nt44Mul nt44Am 3 8 (nt44O4 0) 84

@[expose] noncomputable def nt44Wit (q : Nat) : Bool :=
  andB (Nat.beq (nt44Mul (witnesses ())[q]!.sIndex.val (witnesses ())[q]!.sIndex.val) 0)
    (witL 2688 12 9 nt44P0 nt44P0I nt44L nt44LI nt44KS (witnesses ())[q]!.sIndex.val
      (witnesses ())[q]!.aIndex.val (witnesses ())[q]!.cWord (witnesses ())[q]!.sign)

theorem nt44_trf : allN 256 (fun x => allN 4 fun k =>
    Nat.beq (stepF 8 4 (nt44TF 0) x k) (pg 8 (mask 8) (nt44Tr x) k)) = true := by quickRfl

theorem nt44_pl : plAt 10 4 8 (nt44PL 0) (nt44Par 0) 8 (parent ()).toList 0 = true := by
  simp only [parent, Array.toList_append, List.toList_toArray]
  quickRfl

theorem nt44_ord : allN 256 (ordAt nt44Mul 8 (nt44O4 0) 84) = true := by quickRfl

theorem nt44_pair0 : allR 0 21 nt44Row = true := by quickRfl
theorem nt44_pair1 : allR 21 21 nt44Row = true := by quickRfl
theorem nt44_pair2 : allR 42 21 nt44Row = true := by quickRfl
theorem nt44_pair3 : allR 63 21 nt44Row = true := by quickRfl

theorem nt44_am : allN 3 (fun a => allN 256 fun x => impB (bitB (nt44Am a) x)
    (anyL (((actorSets ())[a]!).map Fin.val) fun y => Nat.beq y x)) = true := by quickRfl

theorem nt44_wit0 : nt44Wit 0 = true := by quickRfl
theorem nt44_wit1 : nt44Wit 1 = true := by quickRfl
theorem nt44_wit2 : nt44Wit 2 = true := by quickRfl

end CertificateChecks.KernelNT44

end
