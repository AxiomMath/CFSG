module

public import Certificates.Kernel.Sporadic.OddCore.J3BetaA5

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3BetaA5

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def parA : Array Nat := Array.ofFn (n := 60) fun i => parOf J3BA.PL i.val

@[expose] noncomputable def labA : Array Nat := Array.ofFn (n := 60) fun i => labOf J3BA.PL i.val

@[expose] noncomputable def imgK : Array Table :=
  (List.range' 1 59).foldl (fun r k => r.push (compT 5 r[parA[k]!]! piA5J3[labA[k]!]!))
    #[idT 5]

@[expose] noncomputable def invL5 (x : Table) : Array Nat :=
  (List.range 5).foldl (fun r i => r.set! (x[i]!).toNat i) (Array.replicate 5 0)

@[expose] noncomputable def pK (x : Table) : Bool :=
  (List.range 5).all fun i => decide ((x[i]!).toNat < 5) && (invL5 x)[(x[i]!).toNat]! == i

@[expose] noncomputable def eq5 (x y : Table) : Bool := (List.range 5).all fun i => ap x i == ap y i

@[expose] noncomputable def cayK : Bool :=
  imgK.size == 60 && imgK.toList.all pK && eq5 imgK[0]! (idT 5) &&
    (List.range 60).all (fun k => (List.range 2).all fun l =>
      Nat.blt (r32 J3BACl (4 * k + l)) 60 &&
        eq5 imgK[r32 J3BACl (4 * k + l)]! (compT 5 imgK[k]! piA5J3[l]!)) &&
    (List.range 60).all (fun k => eq5 imgK[k]! (idT 5) == Nat.beq (J3BA.T k) (pidn 6156 13)) &&
    piA5J3.toList.all pK

theorem cay_ok : cayK = true := by
  decide +kernel

theorem cay_neg : ((List.range 60).all fun k => (List.range 2).all fun l =>
    eq5 imgK[r32 J3BACl (4 * k + l)]! (compT 5 imgK[k]! piA5J3[1 - l]!)) = false := by
  decide +kernel

end CertificateChecks.KernelSpor.J3BetaA5

end
