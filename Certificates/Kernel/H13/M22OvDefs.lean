module

public import Certificates.Kernel.H13.M22Tac

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H13.M22Cert

@[expose] def m22ov1 : Bool :=
  orbL.all fun uw => uw.1 == v0 || U4.contains uw.1 ||
    pE.any fun p₁ => mvN p₁ uw.1 != uw.1 &&
      pE.any fun p₂ => mvN p₂ uw.1 != uw.1 && mvN p₂ uw.1 != mvN p₁ uw.1

@[expose] def m22ov2 : Bool :=
  let hS : Std.HashSet (List ℕ) := Std.HashSet.ofList s0E
  rP.all fun r => hS.contains r.1 && mulN r.1 r.2 == one12

@[expose] def m22ov3 : Bool :=
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList pE
  s0E.all fun s => rP.any fun r => hP.contains (mulN r.2 s)

@[expose] def m22ovU (uw : ℕ × List ℕ) : Bool :=
  let h0 : Std.HashSet (List ℕ) := Std.HashSet.ofList (mE 0)
  let h1 : Std.HashSet (List ℕ) := Std.HashSet.ofList (mE 1)
  !(U4.contains uw.1) || rP.all fun r =>
    let y := mulN (tW uw.2) r.1
    h0.contains y || h1.contains y ||
      (let B := elemsOf 12 (pG ++ [y]) 769
       decide (769 ≤ B.length) && nodupB 12 B)

@[expose] def m22ov4 : Bool := orbL.all m22ovU

@[expose] def m22ov5 : Bool :=
  [0, 1].all fun i => subB 12 (pG ++ [mRep.getD i one12]) (mE i) && (mE i).length == 768

theorem m22_ovB_split : ovB = (m22ov1 && m22ov2 && m22ov3 && m22ov4 && m22ov5) := rfl

end CertificateChecks.KernelH13

end
