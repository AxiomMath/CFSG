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
  (List.range 15).all (fun k => (rP.getD k ([], [])).1 == evalW 12 s0G (rPS0W.getD k [])) &&
    rP.all fun r => mulN r.1 r.2 == one12

@[expose] def m22ov3 : Bool :=
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList pE
  rP.length == 15 && (List.range 15).all fun i => (List.range i).all fun j =>
    !(hP.contains (mulN (rP.getD j ([], [])).2 (rP.getD i ([], [])).1))

@[expose] def m22ovU (uw : ℕ × List ℕ) : Bool :=
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList pE
  let h0 : Std.HashSet (List ℕ) := Std.HashSet.ofList (mE 0)
  let h1 : Std.HashSet (List ℕ) := Std.HashSet.ofList (mE 1)
  !(U4.contains uw.1) || rP.all fun r =>
    let y := mulN (tW uw.2) r.1
    h0.contains y || h1.contains y || ovFourB hP y

@[expose] def m22ov4 : Bool := orbL.all m22ovU

@[expose] def m22ov5 : Bool :=
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList pE
  [0, 1].all fun i => nodupB 12 (mE i) && (mE i).length == 768 && (mCosP i).length == 3 &&
    (mCosP i).all (fun c => validB 12 c.2 && mulN c.1 c.2 == one12) &&
    (mCosP i).any (fun c => hP.contains (mulN c.2 one12)) &&
    (pG ++ [mRep.getD i one12]).all fun g => (mCosP i).all fun c => (mCosP i).any fun c' =>
      hP.contains (mulN c'.2 (mulN g c.1))

theorem m22_ovB_split : ovB = (m22ov1 && m22ov2 && m22ov3 && m22ov4 && m22ov5) := rfl

end CertificateChecks.KernelH13

end
