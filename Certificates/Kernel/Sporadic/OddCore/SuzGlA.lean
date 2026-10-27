module

public import Certificates.Kernel.Sporadic.OddCore.SuzGlF

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzGl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Sporadic.SuzRecog.B0Gluing CFSG.Sporadic.SuzRecog.B0GluingData
open CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor

@[expose] noncomputable def cosK (a : Nat) : Nat :=
  min (min (mulK a zIL[0]!) (mulK a zIL[1]!)) (min (mulK a zIL[2]!) (mulK a zIL[3]!))

@[expose] noncomputable def keyK (a b c d : Nat) : List Nat :=
  [cosK a, cosK b, cosK c, cosK d, cmK a c, cmK a d]

@[expose] noncomputable def thetaKeyK (i : Nat) : List Nat :=
  keyK (thK i (gK 0)) (thK i (gK 1)) (thK i (gK 2)) (thK i (gK 3))

@[expose] noncomputable def ctGammaK (t r i : Nat) : Nat := mulK (mulK t (gammaGenK r i)) (invK t)

@[expose] noncomputable def dictK (q₀ q₁ q₂ q₃ : Nat) : Option (Nat × Nat) :=
  (List.range 64).findSome? fun t =>
    if cosK (ctGammaK t 0 0) == cosK q₀ && cosK (ctGammaK t 0 1) == cosK q₁ &&
        cosK (ctGammaK t 0 2) == cosK q₂ && cosK (ctGammaK t 0 3) == cosK q₃ then
      ((List.range 16).find? fun r => ctGammaK t r 0 == q₀ && ctGammaK t r 1 == q₁ &&
        ctGammaK t r 2 == q₂ && ctGammaK t r 3 == q₃).map fun r => (t, r)
    else none

@[expose] noncomputable def decompOfK (a b c d : Nat) : Option (Nat × Nat × Nat) :=
  ((List.range 36).find? (fun i => thetaKeyK i == keyK a b c d)).bind fun i =>
    (dictK (thIK i a) (thIK i b) (thIK i c) (thIK i d)).map fun x => (i, x.1, x.2)

@[expose] noncomputable def decompEqK (i t r a b c d : Nat) : Bool :=
  decide (i < 36) && decide (t < 64) && decide (r < 16) &&
    a == thK i (ctGammaK t r 0) && b == thK i (ctGammaK t r 1) && c == thK i (ctGammaK t r 2) &&
    d == thK i (ctGammaK t r 3)

@[expose] noncomputable def inKerK (a b c d : Nat) : Bool :=
  anyBelow 15 fun v => chiK v a == 0 && chiK v b == 0 && chiK v c == 0 && chiK v d == 0

@[expose] noncomputable def invPsK : List Nat := (List.range 64).filter fun a => mulK a a == 0

@[expose] noncomputable def cPairsK : List (Nat × Nat) :=
  invPsK.flatMap fun a => (invPsK.filter fun b => cmK a b == 0).map fun b => (a, b)

@[expose] noncomputable def autB (p q : Nat × Nat) : Bool :=
  !(cmK p.1 q.1 == cmK p.2 q.2 && mulK (mulK (cmK p.1 q.2) (cmK p.2 q.1)) (cmK p.1 q.1) == 0) ||
    inKerK p.1 p.2 q.1 q.2 ||
    (decompOfK p.1 p.2 q.1 q.2).any fun x => decompEqK x.1 x.2.1 x.2.2 p.1 p.2 q.1 q.2

@[expose] noncomputable def autSl (s : Nat) : Bool :=
  allBlk (Nat.mul 16 s) (fun j => cPairsK.all (autB (cPairsK.getD j (0, 0)))) 16

theorem cosP_eq (a : Nat) : cosP a = cosK a := by
  unfold cosP cosK
  simp only [mulP_eq, zI_eq]

theorem keyOf_eq (a b c d : Nat) : keyOf a b c d = keyK a b c d := by
  unfold keyOf keyK
  simp only [cosP_eq, cmP_eq]

theorem thetaKey_eq (i : Nat) : thetaKey i = thetaKeyK i := by
  unfold thetaKey thetaKeyK
  simp only [th_eq, gP_eq, keyOf_eq]

theorem ctGamma_eq (t r i : Nat) : ctGamma t r i = ctGammaK t r i := by
  unfold ctGamma ctGammaK
  simp only [mulP_eq, invP_eq, gammaGen_eq]

theorem dictOf_eq (q₀ q₁ q₂ q₃ : Nat) : dictOf q₀ q₁ q₂ q₃ = dictK q₀ q₁ q₂ q₃ := by
  unfold dictOf dictK
  simp only [cosP_eq, ctGamma_eq]

theorem decompOf_eq (a b c d : Nat) : decompOf a b c d = decompOfK a b c d := by
  unfold decompOf decompOfK
  simp only [thetaKey_eq, keyOf_eq, thI_eq, dictOf_eq]

theorem decompEq_eq (i t r a b c d : Nat) : decompEq i t r a b c d = decompEqK i t r a b c d := by
  unfold decompEq decompEqK
  simp only [th_eq, ctGamma_eq]

theorem inKer_eq (a b c d : Nat) : inKer a b c d = inKerK a b c d := by
  unfold inKer inKerK
  simp only [chi_eq]

theorem cPairs_eq : cPairs = cPairsK := by
  unfold cPairs cPairsK invPs invPsK
  simp only [mulP_eq, cmP_eq, oneI_eq]

@[expose] def autBody (p q : Nat × Nat) : Bool :=
  !(cmP p.1 q.1 == cmP p.2 q.2 && mulP (mulP (cmP p.1 q.2) (cmP p.2 q.1)) (cmP p.1 q.1) == oneI) ||
    inKer p.1 p.2 q.1 q.2 || decompOK p.1 p.2 q.1 q.2

theorem autCheck_eq : autCheck = cPairs.all fun p => cPairs.all (autBody p) := rfl

theorem autBody_eq (p q : Nat × Nat) : autBody p q = autB p q := by
  unfold autBody autB decompOK
  simp only [cmP_eq, mulP_eq, oneI_eq, inKer_eq, decompOf_eq, decompEq_eq]

end CertificateChecks.KernelSpor.SuzGl

end
