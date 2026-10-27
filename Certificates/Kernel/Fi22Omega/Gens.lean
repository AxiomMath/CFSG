module

public import Certificates.Data.Kernel.Fi22Omega.Words
public import Certificates.Kernel.Fi22Omega.Data
public import Certificates.Kernel.I242.YData
public import Certificates.Kernel.I242.Text
public import Certificates.Kernel.Sporadic.Fi22.G3147
public import CFSG.Monster.B.Fischer.Fi22OmegaMaxInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Omega

open CFSG.KC.Fi22Omega CFSG.KC.Enum CFSG.KC.I242 CertificateChecks.KernelI242
  CertificateChecks.KernelSpor

@[expose] noncomputable def h1K : Nat := wordK Y.S [6, 5, 4, 5, 7, 3]

@[expose] noncomputable def h2K : Nat := wordK Y.S [2, 0, 5, 1, 2, 7]

@[expose] noncomputable def u0L : List Nat := CFSG.Monster.B.Fischer.fi22OmegaU0.toList

@[expose] noncomputable def rootM (c : Nat) : Nat := msk (recAt T (MS c))

@[expose] noncomputable def withA (k : (Nat → Nat) → Bool) : Bool :=
  strictB (pinv (Fi22CGT.F 0)) fun i0 => strictB (pinv (Fi22CGT.F 1)) fun i1 =>
    k (letA (Fi22CGT.F 0) (Fi22CGT.F 1) i0 i1)

theorem bindH0 : bindOK NT h1K 0 = true := by quickRfl
theorem bindH1 : bindOK NT h2K 1 = true := by quickRfl
theorem u0 : Nat.beq (rootM 0) (wordMask (fun _ => 0) 0 u0L) = true := by quickRfl
theorem roots : withA (fun A => allN 3 (fun c => Nat.beq (rootM (Nat.succ c))
    (wordMask A (MS (Nat.add 4 c)) u0L))) = true := by quickRfl
theorem orbs : band (Nat.beq (rootM 0) (Nat.lor (MS 7) (Nat.lor (MS 8) (MS 9))))
    (band (Nat.beq (Nat.land (MS 7) (MS 8)) 0)
      (band (Nat.beq (Nat.land (MS 7) (MS 9)) 0) (Nat.beq (Nat.land (MS 8) (MS 9)) 0))) = true := by
  quickRfl
theorem cosets : withA (fun A => allN 6 (fun j => allN 3 (fun k =>
    mapsOK A (MS (Nat.add 10 j)) u0L (MS (Nat.add 7 k)) (MS (Nat.add 7 (piOf j k)))))) = true := by
  quickRfl
theorem yFix : allN 8 (fun r => allN 3 (fun k =>
    mapsOK (fun _ => Y.S r) 1 u0L (MS (Nat.add 7 k)) (MS (Nat.add 7 k)))) = true := by quickRfl
theorem qFix : allN 2 (fun k => mapsOK (fun _ => H.F k) 1 u0L (rootM 0) (rootM 0)) = true := by
  quickRfl
theorem lets : allN 2 (fun k => band (cpK (Fi22CGT.F k)) (cpK (H.F k))) = true := by quickRfl
theorem cnt : cntOK T = true := by quickRfl

end CertificateChecks.KernelFi22Omega

end
