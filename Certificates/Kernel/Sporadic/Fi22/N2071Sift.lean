module

public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.E2065
public import Certificates.Kernel.Sporadic.Fi22.E2067
public import Certificates.Kernel.Sporadic.Fi22.H2066c0
public import CFSG.Certificates.Kernel.Spor.SiftBKSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.N2071

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22X

theorem allN_splitS {f : Nat → Bool} {b a c n b' : Nat} (hn : n = a + c) (hb : b' = b + a)
    (h1 : allN a (fun j => f (Nat.add b j)) = true)
    (h2 : allN c (fun j => f (Nat.add b' j)) = true) :
    allN n (fun j => f (Nat.add b j)) = true :=
  CFSG.KS.PackFld.allN_of_forall fun j hj => by
    rcases Nat.lt_or_ge j a with hja | hja
    · exact CFSG.KS.allN_spec h1 j hja
    · have h := CFSG.KS.allN_spec h2 (j - a) (by omega)
      have e : Nat.add b' (j - a) = Nat.add b j := by
        simp only [Nat.add_eq]
        omega
      rwa [e] at h

@[expose] noncomputable def poolF (x : Nat) : Bool := bAnd(cn (Fi22CentT.L x),
    bAnd(permOK 3510 12 (mask 12) (3510 * 12) (Fi22CentT.L x) (inv (Fi22CentT.L x)),
    bAnd(siftP (Fi22CentT.L x),
      siftBK 3510 12 (mask 12) (3510 * 12) 6 Fi22H0.S Fi22H0.SI Fi22H0.LR Fi22H0.ST 19 6 0
        (baseImK 12 (mask 12) 6 (Fi22CentT.L x) Fi22H0.BP))))

theorem pool_0 : allN 8 (fun j => poolF (Nat.add 240 j)) = true := by quickRfl
theorem pool_1 : allN 8 (fun j => poolF (Nat.add 248 j)) = true := by quickRfl
theorem pool_2 : allN 8 (fun j => poolF (Nat.add 256 j)) = true := by quickRfl
theorem pool_3 : allN 8 (fun j => poolF (Nat.add 264 j)) = true := by quickRfl
theorem pool_4 : allN 8 (fun j => poolF (Nat.add 272 j)) = true := by quickRfl
theorem pool_5 : allN 8 (fun j => poolF (Nat.add 280 j)) = true := by quickRfl
theorem pool_6 : allN 8 (fun j => poolF (Nat.add 288 j)) = true := by quickRfl
theorem pool_7 : allN 8 (fun j => poolF (Nat.add 296 j)) = true := by quickRfl

theorem pool : allN 64 (fun j => bAnd(cn (Fi22CentT.L (Nat.add 240 j)),
    bAnd(permOK 3510 12 (mask 12) (3510 * 12) (Fi22CentT.L (Nat.add 240 j))
      (inv (Fi22CentT.L (Nat.add 240 j))),
    bAnd(siftP (Fi22CentT.L (Nat.add 240 j)),
      siftBK 3510 12 (mask 12) (3510 * 12) 6 Fi22H0.S Fi22H0.SI Fi22H0.LR Fi22H0.ST 19 6 0
        (baseImK 12 (mask 12) 6 (Fi22CentT.L (Nat.add 240 j)) Fi22H0.BP))))) = true := by
  show allN 64 (fun j => poolF (Nat.add 240 j)) = true
  exact allN_splitS (a := 8) (c := 56) (b' := 248) rfl rfl pool_0
      (allN_splitS (a := 8) (c := 48) (b' := 256) rfl rfl pool_1
      (allN_splitS (a := 8) (c := 40) (b' := 264) rfl rfl pool_2
      (allN_splitS (a := 8) (c := 32) (b' := 272) rfl rfl pool_3
      (allN_splitS (a := 8) (c := 24) (b' := 280) rfl rfl pool_4
      (allN_splitS (a := 8) (c := 16) (b' := 288) rfl rfl pool_5
      (allN_splitS (a := 8) (c := 8) (b' := 296) rfl rfl pool_6
      (pool_7)))))))

theorem cnA : allN 2 (fun i => cn (Fi22CentT.L (Nat.add 304 i))) = true := by quickRfl
theorem cnT0 : cn (Fi22ExtT.L 21) = true := by quickRfl
theorem comm : allN 2 (fun i => Nat.beq (c (Fi22CentT.L (Nat.add 304 i)) (Fi22ExtT.L 21))
    (c (Fi22ExtT.L 21) (Fi22CentT.L (Nat.add 304 i)))) = true := by quickRfl
theorem s0 : siftP (Fi22CentT.L 304) = true := by quickRfl
theorem s1 : bIf(siftP (Fi22CentT.L 305), false, true) = true := by quickRfl
theorem s2 : siftP (c GO (Fi22CentT.L 305)) = true := by quickRfl

end CertificateChecks.KernelSpor.N2071

end
