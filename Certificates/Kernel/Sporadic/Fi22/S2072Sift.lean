module

public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.E2065T
public import Certificates.Kernel.Sporadic.Fi22.H2066c0
public import Certificates.Kernel.Sporadic.Fi22.H2066c1
public import Certificates.Kernel.Sporadic.Fi22.H2066c2
public import Certificates.Kernel.Sporadic.Fi22.H2066c3
public import Certificates.Kernel.Sporadic.Fi22.H2066c4
public import CFSG.Certificates.Kernel.Spor.SiftBKSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2072

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22X

@[expose] noncomputable def memK (S SI LR ST : Nat → Nat) (kS BP lo k : Nat) : Bool :=
  allN k fun j => strictB (Fi22CentT.L (Nat.add lo j)) fun q =>
    bAnd(cn q, bAnd(siftP q,
      siftBK 3510 12 (mask 12) (3510 * 12) 6 S SI LR ST kS 6 0 (baseImK 12 (mask 12) 6 q BP)))

theorem mc0s : memK Fi22H0.S Fi22H0.SI Fi22H0.LR Fi22H0.ST 19 Fi22H0.BP 80 3 = true := by quickRfl
theorem mc0w : memK Fi22H0.S Fi22H0.SI Fi22H0.LR Fi22H0.ST 19 Fi22H0.BP 108 26 = true := by
  quickRfl
theorem mc1s : memK Fi22H1.S Fi22H1.SI Fi22H1.LR Fi22H1.ST 16 Fi22H1.BP 83 5 = true := by quickRfl
theorem mc1w : memK Fi22H1.S Fi22H1.SI Fi22H1.LR Fi22H1.ST 16 Fi22H1.BP 134 14 = true := by
  quickRfl
theorem mc2s : memK Fi22H2.S Fi22H2.SI Fi22H2.LR Fi22H2.ST 9 Fi22H2.BP 88 6 = true := by quickRfl
theorem mc2w : memK Fi22H2.S Fi22H2.SI Fi22H2.LR Fi22H2.ST 9 Fi22H2.BP 148 14 = true := by
  quickRfl
theorem mc3s : memK Fi22H3.S Fi22H3.SI Fi22H3.LR Fi22H3.ST 19 Fi22H3.BP 94 9 = true := by quickRfl

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

@[expose] noncomputable def mc3F (x : Nat) : Bool :=
  strictB (Fi22CentT.L x) fun q =>
    bAnd(cn q, bAnd(siftP q,
      siftBK 3510 12 (mask 12) (3510 * 12) 6 Fi22H3.S Fi22H3.SI Fi22H3.LR Fi22H3.ST 19 6 0
        (baseImK 12 (mask 12) 6 q Fi22H3.BP)))

theorem mc3w_0 : allN 4 (fun j => mc3F (Nat.add 162 j)) = true := by quickRfl
theorem mc3w_1 : allN 4 (fun j => mc3F (Nat.add 166 j)) = true := by quickRfl
theorem mc3w_2 : allN 4 (fun j => mc3F (Nat.add 170 j)) = true := by quickRfl
theorem mc3w_3 : allN 4 (fun j => mc3F (Nat.add 174 j)) = true := by quickRfl
theorem mc3w_4 : allN 4 (fun j => mc3F (Nat.add 178 j)) = true := by quickRfl
theorem mc3w_5 : allN 4 (fun j => mc3F (Nat.add 182 j)) = true := by quickRfl
theorem mc3w_6 : allN 4 (fun j => mc3F (Nat.add 186 j)) = true := by quickRfl
theorem mc3w_7 : allN 4 (fun j => mc3F (Nat.add 190 j)) = true := by quickRfl
theorem mc3w_8 : allN 4 (fun j => mc3F (Nat.add 194 j)) = true := by quickRfl
theorem mc3w_9 : allN 4 (fun j => mc3F (Nat.add 198 j)) = true := by quickRfl
theorem mc3w_10 : allN 4 (fun j => mc3F (Nat.add 202 j)) = true := by quickRfl
theorem mc3w_11 : allN 4 (fun j => mc3F (Nat.add 206 j)) = true := by quickRfl
theorem mc3w_12 : allN 4 (fun j => mc3F (Nat.add 210 j)) = true := by quickRfl
theorem mc3w_13 : allN 4 (fun j => mc3F (Nat.add 214 j)) = true := by quickRfl
theorem mc3w_14 : allN 4 (fun j => mc3F (Nat.add 218 j)) = true := by quickRfl
theorem mc3w_15 : allN 2 (fun j => mc3F (Nat.add 222 j)) = true := by quickRfl

theorem mc3w : memK Fi22H3.S Fi22H3.SI Fi22H3.LR Fi22H3.ST 19 Fi22H3.BP 162 62 = true := by
  show allN 62 (fun j => mc3F (Nat.add 162 j)) = true
  exact allN_splitS (a := 4) (c := 58) (b' := 166) rfl rfl mc3w_0
      (allN_splitS (a := 4) (c := 54) (b' := 170) rfl rfl mc3w_1
      (allN_splitS (a := 4) (c := 50) (b' := 174) rfl rfl mc3w_2
      (allN_splitS (a := 4) (c := 46) (b' := 178) rfl rfl mc3w_3
      (allN_splitS (a := 4) (c := 42) (b' := 182) rfl rfl mc3w_4
      (allN_splitS (a := 4) (c := 38) (b' := 186) rfl rfl mc3w_5
      (allN_splitS (a := 4) (c := 34) (b' := 190) rfl rfl mc3w_6
      (allN_splitS (a := 4) (c := 30) (b' := 194) rfl rfl mc3w_7
      (allN_splitS (a := 4) (c := 26) (b' := 198) rfl rfl mc3w_8
      (allN_splitS (a := 4) (c := 22) (b' := 202) rfl rfl mc3w_9
      (allN_splitS (a := 4) (c := 18) (b' := 206) rfl rfl mc3w_10
      (allN_splitS (a := 4) (c := 14) (b' := 210) rfl rfl mc3w_11
      (allN_splitS (a := 4) (c := 10) (b' := 214) rfl rfl mc3w_12
      (allN_splitS (a := 4) (c := 6) (b' := 218) rfl rfl mc3w_13
      (allN_splitS (a := 4) (c := 2) (b' := 222) rfl rfl mc3w_14
      (mc3w_15)))))))))))))))

theorem mc4s : memK Fi22H4.S Fi22H4.SI Fi22H4.LR Fi22H4.ST 16 Fi22H4.BP 103 5 = true := by
  quickRfl
theorem mc4w : memK Fi22H4.S Fi22H4.SI Fi22H4.LR Fi22H4.ST 16 Fi22H4.BP 224 16 = true := by
  quickRfl

end CertificateChecks.KernelSpor.S2072

end
