module

public import Certificates.Kernel.SporSch.PairBT.McLSylFacts
public import CFSG.Certificates.Kernel.SporSch.McLSylowProof
public import Certificates.Kernel.SporSch.Pair.McLCheckP

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLSylK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.Sporadic.Schreier.PairMcL CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.McLSylChk

theorem base_nodup : CFSG.Sporadic.Schreier.PairMcL.baseArr.toList.Nodup := by decide

theorem clSize : (cl.map fun c => c.2.1.size).sum = 22275 := PMcLCheck.facts_proved.2.2.2.2.2

theorem pair_total {rest : List (List Bool × Nat)} (hpos : ∀ c ∈ rest, 0 < c.2)
    {row₀ row₁ : List Nat} (hL₀ : (McLCK.getD 0 clsD0).c ≤ row₀.length * 256)
    (hL₁ : (McLCK.getD 0 clsD0).c ≤ row₁.length * 256)
    (h₀ : ∀ b < row₀.length, cntZK 275 9 (mask 9) (pidn 275 9) 2 5
      (condWords (([false, true], 11) :: rest)) Z (McLCK.getD 0 clsD0) (b * 256) 256 =
        row₀.getD b 0)
    (h₁ : ∀ b < row₁.length, cntZK 275 9 (mask 9) (pidn 275 9) 2 5
      (condWords (([false, true], 11) :: rest)) Zi (McLCK.getD 0 clsD0) (b * 256) 256 =
        row₁.getD b 0) :
    22275 * countPair bs 5 wA (([false, true], 11) :: rest) blocks * 11 =
      898128000 * (row₀.sum + row₁.sum) := by
  have hN : ¬11 ^ 2 ∣ ordK PMcL.LR 5 := by
    rw [ord]
    decide
  have h := pair11_proved sz McLSylFacts.chainS base_nodup (by decide)
    (allN_spec PMcLCheck.perm 0 (by decide)) (allN_spec PMcLCheck.perm 1 (by decide)) cA oA hN
    (bs := bs) (by decide) (groups := groups) (by decide) pZ pG cZ cG sZ sG oZ rel bZZ bZZi
    (d := McLCK.getD 0 clsD0) McLSylFacts.clsOK (Nat.eq_of_beq_eq_true McLSylFacts.hR0) hpos
    hL₀ hL₁ h₀ h₁
  rw [ord, Nat.eq_of_beq_eq_true McLSylFacts.dc0] at h
  rw [PMcLCheck.wA_eq]
  exact h

private theorem total_cl {w : List (Array Nat)} {C : Array (Array Nat) × Array Nat × Array Nat}
    {f : List (Array Nat) → Nat} {N s t : Nat} (hf : f w = N)
    (h : ([(w, C)].map fun c => c.2.1.size).sum = s) (ht : s * N = t) :
    ([(w, C)].map fun c => c.2.1.size * f c.1).sum = t := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h ⊢
  rw [h, hf, ht]

private theorem tot2245 {N : Nat} (h : 22275 * N * 11 = 898128000 * 594) :
    22275 * N = 48498912000 := by
  omega

private theorem tot2246 {N : Nat} (h : 22275 * N * 11 = 898128000 * 22) :
    22275 * N = 1796256000 := by
  omega

theorem facts2245 :
    (cl.map fun c => c.2.1.size * countPair bs 5 c.1 conds blocks).sum = 48498912000 := by
  have hs := clSize
  rw [PMcLCheck.cl_eq] at hs ⊢
  have h := pair_total (rest := [(commPat, 5)]) (by decide)
    (Nat.le_of_ble_eq_true McLSylFacts.len1.1) (Nat.le_of_ble_eq_true McLSylFacts.len1.2)
    McLSylZ1.h0_0 McLSylZ1.h1_0
  rw [Nat.eq_of_beq_eq_true McLSylFacts.rows1] at h
  exact total_cl (f := fun w => countPair bs 5 w [([false, true], 11), (commPat, 5)] blocks)
    (N := countPair bs 5 wA [([false, true], 11), (commPat, 5)] blocks) rfl hs (tot2245 h)

theorem facts2246 :
    (ordB bs (patW wA wB [false, true, true]) 12 = true ∧
      ordB bs (patW wA wB [false, true, false, true, true]) 14 = true ∧
      ordB bs (patW wA wB pat10) 10 = true) ∧
    ((cl.map fun c => c.2.1.size * countPair bs 5 c.1 conds2 blocks).sum = 1796256000) := by
  refine ⟨?_, ?_⟩
  · have e12 : patW [unpack 275 9 (PMcL.S 0)] [unpack 275 9 (PMcL.S 1)] [false, true, true] =
        [PMcL.S 1, PMcL.S 1, PMcL.S 0].map (unpack 275 9) := rfl
    have e14 : patW [unpack 275 9 (PMcL.S 0)] [unpack 275 9 (PMcL.S 1)]
        [false, true, false, true, true] =
        [PMcL.S 1, PMcL.S 1, PMcL.S 0, PMcL.S 1, PMcL.S 0].map (unpack 275 9) := rfl
    have e10 : patW [unpack 275 9 (PMcL.S 0)] [unpack 275 9 (PMcL.S 1)] pat10 =
        [PMcL.S 1, PMcL.S 1, PMcL.S 1, PMcL.S 0, PMcL.S 1, PMcL.S 1, PMcL.S 0, PMcL.S 1,
          PMcL.S 0].map (unpack 275 9) := rfl
    rw [PMcLCheck.wA_eq, PMcLCheck.wB_eq, e12, e14, e10]
    exact ⟨ordWK_sound McLSylFacts.o12, ordWK_sound McLSylFacts.o14,
      ordWK_sound McLSylFacts.o10⟩
  have hs := clSize
  rw [PMcLCheck.cl_eq] at hs ⊢
  have h := pair_total
    (rest := [(commPat, 5), ([false, true, true], 12), ([false, true, false, true, true], 14),
      (pat10, 10)]) (by decide)
    (Nat.le_of_ble_eq_true McLSylFacts.len2.1) (Nat.le_of_ble_eq_true McLSylFacts.len2.2)
    McLSylZ2.h0_0 McLSylZ2.h1_0
  rw [Nat.eq_of_beq_eq_true McLSylFacts.rows2] at h
  exact total_cl (f := fun w => countPair bs 5 w [([false, true], 11), (commPat, 5),
      ([false, true, true], 12), ([false, true, false, true, true], 14), (pat10, 10)] blocks)
    (N := countPair bs 5 wA [([false, true], 11), (commPat, 5), ([false, true, true], 12),
      ([false, true, false, true, true], 14), (pat10, 10)] blocks) rfl hs (tot2246 h)

end CertificateChecks.KernelSporSch.McLSylK

end
