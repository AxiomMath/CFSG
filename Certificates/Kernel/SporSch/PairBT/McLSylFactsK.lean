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

theorem pair_total {rest : List (List Bool × Nat)} (hpos : ∀ c ∈ rest, 0 < c.2)
    {row₀ row₁ : List Nat} (hL₀ : 2025 ≤ row₀.length * 256) (hL₁ : 2025 ≤ row₁.length * 256)
    (h₀ : ∀ b < row₀.length, cntZK 275 9 (mask 9) (pidn 275 9) 2 5
      (condWords (([false, true], 11) :: rest)) Z (clsSub McLZC.clsD 2025 McLZC.RP)
        (b * 256) 256 = row₀.getD b 0)
    (h₁ : ∀ b < row₁.length, cntZK 275 9 (mask 9) (pidn 275 9) 2 5
      (condWords (([false, true], 11) :: rest)) Zi (clsSub McLZC.clsD 2025 McLZC.RP)
        (b * 256) 256 = row₁.getD b 0) :
    22275 * countPair bs 5 wA (([false, true], 11) :: rest) blocks * 11 =
      898128000 * (11 * row₀.sum + 11 * row₁.sum) := by
  have hN : ¬11 ^ 2 ∣ ordK PMcL.LR 5 := by
    rw [ord]
    decide
  have hc : McLZC.clsD.c = 2025 * 11 := by
    rw [Nat.eq_of_beq_eq_true McLSylFacts.dc0]
  have hO := elems_of_slices (c := McLZC.clsD.c) (nb := 88)
    (by rw [Nat.eq_of_beq_eq_true McLSylFacts.dc0]; norm_num) McLZOrbS.all
  have h := pair11_sem sz McLSylFacts.chainS base_nodup (by decide)
    (allN_spec PMcLCheck.perm 0 (by decide)) (allN_spec PMcLCheck.perm 1 (by decide)) cA oA hN
    (bs := bs) (by decide) (groups := groups) (by decide) pZ pG cZ cG sZ sG oZ rel bZZ bZZi
    (d := McLZC.clsD) McLZOrb.sem hpos
    hc hO McLZOrb.hr hL₀ hL₁ h₀ h₁
  rw [ord, Nat.eq_of_beq_eq_true McLSylFacts.dc0] at h
  rw [PMcLCheck.wA_eq]
  exact h

private theorem tot2245 {N : Nat} (h : 22275 * N * 11 = 898128000 * 594) : N = 2177280 := by
  omega

private theorem tot2246 {N : Nat} (h : 22275 * N * 11 = 898128000 * 22) : N = 80640 := by
  omega

theorem facts2245 : countPair bs 5 wA conds blocks = 2177280 := by
  have h := pair_total (rest := [(commPat, 5)]) (by decide) (by simp) (by simp)
    (rows_of_slices McLSylZ1.S0.all fun _ => rfl) (rows_of_slices McLSylZ1.S1.all fun _ => rfl)
  rw [Nat.eq_of_beq_eq_true McLSylFacts.rows1] at h
  have h' := tot2245 h
  exact h'

theorem facts2246 :
    (ordB bs (patW wA wB [false, true, true]) 12 = true ∧
      ordB bs (patW wA wB [false, true, false, true, true]) 14 = true ∧
      ordB bs (patW wA wB pat10) 10 = true) ∧
    countPair bs 5 wA conds2 blocks = 80640 := by
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
  have h := pair_total
    (rest := [(commPat, 5), ([false, true, true], 12), ([false, true, false, true, true], 14),
      (pat10, 10)]) (by decide) (by simp) (by simp)
    (rows_of_slices McLSylZ2.S0.all fun _ => rfl) (rows_of_slices McLSylZ2.S1.all fun _ => rfl)
  rw [Nat.eq_of_beq_eq_true McLSylFacts.rows2] at h
  have h' := tot2246 h
  exact h'

end CertificateChecks.KernelSporSch.McLSylK

end
