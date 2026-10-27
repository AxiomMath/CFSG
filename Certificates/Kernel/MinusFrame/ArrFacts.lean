module

public import Certificates.Kernel.MinusFrame.ArrChecks
public import Certificates.Kernel.MinusFrame.SmallFacts
import CFSG.Certificates.Kernel.Spor.PackWord

public section

namespace CertificateChecks.KernelMinusFrame

open CFSG.OddTranspositions.PartThree CFSG.OddTranspositions.PartThree.MinusFrame
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermPinK
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CertificateChecks.KernelMinusEnum

theorem gC {k : Nat} (hk : k < 65) : canonK 65 7 (mask 7) (65 * 7) (ME.G k) = true :=
  allN_spec kG k (by rw [nums.1]; exact hk)

theorem rowE {k : Nat} (hk : k < 65) : minusTable[k]! = unpack 65 7 (ME.G k) :=
  bind.2 k (by rw [nums.1]; exact hk)

theorem notMem : MinusFrame.notMemCheck () = true := by
  unfold MinusFrame.notMemCheck
  dsimp only
  rw [bindX.1, List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  rw [rowE hk, eqA_unpack (canonX (by omega)) (gC hk)]
  exact allN_spec kNotMemP k hk

theorem cent : MinusFrame.centCheck () = true := by
  unfold MinusFrame.centCheck
  dsimp only
  rw [bindX.1, List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  have hX := canonX (k := 0) (by omega)
  rw [rowE hk]
  unfold commutesA
  rw [compA_unpack hX (gC hk), compA_unpack (gC hk) hX,
    eqA_unpack (canonK_pcomp hX (gC hk)) (canonK_pcomp (gC hk) hX)]
  exact allN_spec kCentP k hk

theorem notMul : MinusFrame.notMulCheck () = true := by
  unfold MinusFrame.notMulCheck
  dsimp only
  rw [bindX.1, List.all_eq_true]
  intro a _
  rw [List.all_eq_true]
  intro b _
  have ha := cent_lt' a
  have hb := cent_lt' b
  rw [rowE ha, rowE hb, compA_unpack (gC ha) (gC hb),
    eqA_unpack (canonK_pcomp (gC ha) (gC hb)) (canonX (by omega))]
  exact allN_spec (allN_spec kNotMulP a a.2) b b.2

theorem conjX : MinusFrame.conjCommuteCheck (minusEnum ()) = true := by
  have hk := kConjP
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hp, hne⟩, hc⟩ := hk
  have hX := canonX (k := 0) (by omega)
  have hx := canonX (k := 1) (by omega)
  have hi : canonK 65 7 (mask 7) (65 * 7) (pinvS 65 7 (mask 7) (XT 1)) = true :=
    (PP_of_permOK kSz hp).inv.1
  have hy := canonK_pcomp (canonK_pcomp hx hX) hi
  unfold MinusFrame.conjCommuteCheck
  dsimp only
  rw [xMem, bindX.1, bindX.2.1, validA_unpack hp, invCand_unpack hp, compA_unpack hx hX,
    compA_unpack (canonK_pcomp hx hX) hi, eqA_unpack hy hX]
  unfold commutesA
  rw [compA_unpack hX hy, compA_unpack hy hX,
    eqA_unpack (canonK_pcomp hX hy) (canonK_pcomp hy hX)]
  change (true && !Nat.beq (pm (pm (XT 1) (XT 0)) (pinvS 65 7 (mask 7) (XT 1))) (XT 0) &&
    Nat.beq (pm (XT 0) (pm (pm (XT 1) (XT 0)) (pinvS 65 7 (mask 7) (XT 1))))
      (pm (pm (pm (XT 1) (XT 0)) (pinvS 65 7 (mask 7) (XT 1))) (XT 0)) && true) = true
  rw [hne, hc]
  rfl

end CertificateChecks.KernelMinusFrame

end
