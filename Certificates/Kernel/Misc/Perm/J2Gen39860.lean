module

public import Certificates.Kernel.Misc.Perm.J2Rel
public import CFSG.RankThree.PartTwo.Sec17.PropUJ2GenInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2Fam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec17.PropU.J2Gen
open CertificateChecks.KernelMisc.J2C3 (cm I)

theorem rVG : ∀ l < 6, R vGens[l]! (VG l) := by
  unfold vGens
  exact R.vk6

theorem okVG : ∀ l < 6, okA vGens[l]! = true := by
  intro l hl
  interval_cases l <;> exact (rVG _ (by norm_num)).ok (by quickRfl) (by quickRfl)

theorem R.memKlein {g h : Array ℕ} {p q r : ℕ} {t : Array ℕ} (hg : R g p) (hh : R h q)
    (ht : R t r) : inKlein g h t =
      (Nat.beq r I || Nat.beq r p || Nat.beq r q || Nat.beq r (cm p q)) := by
  unfold inKlein
  rw [ht.eq R.id, ht.eq hg, ht.eq hh, ht.eq (hg.comp hh)]

theorem chkE_K : chkE = true := by
  unfold chkE
  rw [J2C3.okx, J2C3.okz, (rX.comp (rX.comp rX)).eq R.id, (rZ.comp (rZ.comp rZ)).eq R.id,
    rX.commA rZ, rX.eq R.id, rZ.eq R.id, rZ.eq rX, rZ.eq (rX.comp rX)]
  quickRfl

theorem chkV_K : chkV = true := by
  unfold chkV
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun l hl => ?_, fun k hk => ?_⟩
  · rw [List.mem_range] at hl
    rw [okVG l hl, ((rVG l hl).comp (rVG l hl)).eq R.id]
    interval_cases l <;> quickRfl
  · rw [List.mem_range] at hk
    have h0 := rVG (2 * k) (by omega)
    have h1 := rVG (2 * k + 1) (by omega)
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [h0.commA h1, R.memKlein h0 h1 (rX.conj h0), R.memKlein h0 h1 (rX.conj h1),
      R.memKlein h0 h1 (rZ.conj h0), R.memKlein h0 h1 (rZ.conj h1)]
    interval_cases k <;> quickRfl

theorem chkGen_K : chkGen = true := by
  unfold chkGen evalWord
  rw [(R.foldl rVG wordA (by quickRfl) R.id).eq (rAB (k := 0) (by norm_num)),
    (R.foldl rVG wordB (by quickRfl) R.id).eq (rAB (k := 1) (by norm_num))]
  quickRfl

theorem j2GenCheck_K : j2GenCheck = true := by
  unfold j2GenCheck
  rw [chkE_K, chkV_K, chkGen_K]
  rfl

end CertificateChecks.KernelMisc.J2Fam

end
