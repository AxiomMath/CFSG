module

public import Certificates.Kernel.J4Loc.TrioChk
public import Certificates.Kernel.J4Loc.I5Chk
public import CFSG.Certificates.Kernel.J4Loc.TrioOctSound

public section

namespace CertificateChecks.KernelJ4Loc

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KD.J4Loc CFSG.KS.J4Loc CFSG.Sporadic.J4.QT
  CFSG.Quasithin.J4Loc

theorem k4174_octAll : OctAll letterRows TRK TRR 3795 TRI0 :=
  octBlk_all (B := 119) (fun k hk => TRC.all k hk) (by decide)

theorem k4174_letterRows : ∀ l < 6, (letterRows.getD l []).length = 11 := by
  intro l hl
  interval_cases l <;> rfl

theorem k4174_I0 : TRI0 < 3795 := lt_of_blt (andB_true ch4174_v0).1

theorem k4174_V0 : octF TRK TRI0 = V0F := by
  unfold octF
  rw [eqLK_spec (andB_true ch4174_v0).2]
  decide

theorem k4174_trio_eq : TrioOct = octF TRK '' {i | i < 3795} :=
  trioOct_eq k4174_octAll k4174_letterRows k4174_I0 k4174_V0

theorem k4174_trio_ncard : TrioOct.ncard = 3795 :=
  trioOct_ncard k4174_octAll k4174_letterRows k4174_I0 k4174_V0

theorem k4174_trio_props {W : Finset ℕ} (hW : W ∈ TrioOct) :
    W.card = 8 ∧ 0 ∈ W ∧ (∀ x ∈ W, x < 2048) ∧ ∀ x ∈ W, ∀ y ∈ W, x ^^^ y ∈ W :=
  trioOct_props k4174_octAll k4174_letterRows k4174_I0 k4174_V0 hW

theorem k4177_oct_mem : ({0, 965, 1979, 1243, 165, 864, 1822, 1150} : Finset ℕ) ∈ TrioOct := by
  obtain ⟨-, h⟩ := andB_true ch4177_oct
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨h1, h2⟩ := andB_true h
  rw [k4174_trio_eq]
  refine ⟨I5I, lt_of_blt h1, ?_⟩
  ext x
  unfold octF
  rw [List.mem_toFinset, mem_of_keyK_eq h2 x]
  simp

end CertificateChecks.KernelJ4Loc

end
