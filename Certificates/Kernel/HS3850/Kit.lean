module

public import Certificates.Kernel.HS3850.Small
public import Certificates.Kernel.LocalQT.HSAutO.F4064
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.Misc.RuInvCov
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import CFSG.Sporadic.SmallOddCore.HSLocalCheckInputs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KC.PkPow CFSG.KD.LQT.C4126
open CFSG.KD.LQT.HO CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native

theorem cent_parts {k : Nat} (hk : k < 43) :
    natArr (hsCentTbl k) = unpack 3850 12 (HC.F k) ∧ Cn (HC.F k) :=
  ⟨hsCentTbl_eq hk, allN_spec canon_hc k hk⟩

theorem comp_pc' {p q : Nat} (hp : Cn p) (hq : Cn q) :
    comp 3850 (unpack 3850 12 p) (unpack 3850 12 q) = unpack 3850 12 (pc p q) :=
  comp_unp hp hq

theorem cn_pc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) :=
  CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem beq_pc' {p q : Nat} (hp : Cn p) (hq : Cn q) :
    (unpack 3850 12 p == unpack 3850 12 q) = Nat.beq p q :=
  CFSG.KS.PEnum.beq_unpack hp hq

theorem idTab_idn : idTab 3850 = unpack 3850 12 idn := idTab_unp (by decide)

theorem countP_nfix (n w p : Nat) :
    ((List.range n).countP fun x => (unpack n w p)[x]! == x) = nfix n w p := by
  unfold nfix
  rw [CFSG.KC.Misc.RuInv.P.foldN_count, List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro x hx
  rw [CFSG.KC.BfsPin.unpack_getElem!, if_pos (List.mem_range.1 hx), Bool.eq_iff_iff, beq_iff_eq,
    Nat.beq_eq]

theorem fixedCount_fx (p : Nat) :
    CFSG.ComponentClassification.J2Cover.fixedCount 3850 (unpack 3850 12 p) = fx p :=
  countP_nfix 3850 12 p

theorem wordTabS_unp {gs : Array Tab} {L : Nat → Nat} (ls : List Nat)
    (h : ∀ l ∈ ls, gs[l]! = unpack 3850 12 (L l) ∧ Cn (L l)) :
    wordTabS 3850 gs ls = unpack 3850 12 (wfoldR L ls) ∧ Cn (wfoldR L ls) := by
  have e : wordTabS 3850 gs ls = (ls.map fun l => gs[l]!).foldr (comp 3850) (idTab 3850) := by
    unfold wordTabS
    rw [List.foldr_map]
  rw [e]
  exact foldr_unp ls h

theorem c2_parts {l : Nat} (hl : l < 4) :
    hsC2Tabs[l]! = unpack 3850 12 (lc2 l) ∧ Cn (lc2 l) := by
  have e : hsC2Tabs[l]! = natArr (hsCentTbl (l + 13)) := by
    unfold hsC2Tabs
    rw [getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn]
  rw [e, Nat.add_comm]
  exact cent_parts (by omega)

theorem c2Word {ls : List Nat} (hls : ∀ l ∈ ls, l < 4) :
    wordTabS 3850 hsC2Tabs ls = unpack 3850 12 (wfoldR lc2 ls) ∧ Cn (wfoldR lc2 ls) :=
  wordTabS_unp ls fun l hl => c2_parts (hls l hl)

end CFSG.KD.HS3850

end
