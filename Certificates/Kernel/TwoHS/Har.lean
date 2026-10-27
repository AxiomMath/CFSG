module

public import Certificates.Kernel.TwoHS.Four
public import Certificates.Kernel.TwoHS.HYOps
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl2
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl2
meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
meta import CFSG.Certificates.CosetTableShort

public section

set_option maxRecDepth 400000
set_option Elab.async false

#ks_chars CFSG.KD.TwoHS.CJ CFSG.EvenSporadicStandard.TwoHS.harConjHex
#kmisc_hexflat CFSG.KD.TwoHS.CJ CFSG.EvenSporadicStandard.TwoHS.harConjHex 3 3850 12 2

#kc_repo #kc_json_gz CFSG.KD.TwoHS "Certificates/Kernel/TwoHS/data/cjw.json.gz" 71
  15293426016868792600 (cjW : List (List Nat))

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KD.LQT.C4126 CFSG.KD.LQT.HN
open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Recognition.HSMultiplier
open CFSG.KS.MulH (wfoldK)

@[expose] noncomputable def HYF (i : Fin 6) : Nat := HY.F i.val

@[expose] noncomputable def cmH (v : Nat) : Bool := (List.finRange 6).all fun i =>
  Nat.beq (CFSG.KD.TwoHS.pc (HYF i) v) (CFSG.KD.TwoHS.pc v (HYF i))

theorem hm_idc : cmH idK = true := by quickRfl

theorem hm_coxK : hsCoxeter.all (fun r => strictB (EVK HYF HYF r) fun v =>
    bIf(Nat.beq v idK, true, cmH v)) = true := by quickRfl

theorem hm_extraK : hsExtra.all (fun r => strictB (EVK HYF HYF r) fun v =>
    bIf(Nat.beq v idK, true, cmH v)) = true := by quickRfl

theorem hm_comm : (List.finRange 6).all (fun i => Nat.beq (EVK HYF HYF (hsCommWord i)) (HYF i)) =
    true := by quickRfl

theorem hl_u : (((List.range 3).all fun j =>
    invEqK 11200 14 (mask 14) (11200 * 14) (WK (harUW.getD j [])) (WKI (harUW.getD j []))) &&
    !Nat.beq (UK [1, 2, 1, 2, 3, 1, 2, 1, 2, 3]) idK &&
    Nat.beq (CFSG.KD.TwoHS.pc (UK [1, 2, 1, 2, 3]) (UK [1, 2, 1, 2, 3]))
      (UK [1, 2, 1, 2, 3, 1, 2, 1, 2, 3])) = true := by quickRfl

@[expose] noncomputable def A3 (i : Fin 2) : Nat := HS.F i.val

@[expose] noncomputable def A3I (i : Fin 2) : Nat := pinv (HS.F i.val)

@[expose] noncomputable def EV3 {m : Nat} (G GI : Fin m → Nat) (wd : List (Fin m × Bool)) : Nat :=
  wd.foldl (fun acc l => CFSG.KS.HSAutN.pc acc (cond l.2 (G l.1) (GI l.1))) idn

@[expose] noncomputable def XK (i : Fin 6) : Nat := EV3 A3 A3I (hsGenWords.getD i.val [])

@[expose] noncomputable def XKI (i : Fin 6) : Nat := pinv (XK i)

@[expose] noncomputable def LX (l : Nat) : Nat := XK ⟨(l - 1) % 6, Nat.mod_lt _ (by norm_num)⟩

@[expose] noncomputable def UXL (l : Nat) : Nat :=
  wfoldK 3850 12 (mask 12) LX (harUW.getD (l - 1) []) idn

@[expose] noncomputable def UXK (wd : List Nat) : Nat := wfoldK 3850 12 (mask 12) UXL wd idn

theorem hp_a : (List.finRange 2).all (fun i => invK (A3 i)) = true := by quickRfl

theorem hp_x : (List.finRange 6).all (fun i => invK (XK i)) = true := by quickRfl

theorem hp_rels : hsRels.all (fun r => Nat.beq (EV3 XK XKI r) idn) = true := by quickRfl

theorem hp_comm : (List.finRange 6).all (fun i => Nat.beq (EV3 XK XKI (hsCommWord i)) (XK i)) =
    true := by quickRfl

theorem hp_surj : (Nat.beq (EV3 XK XKI hsSurjA) (A3 0) && Nat.beq (EV3 XK XKI hsSurjB) (A3 1)) =
    true := by quickRfl

theorem hl_x : (((List.range 3).all fun j => invK (UXL (j + 1))) &&
    Nat.beq (UXK [1, 2, 1, 2, 3, 1, 2, 1, 2, 3]) idn &&
    (List.range 2).all (fun j => bAnd(Nat.beq (CJ.F j) (wfoldR ls8 (cjW.getD j [])), invK (CJ.F j))) &&
    conjK (CJ.F 0) (HC.F 5) (UXK [3, 3, 3, 3]) && conjK (CJ.F 1) (HC.F 12) (UXK [1, 2, 1, 2, 3])) =
      true := by quickRfl

end CFSG.KD.TwoHS

end
