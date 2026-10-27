module

public import Certificates.Kernel.KDenseP.AgreeB
public import Certificates.Kernel.KDenseP.ReplayN
public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.MonoAll
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.C136220
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.C136221
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.C136222
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.C136223
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.C136224
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.C13638
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.C13639
import Certificates.Kernel.KDenseP.MonoTabL
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.MonoEChk0
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.MonoEChk1
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.MonoEChk2

public section

namespace CertificateChecks.KernelKDenseP.MonThreeB

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB CertificateChecks.KernelKDenseP.Axis
  CertificateChecks.KernelKDenseP.TwoPoint CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.M3BM.MT = true := by
  kd_monoTabL CFSG.KD.M3BME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.M3BM.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

open Lean in
macro "kd_m3b% " pre:ident eqs:term:max nes:term:max : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  `(tp3B_sound CertificateChecks.KernelKDenseP.MonThreeB.data_ok $eqs $nes (by quickRfl)
      (S := rlS $(n "rn") $(n "CH") $(n "PRf") CFSG.KD.KDF.I 3) (fun x hx => rlS_lt hx)
      (CH := $(n "CH")) (nch := kd_count% $pre $(mkIdent `CH)) (IT := $(n "IT"))
      (replay_sound (run := $(n "rn")) (chk := CFSG.KD.M3B.chkP (tri $eqs $nes))
        (fun S S' c h3 h4 => CFSG.KC.KDenseP.chunkOKN_loc S S' c h3 h4)
        (fun S c h => CFSG.KC.KDenseP.chunkOKN_prod S c h)
        (CH := $(n "CH")) (PR := $(n "PRf")) (GK := $(n "GKf")) (G := $(n "Gf"))
        (S0 := CFSG.KD.KDF.I) (w := 3) (ng := kd_count% $pre $(mkIdent `u))
        (by kd_allE $pre $(mkIdent `u)) (by quickRfl))
      (by quickRfl) (by quickRfl))

theorem c136220 : agreeAll ((m3bEqs.drop 0).take 8) = true :=
  (kd_m3b% CFSG.KD.M3B.c136220 e136220 []).1
theorem c136221 : agreeAll ((m3bEqs.drop 8).take 18) = true :=
  (kd_m3b% CFSG.KD.M3B.c136221 e136221 []).1
theorem c136222 : agreeAll ((m3bEqs.drop 26).take 17) = true :=
  (kd_m3b% CFSG.KD.M3B.c136222 e136222 []).1
theorem c136223 : agreeAll (m3bEqs.drop 43) = true :=
  (kd_m3b% CFSG.KD.M3B.c136223 e136223 []).1

theorem moveCheck_of_sep {w : List Native.Gen}
    (h : (∀ g ∈ w, g.validB = true) ∧ (∀ g ∈ ([] : List Native.Gen), g.validB = true) ∧
      EdgeNoncomm.moveCheckAux (Native.evalWord w (aV ())) (Native.evalWord [] (aV ())) = true) :
    EdgeNoncomm.moveCheck w (aV ()) = true := by
  unfold EdgeNoncomm.moveCheck
  rw [Bool.and_eq_true]
  exact ⟨List.all_eq_true.2 h.1, h.2.2⟩

theorem c136224 : m3bMoves.all (fun w => EdgeNoncomm.moveCheck w (aV ())) = true := by
  have h := (kd_m3b% CFSG.KD.M3B.c136224 [] n136224).2
  refine List.all_eq_true.2 fun w hw => moveCheck_of_sep (h (w, []) ?_)
  exact List.mem_map.2 ⟨w, hw, rfl⟩

theorem c13638 : agreeAll m7APairs = true ∧ EdgeNoncomm.moveCheck m7rbW (aV ()) = true ∧
    EdgeNoncomm.moveCheck m7rtbW (aV ()) = true := by
  obtain ⟨he, hn⟩ := kd_m3b% CFSG.KD.M3B.c13638 m7APairs n13638
  exact ⟨he, moveCheck_of_sep (hn (m7rbW, []) (by simp [n13638])),
    moveCheck_of_sep (hn (m7rtbW, []) (by simp [n13638]))⟩

theorem c13639 : agreeAll m7BPairs = true ∧ m7SepCheck = true := by
  obtain ⟨he, hn⟩ := kd_m3b% CFSG.KD.M3B.c13639 m7BPairs n13639
  obtain ⟨v1, v2, hm⟩ := hn _ (List.mem_singleton.2 rfl)
  refine ⟨he, ?_⟩
  unfold m7SepCheck sepCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨List.all_eq_true.2 v1, List.all_eq_true.2 v2⟩, hm⟩

end CertificateChecks.KernelKDenseP.MonThreeB

end
